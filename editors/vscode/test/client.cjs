// The acceptance of a client of the shared library, run by scripts/tests/client-acceptance.sh in
// the folder of a fresh clone, with the extensions installed from the pinned checkout or release.
const assert = require('node:assert/strict');
const { readFileSync, unlinkSync, writeFileSync } = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');
const { command, replace, diagnostics } = require('./authoring.cjs');

exports.run = async (test, checkTask) => {
  const client = process.env.GEB_TEST_CLIENT;
  const geb = path.join(client, 'geb');
  const library = path.join(geb, 'library/Lists.geb');
  const original = readFileSync(library, 'utf8');

  await test('the extensions are the installed packages of the pinned revision', async () => {
    const extension = vscode.extensions.getExtension('geb-mathlib.geb-language');
    assert.ok(extension);
    assert.ok(!extension.extensionPath.startsWith(geb), 'not run from the submodule\'s sources');
    assert.equal(extension.packageJSON.version, process.env.GEB_TEST_LANGUAGE_VERSION);
    const paredit = vscode.extensions.getExtension('MikeDelmonaco.paredit');
    assert.ok(paredit);
    assert.equal(paredit.packageJSON.version, process.env.GEB_TEST_PAREDIT_VERSION);
    await extension.activate();
  });
  await test('go to definition follows an import into the library', async () => {
    const document = await vscode.workspace.openTextDocument(path.join(client, 'Client.geb'));
    await vscode.window.showTextDocument(document);
    const at = document.positionAt(document.getText().indexOf('reverse T xs'));
    const [location, ...rest] = await vscode.commands.executeCommand(
      'vscode.executeDefinitionProvider', document.uri, at);
    assert.equal(rest.length, 0);
    assert.equal(location.uri.fsPath, library);
    const target = await vscode.workspace.openTextDocument(location.uri);
    assert.equal(target.getText(location.range), 'reverse');
    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider',
      document.uri, at);
    assert.match(hovers.flatMap(h => h.contents).map(c => c.value).join('\n')
      .replaceAll('&nbsp;', ' '), /elements of a list in the opposite order/);
  });
  await test('warm client navigation sees an unsaved change in the library', async () => {
    const clientDoc = await vscode.workspace.openTextDocument(path.join(client, 'Client.geb'));
    const at = clientDoc.positionAt(clientDoc.getText().indexOf('reverse T xs'));
    const query = async (kind, stage) => {
      const start = performance.now();
      const reply = await vscode.commands.executeCommand(`vscode.execute${kind}Provider`, clientDoc.uri, at);
      console.log(`Client ${kind} (${stage}): ${Math.round(performance.now() - start)} ms`);
      return reply;
    };
    const [initial] = await query('Definition', 'warm');
    const complete = async stage => {
      const result = await query('CompletionItem', stage);
      return result.items.map(item => item.label);
    };
    assert.ok((await complete('warm')).includes('Lists.find'));
    const changed = '\n' + original.replace('The elements of a list in the opposite order',
      'Updated elements of a list in the opposite order').replaceAll('find', 'findFirst');
    try {
      await replace(library, changed);
      const hover = await query('Hover', 'after unsaved import edit');
      assert.match(hover.flatMap(h => h.contents).map(c => c.value).join(' ')
        .replaceAll('&nbsp;', ' '), /Updated elements/);
      const [moved] = await query('Definition', 'after reindexing');
      assert.equal(moved.range.start.line, initial.range.start.line + 1);
      const choices = await complete('after reindexing');
      assert.ok(choices.includes('Lists.findFirst') && !choices.includes('Lists.find'));
      await query('Hover', 'warm');
      assert.equal(readFileSync(library, 'utf8'), original);
    } finally {
      await replace(library, original);
    }
  });
  await test('compile checks the examples of the library and the client', async () => {
    await vscode.commands.executeCommand('geb.selectProgram', 'Client');
    const start = performance.now();
    const result = await command('compile');
    console.log(`Client Compile Program task: ${Math.round(performance.now() - start)} ms`);
    assert.equal(result.code, 0);
    assert.equal(result.task.execution.options.cwd, geb);
    const warm = performance.now();
    assert.equal((await command('compile')).code, 0);
    console.log(`Client repeat Compile Program task: ${Math.round(performance.now() - warm)} ms`);
  });
  await test('an edit of the library module is checked by the client\'s compile', async () => {
    // The Problems range includes the entire false example in the imported source.
    const term = '(node 0 (Lists.reverse T (cons 7 (cons 8 (cons 9 (nil T))))))';
    const failing = `(example ${term}\n      (quote (0 (7) (8) (9))))`;
    const wrong = await replace(library, original.replace(
      `(example ${term} (quote (0 (9) (8) (7))))`, `(future "λ😀") ${failing}`));
    assert.equal((await command('compile')).code, 1);
    const [example] = await diagnostics(wrong, ds => ds.length === 1 &&
      ds[0].message.includes('differs from its expected value'));
    assert.equal(wrong.getText(example.range), failing);
    const document = await replace(library, original.replace('(k (cons x acc))', '(k (cons x unit))'));
    assert.equal((await command('compile')).code, 1);
    await diagnostics(document, found => found.length === 1 &&
      found[0].message.startsWith('Lists.reverse does not check'));
    await replace(library, original);
    assert.equal((await command('compile')).code, 0);
    await diagnostics(document, found => found.length === 0);
  });
  await test('prove and replay the client\'s and the library\'s theorems', async () => {
    assert.equal((await command('prove')).code, 0);
    assert.equal((await command('replay')).code, 0);
  });
  await test('the editor runs the same Copy.step as the client CI check', async () => {
    const file = name => path.join(client, '.lake', name);
    const copy = () => command('interact', {
      entry: 'Copy.step', arguments: ['.lake/copy.index', '.lake/editor.copy'] });
    writeFileSync(file('copy.source'), readFileSync(file('copy.found')));
    assert.equal((await copy()).code, 0);
    assert.deepEqual(readFileSync(file('editor.copy')), readFileSync(file('copy.found')));
    unlinkSync(file('copy.source'));
    assert.equal((await copy()).code, 0);
    assert.deepEqual(readFileSync(file('editor.copy')), readFileSync(file('copy.missing')));
  });
  for (const file of [library, path.join(client, 'Client.proofs.geb')]) {
    await test(`check saved file ${path.relative(client, file)}`, async () => {
      const editor = await vscode.window.showTextDocument(
        await vscode.workspace.openTextDocument(file));
      const { exitCode, found } = await checkTask(editor);
      assert.equal(exitCode, 0);
      assert.equal(found.length, 0);
    });
  }
};
