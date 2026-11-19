// The acceptance of a client of the shared library, run by scripts/tests/client-acceptance.sh in
// the folder of a fresh clone, with the extensions installed from the packages its submodule built.
const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');
const { command, replace, diagnostics } = require('./authoring.cjs');

exports.run = async (test, checkTask) => {
  const client = process.env.GEB_TEST_CLIENT;
  const geb = path.join(client, 'geb');
  const library = path.join(geb, 'library/Bytes.geb');
  const original = readFileSync(library, 'utf8');

  await test('the extensions are the installed packages of the pinned revision', async () => {
    const extension = vscode.extensions.getExtension('geb-mathlib.geb-language');
    assert.ok(extension);
    assert.ok(!extension.extensionPath.startsWith(geb), 'not run from the submodule\'s sources');
    const pinned = JSON.parse(readFileSync(path.join(geb, 'editors/vscode/package.json'), 'utf8'));
    assert.equal(extension.packageJSON.version, pinned.version);
    const paredit = vscode.extensions.getExtension('MikeDelmonaco.paredit');
    assert.ok(paredit);
    assert.equal(paredit.packageJSON.version, pinned.editorTest.paredit.version);
    await extension.activate();
  });
  await test('go to definition follows an import into the library', async () => {
    const document = await vscode.workspace.openTextDocument(path.join(client, 'Client.geb'));
    await vscode.window.showTextDocument(document);
    const at = document.positionAt(document.getText().indexOf('Bytes.reverse xs') + 'Bytes.'.length);
    const [location, ...rest] = await vscode.commands.executeCommand(
      'vscode.executeDefinitionProvider', document.uri, at);
    assert.equal(rest.length, 0);
    assert.equal(location.uri.fsPath, library);
    const target = await vscode.workspace.openTextDocument(location.uri);
    assert.equal(target.getText(location.range), 'reverse');
    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider',
      document.uri, at);
    assert.match(hovers.flatMap(h => h.contents).map(c => c.value).join('\n')
      .replaceAll('&nbsp;', ' '), /elements of a list of bytes in the opposite order/);
  });
  await test('compile checks the examples of the library and the client', async () => {
    await vscode.commands.executeCommand('geb.selectProgram', 'Client');
    const result = await command('compile');
    assert.equal(result.code, 0);
    assert.equal(result.task.execution.options.cwd, geb);
  });
  await test('an edit of the library module is checked by the client\'s compile', async () => {
    // A false example fails the compile, which reports it without a position.
    await replace(library, original.replace('(quote (0 (9) (8) (7)))', '(quote (0 (7) (8) (9)))'));
    assert.equal((await command('compile')).code, 1);
    const document = await replace(library, original.replace('(Ts.reverse xs)', '(Ts.reverse unit)'));
    assert.equal((await command('compile')).code, 1);
    await diagnostics(document, found => found.length === 1 &&
      found[0].message.startsWith('Bytes.reverse does not check'));
    await replace(library, original);
    assert.equal((await command('compile')).code, 0);
    await diagnostics(document, found => found.length === 0);
  });
  await test('prove and replay the client\'s and the library\'s theorems', async () => {
    assert.equal((await command('prove')).code, 0);
    assert.equal((await command('replay')).code, 0);
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
