const assert = require('node:assert/strict');
const { readFileSync } = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');

exports.run = async test => {
  const root = process.env.GEB_TEST_AUTHORING_PROJECT;
  if (!root) return;
  await vscode.commands.executeCommand('geb.selectProgram', 'Editor fixture');
  const file = path.join(root, 'Lists.geb');
  const original = readFileSync(file, 'utf8');
  const document = await vscode.workspace.openTextDocument(file);
  const editor = await vscode.window.showTextDocument(document);
  const changed = original + '\n(module Use (import Pair as P) (export run)\n' +
    '  (defn run ((x T)) T (P.first x x)))\n' +
    '(def "λ😀" (lam ((x T)) (Pair.first x x)))\n(def last "λ😀")\n';
  try {
    await editor.edit(edit => edit.replace(new vscode.Range(document.positionAt(0),
      document.positionAt(document.getText().length)), changed));
    const at = text => document.positionAt(document.getText().indexOf(text));
    await test('navigation resolves imports from unsaved source and leaves buffers unsaved', async () => {
      const locations = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
        document.uri, at('P.first x'));
      assert.equal(locations.length, 1);
      assert.equal(path.basename(locations[0].uri.fsPath), 'Pair.geb');
      const target = await vscode.workspace.openTextDocument(locations[0].uri);
      assert.equal(target.getText(locations[0].range), 'first');
      const after = at('P.first x').translate(0, 'P.first'.length);
      const fromEnd = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
        document.uri, after);
      assert.equal(fromEnd.length, 1);
      assert.equal(target.getText(fromEnd[0].range), 'first');
      assert.equal(document.isDirty, true);
      assert.equal(readFileSync(file, 'utf8'), original);
    });
    await test('hover shows the declaration and its note-associated documentation', async () => {
      const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider',
        document.uri, at('Pair.first x'));
      assert.ok(hovers.length);
      const content = hovers.flatMap(h => h.contents).map(c => c.value).join('\n');
      assert.match(content, /defn first/);
      assert.match(content.replaceAll('&nbsp;', ' '), /first component of the pair/);
    });
    await test('definition ranges translate UTF-8 bytes to UTF-16 positions', async () => {
      const offset = document.getText().lastIndexOf('"λ😀"');
      const locations = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
        document.uri, document.positionAt(offset + 1));
      assert.equal(locations.length, 1);
      assert.equal(document.getText(locations[0].range), '"λ😀"');
    });
    await test('outline and workspace symbols expose source declarations', async () => {
      const symbols = await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider',
        document.uri);
      assert.ok(symbols.some(s => s.name === 'Lists.append'));
      assert.ok(symbols.some(s => s.name === 'Use.run'));
      const notes = await vscode.workspace.openTextDocument({ language: 'markdown', content: 'Notes' });
      await vscode.window.showTextDocument(notes);
      const workspace = await vscode.commands.executeCommand('vscode.executeWorkspaceSymbolProvider',
        'Lists.append');
      assert.ok(workspace.some(s => s.name === 'Lists.append'));
      await vscode.window.showTextDocument(document);
    });
  } finally {
    const current = await vscode.window.showTextDocument(document);
    await current.edit(edit => edit.replace(new vscode.Range(document.positionAt(0),
      document.positionAt(document.getText().length)), original));
    await document.save();
  }
};
