const assert = require('node:assert/strict');
const { execFileSync } = require('node:child_process');
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
    await test('locals navigate to their binders and completion respects imports', async () => {
      const position = at('P.first x').translate(0, 'P.first '.length);
      const locations = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
        document.uri, position);
      assert.equal(locations.length, 1);
      assert.equal(document.getText(locations[0].range), 'x');
      assert.ok(locations[0].range.start.isBefore(position));
      const choices = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider',
        document.uri, at('P.first x').translate(0, 3));
      assert.ok(choices.items.some(i => i.label === 'P.first'));
      assert.ok(choices.items.some(i => i.label === 'x'));
      assert.ok(!choices.items.some(i => i.label === 'first'));
      const quoted = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider',
        document.uri, document.positionAt(document.getText().lastIndexOf('"λ😀"') + 2));
      const unicode = quoted.items.find(i => i.label === 'λ😀');
      assert.equal(unicode.insertText, '"λ😀"');
      assert.equal(unicode.filterText, '"λ😀"');
      assert.equal(document.getText(unicode.range), '"λ😀"');
    });
    await test('accepting completion replaces an entire quoted atom', async () => {
      const pane = await vscode.window.showTextDocument(document);
      const before = document.getText(), start = before.lastIndexOf('"λ😀"');
      try {
        await pane.edit(e => e.replace(new vscode.Range(document.positionAt(start),
          document.positionAt(start + '"λ😀"'.length)), '"λ"'));
        const caret = document.positionAt(start + '"λ'.length);
        pane.selection = new vscode.Selection(caret, caret);
        await vscode.commands.executeCommand('editor.action.triggerSuggest');
        for (let i = 0; i < 100 && document.getText() !== before; i++) {
          await new Promise(resolve => setTimeout(resolve, 100));
          await vscode.commands.executeCommand('acceptSelectedSuggestion');
        }
        assert.equal(document.getText(), before);
      } finally {
        await vscode.commands.executeCommand('hideSuggestWidget');
        await pane.edit(e => e.replace(new vscode.Range(document.positionAt(0),
          document.positionAt(document.getText().length)), before));
      }
    });
    await test('proof navigation resolves imported theorems and local hypotheses', async () => {
      const proof = await vscode.workspace.openTextDocument(
        path.join(process.env.GEB_TEST_AUTHORING_PROOFS, 'More.proofs.geb'));
      const before = proof.getText();
      const pane = await vscode.window.showTextDocument(proof);
      const source = '(proofs 2 (import Pair.proofs.geb)\n' +
        ' (theorem again (forall ((xs (List T)))\n' +
        '  (implies (h (equal xs xs)) (equal xs xs)))\n' +
        '  (by (reduce weak h append-nil))))\n';
      try {
        await pane.edit(e => e.replace(new vscode.Range(proof.positionAt(0),
          proof.positionAt(before.length)), source));
        const atProof = s => proof.positionAt(proof.getText().indexOf(s));
        const h = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
          proof.uri, atProof('h append-nil'));
        assert.equal(proof.getText(h[0].range), 'h');
        const theorem = await vscode.commands.executeCommand('vscode.executeDefinitionProvider',
          proof.uri, atProof('append-nil'));
        assert.equal(path.basename(theorem[0].uri.fsPath), 'Pair.proofs.geb');
        const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider',
          proof.uri, atProof('append-nil'));
        assert.match(hovers.map(h => h.contents.map(c => c.value).join('')).join(''), /forall/);
        const outline = await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider', proof.uri);
        assert.ok(outline.some(s => s.name === 'again'));
        assert.equal(proof.isDirty, true);
      } finally {
        await pane.edit(e => e.replace(new vscode.Range(proof.positionAt(0),
          proof.positionAt(proof.getText().length)), before));
        await vscode.window.showTextDocument(document);
      }
    });
    await test('incomplete source retains current and explicitly previous outline entries', async () => {
      const pane = await vscode.window.showTextDocument(document);
      const source = document.getText();
      try {
        await pane.edit(e => e.insert(at('(module Use'), '(def unfinished "\n'));
        const symbols = await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider', document.uri);
        assert.ok(symbols.some(s => s.name === 'Lists.append' && !s.detail.includes('previous')));
        assert.ok(symbols.some(s => s.name === 'Use.run' && s.detail.includes('previous successful parse')));
      } finally {
        await pane.edit(e => e.replace(new vscode.Range(document.positionAt(0),
          document.positionAt(document.getText().length)), source));
      }
    });
    await test('format document works on unsaved text with one undo', async () => {
      const draft = await vscode.workspace.openTextDocument({ language: 'geb',
        content: '; λ😀 retained\r\n(note (future opaque))\r\n' +
          '(def "λ😀"   (quote (0 "first\r\nsecond")))\r\n' });
      await vscode.window.showTextDocument(draft);
      const before = draft.getText();
      assert.equal(draft.eol, vscode.EndOfLine.CRLF);
      const formatted = text => Buffer.from(JSON.parse(execFileSync(
        path.resolve(__dirname, '../../../.lake/build/bin/geb-author'), ['format-buffer'],
        { input: JSON.stringify({ text }), encoding: 'utf8' })).text).toString('utf8');
      await vscode.commands.executeCommand('editor.action.formatDocument');
      assert.notEqual(draft.getText(), before);
      assert.match(draft.getText(), /λ😀 retained/);
      assert.match(draft.getText(), /future opaque/);
      assert.equal(formatted(draft.getText()), formatted(before));
      await vscode.commands.executeCommand('undo');
      assert.equal(draft.getText(), before);
      await vscode.window.showTextDocument(document);
    });
    await test('kernel obligations locate repeated holes and update after unsaved filling', async () => {
      await vscode.commands.executeCommand('geb.selectProgram', 'Kernel fixture');
      const holes = await vscode.workspace.openTextDocument(path.join(root, 'open.geb'));
      const pane = await vscode.window.showTextDocument(holes);
      const before = holes.getText();
      try {
        await pane.edit(e => e.replace(new vscode.Range(holes.positionAt(0),
          holes.positionAt(before.length)), before.replace('add x ?body', 'add ?body ?body')));
        const report = await vscode.commands.executeCommand('geb.inspectHoles');
        assert.equal(report.complete, false);
        assert.equal(report.holes.length, 1);
        assert.equal(report.holes[0].occurrences.length, 2);
        assert.equal(Buffer.from(report.holes[0].context[0].name).toString(), 'x');
        await vscode.commands.executeCommand('geb.openObligation', report.holes[0].occurrences[1]);
        assert.equal(holes.getText(vscode.window.activeTextEditor.selection), '?body');
        await pane.edit(e => e.replace(new vscode.Range(holes.positionAt(0),
          holes.positionAt(holes.getText().length)), before.replace('?body', 'x')));
        assert.equal((await vscode.commands.executeCommand('geb.inspectHoles')).complete, true);
        assert.equal(readFileSync(holes.fileName, 'utf8'), before);
      } finally {
        await pane.edit(e => e.replace(new vscode.Range(holes.positionAt(0),
          holes.positionAt(holes.getText().length)), before));
        await vscode.commands.executeCommand('geb.selectProgram', 'Editor fixture');
        await vscode.window.showTextDocument(document);
      }
    });
  } finally {
    const current = await vscode.window.showTextDocument(document);
    await current.edit(edit => edit.replace(new vscode.Range(document.positionAt(0),
      document.positionAt(document.getText().length)), original));
    await document.save();
  }
};
