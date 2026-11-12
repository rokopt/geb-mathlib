const assert = require('node:assert/strict');
const vscode = require('vscode');
const { execFileSync } = require('node:child_process');
const { readFileSync, writeFileSync, mkdtempSync, rmSync } = require('node:fs');
const path = require('node:path');

const root = path.resolve(__dirname, '../../..');
const bin = name => path.join(root, '.lake/build/bin', name);
let scratch;
let serial = 0;

async function open(text) {
  const file = path.join(scratch, `fixture ${serial++}.geb`);
  writeFileSync(file, text);
  const document = await vscode.workspace.openTextDocument(file);
  assert.equal(document.languageId, 'geb');
  const editor = await vscode.window.showTextDocument(document);
  // Task terminals can retain keyboard focus after their process exits. Built-in
  // editing commands act on the focused widget, while Paredit uses the active editor.
  await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');
  return editor;
}

function select(editor, start, end = start) {
  editor.selection = new vscode.Selection(editor.document.positionAt(start),
    editor.document.positionAt(end));
}

function normalized(text) {
  const file = path.join(scratch, `format ${serial++}.geb`);
  writeFileSync(file, text);
  execFileSync(bin('geb-fmt'), [file]);
  return readFileSync(file, 'utf8');
}

function checked(text) {
  const file = path.join(scratch, `check ${serial++}.geb`);
  const image = `${file}.img`;
  writeFileSync(file, text);
  execFileSync(bin('geb-kernel'), ['build', file, image]);
  return readFileSync(image);
}

// Save the buffer and run a task of the repository on it, to the task's exit status.
async function runTask(name, editor) {
  const task = (await vscode.tasks.fetchTasks()).find(t => t.name === name);
  assert.ok(task, `the repository task ${name} is available`);
  await editor.document.save();
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      listener.dispose();
      reject(new Error(`${name} timed out`));
    }, 30000);
    const listener = vscode.tasks.onDidEndTaskProcess(event => {
      if (event.execution.task.name !== task.name) return;
      clearTimeout(timer);
      listener.dispose();
      resolve(event.exitCode);
    });
    vscode.tasks.executeTask(task).catch(error => {
      clearTimeout(timer);
      listener.dispose();
      reject(error);
    });
  });
}

async function formatTask(editor) {
  const exitCode = await runTask('Geb: format saved file', editor);
  if (exitCode !== 0) throw new Error(`formatter task exited ${exitCode}`);
  return readFileSync(editor.document.uri.fsPath, 'utf8');
}

// The diagnostics the check task's problem matcher publishes for the buffer.
async function checkTask(editor) {
  const exitCode = await runTask('Geb: check saved file', editor);
  for (let i = 0; i < 50; i++) {
    const found = vscode.languages.getDiagnostics(editor.document.uri);
    if (found.length || exitCode === 0) return { exitCode, found };
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  return { exitCode, found: [] };
}

async function edit(command, marked, expected) {
  const at = marked.indexOf('⟦');
  assert.notEqual(at, -1);
  const text = marked.replace('⟦', '');
  const editor = await open(text);
  select(editor, at);
  await vscode.commands.executeCommand(command);
  const actual = editor.document.getText();
  // The formatter's retraction makes equality here equality of parsed documents,
  // including comments. Checking each intended tree also catches ill-typed edits.
  assert.equal(normalized(actual), normalized(expected), command);
  assert.deepEqual(checked(actual), checked(expected), command);
  await vscode.commands.executeCommand('undo');
  assert.equal(editor.document.getText(), text, `${command}: undo`);
  console.log(`PASS ${command} and undo`);
}

exports.run = async () => {
  scratch = mkdtempSync(path.join(__dirname, '../node_modules/.cache/editor/fixtures-'));
  const failures = [];
  async function test(name, action) {
    try {
      await action();
      console.log(`PASS ${name}`);
    } catch (error) {
      console.error(`FAIL ${name}: ${error.stack}`);
      failures.push(error);
      await vscode.commands.executeCommand('workbench.action.files.revert');
    }
  }
  try {
    if (process.env.GEB_TEST_NAVIGATION_ONLY) {
      await require('./navigation.cjs').run(test);
      if (failures.length) throw new AggregateError(failures, 'Navigation acceptance failed');
      return;
    }
    const profile = readFileSync(path.join(__dirname, 'fixtures/profile.geb'), 'utf8');
    for (const [eol, text] of [['LF', profile], ['CRLF', profile.replaceAll('\n', '\r\n')]]) {
      await test(`formatter task preserves the document and checked program (${eol})`, async () => {
        const editor = await open(text);
        const formatted = await formatTask(editor);
        assert.equal(formatted, normalized(text));
        assert.equal(normalized(formatted), formatted);
        assert.deepEqual(checked(formatted), checked(text));
        assert.equal(vscode.workspace.getConfiguration('editor', editor.document)
          .get('formatOnSave'), false);
      });
      await test(`bracket matching ignores comments and quoted atoms (${eol})`, async () => {
        const editor = await open(text);
        select(editor, text.indexOf('(module'));
        await vscode.commands.executeCommand('editor.action.jumpToBracket');
        const lastClose = text.lastIndexOf(')', text.indexOf('(def main'));
        assert.equal(editor.document.offsetAt(editor.selection.active), lastClose);
      });
    }
    await test('formatting rejects incomplete input without changing it', async () => {
      const text = '(def unfinished';
      const editor = await open(text);
      await assert.rejects(formatTask(editor), /formatter task exited 1/);
      assert.equal(readFileSync(editor.document.uri.fsPath, 'utf8'), text);
    });
    await test('check task reports a failure at its declaration', async () => {
      const editor = await open('(def f (lam ((x T)) x))\n(def g (lam ((x T)) (nope x)))\n');
      const { exitCode, found } = await checkTask(editor);
      assert.equal(exitCode, 1);
      assert.equal(found.length, 1);
      assert.equal(found[0].message, 'g does not check');
      assert.equal(found[0].severity, vscode.DiagnosticSeverity.Error);
      assert.deepEqual([found[0].range.start.line, found[0].range.start.character], [1, 5]);
    });
    await test('check task reports nothing for an accepted program', async () => {
      const editor = await open('(def f (lam ((x T)) x))\n');
      const { exitCode, found } = await checkTask(editor);
      assert.equal(exitCode, 0);
      assert.equal(found.length, 0);
    });
    // A proof document is proved against the program it names, the manifest beside it.
    writeFileSync(path.join(scratch, 'fixture.manifest'),
      '(program fixture (edition 0) (document (syntax authoring 0) (schema 0) (prose verso 0))\n' +
      '  (sources Program.geb)\n  (entries))\n');
    writeFileSync(path.join(scratch, 'Program.geb'),
      '(module F (export id other)\n  (defn id ((x T)) T x)\n' +
      '  (defn other ((x T)) T (fst (pair x x))))\n');
    const proofs = fuel => '(proofs 2 (program fixture)\n' +
      `  (theorem same (equal F.id F.other) (by (normalize ${fuel}))))\n`;
    await test('check task reports a theorem its script does not prove', async () => {
      const editor = await open(proofs(0));
      const { exitCode, found } = await checkTask(editor);
      assert.equal(exitCode, 1);
      assert.equal(found.length, 1);
      assert.equal(found[0].message, 'the script of the theorem same does not prove it');
      assert.deepEqual([found[0].range.start.line, found[0].range.start.character], [1, 11]);
    });
    await test('check task reports nothing for a proved document', async () => {
      const editor = await open(proofs(64));
      const { exitCode, found } = await checkTask(editor);
      assert.equal(exitCode, 0);
      assert.equal(found.length, 0);
    });
    for (const text of ['', '; comment ', '(def name "atom ']) {
      await test(`parenthesis completion at ${JSON.stringify(text)}`, async () => {
        const editor = await open(text);
        select(editor, text.length);
        await vscode.commands.executeCommand('type', { text: '(' });
        assert.equal(editor.document.getText(), text + (text === '' ? '()' : '('));
        await vscode.commands.executeCommand('undo');
        assert.equal(editor.document.getText(), text);
      });
    }
    if (process.env.GEB_TEST_PAREDIT_VERSION) await pareditTests(test, profile);
    else {
      await require('./navigation.cjs').run(test);
      await require('./authoring.cjs').run(test);
    }
    if (failures.length) throw new AggregateError(failures, 'Editor acceptance failed');
  } finally {
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    rmSync(scratch, { recursive: true, force: true });
  }
};

async function pareditTests(test, profile) {
  const paredit = vscode.extensions.getExtension('MikeDelmonaco.paredit');
  assert.ok(paredit);
  assert.equal(paredit.packageJSON.version, process.env.GEB_TEST_PAREDIT_VERSION);
  await paredit.activate();
  for (const atom of ['"plain"', '"(;)"', '"escaped \\\"quote\\\""', '"λ"', '"first\nsecond"']) {
    await test(`navigate quoted atom ${JSON.stringify(atom)}`, async () => {
      const text = `(quote (0 ${atom}))`;
      const editor = await open(text);
      select(editor, 0);
      await vscode.commands.executeCommand('paredit.forwardSexp');
      assert.equal(editor.document.offsetAt(editor.selection.active), text.length);
    });
  }
  await test('navigate CRLF', async () => {
    const text = '; comment\r\n(def f (lam ((x T)) x))';
    const editor = await open(text);
    select(editor, text.indexOf('(def'));
    await vscode.commands.executeCommand('paredit.forwardSexp');
    assert.equal(editor.document.offsetAt(editor.selection.active), text.length);
  });
  for (const [eol, text] of [['LF', profile], ['CRLF', profile.replaceAll('\n', '\r\n')]]) {
    await test(`profile navigation and selection (${eol})`, async () => {
      const editor = await open(text);
      const start = text.indexOf('(module');
      const end = text.lastIndexOf(')', text.indexOf('(def main')) + 1;
      select(editor, start);
      await vscode.commands.executeCommand('paredit.forwardSexp');
      assert.equal(editor.document.offsetAt(editor.selection.active), end);
      await vscode.commands.executeCommand('paredit.backwardSexp');
      assert.equal(editor.document.offsetAt(editor.selection.active), start);
      await vscode.commands.executeCommand('paredit.selectForwardSexp');
      assert.equal(editor.document.getText(editor.selection), text.slice(start, end));
    });
  }
  const prefix = '; unmatched ( ] "\n(def editorText (quote (0 "(;)" "🌳" "first\nsecond")))\n';
  for (const [name, eol] of [['LF', '\n'], ['CRLF', '\r\n']]) {
    const source = text => (prefix + text).replaceAll('\n', eol);
    await test(`wrap (${name})`, () => edit('paredit.wrapWithParen',
      source('(def main ⟦(lam ((x T)) ; comment with "(\n x))\n'),
      source('(def main ((lam ((x T)) ; comment with "(\n x)))\n')));
    await test(`slurp (${name})`, () => edit('paredit.slurpForward',
      source('(def main (lam ((x T)) ((⟦add 1) 2)))\n'),
      source('(def main (lam ((x T)) ((add 1 2))))\n')));
    await test(`barf (${name})`, () => edit('paredit.barfForward',
      source('(def main (lam ((x T)) ((⟦add 1 2))))\n'),
      source('(def main (lam ((x T)) ((add 1) 2)))\n')));
    await test(`slurp across a comment (${name})`, () => edit('paredit.slurpForward',
      source('(def main (lam ((x T)) ((⟦add 1) ; comment with "(\n 2)))\n'),
      source('(def main (lam ((x T)) ((add 1 ; comment with "(\n 2))))\n')));
    await test(`barf across a comment (${name})`, () => edit('paredit.barfForward',
      source('(def main (lam ((x T)) ((⟦add 1 ; comment with "(\n 2))))\n'),
      source('(def main (lam ((x T)) ((add 1) ; comment with "(\n 2)))\n')));
    await test(`incomplete buffer (${name})`, async () => {
      const text = source('(def main (lam ((x T)) ?body');
      const editor = await open(text);
      select(editor, text.indexOf('?body'));
      await vscode.commands.executeCommand('paredit.selectForwardSexp');
      assert.equal(editor.document.getText(editor.selection), '?body');
      assert.equal(editor.document.getText(), text);
    });
  }
}
