const assert = require('node:assert/strict');
const vscode = require('vscode');
const { execFileSync } = require('node:child_process');
const { readFileSync, writeFileSync, mkdtempSync, rmSync } = require('node:fs');
const path = require('node:path');
const { editorTest } = require('../package.json');

const root = path.resolve(__dirname, '../../..');
const bin = name => path.join(root, '.lake/build/bin', name);
let scratch;
let serial = 0;

async function open(text) {
  const file = path.join(scratch, `fixture ${serial++}.geb`);
  writeFileSync(file, text);
  const document = await vscode.workspace.openTextDocument(file);
  assert.equal(document.languageId, 'geb');
  return vscode.window.showTextDocument(document);
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

async function formatTask(editor) {
  const task = (await vscode.tasks.fetchTasks()).find(t => t.name === 'Geb: format saved file');
  assert.ok(task, 'the repository formatter task is available');
  await editor.document.save();
  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      listener.dispose();
      reject(new Error('formatter task timed out'));
    }, 30000);
    const listener = vscode.tasks.onDidEndTaskProcess(event => {
      if (event.execution.task.name !== task.name) return;
      clearTimeout(timer);
      listener.dispose();
      if (event.exitCode === 0) resolve();
      else reject(new Error(`formatter task exited ${event.exitCode}`));
    });
    vscode.tasks.executeTask(task).catch(error => {
      clearTimeout(timer);
      listener.dispose();
      reject(error);
    });
  });
  return readFileSync(editor.document.uri.fsPath, 'utf8');
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
    if (process.env.GEB_TEST_PAREDIT === '1') await pareditTests(test, profile);
    if (failures.length) throw new AggregateError(failures, 'Editor acceptance failed');
  } finally {
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    rmSync(scratch, { recursive: true, force: true });
  }
};

async function pareditTests(test, profile) {
  const paredit = vscode.extensions.getExtension('MikeDelmonaco.paredit');
  assert.ok(paredit);
  assert.equal(paredit.packageJSON.version, editorTest.paredit.split('@')[1]);
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
