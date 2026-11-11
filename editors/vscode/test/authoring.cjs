const assert = require('node:assert/strict');
const { readFileSync, writeFileSync, existsSync } = require('node:fs');
const path = require('node:path');
const vscode = require('vscode');

// Observe the real task exit, including failure and the kernel's open-obligation status.
async function command(action, ...args) {
  let execution;
  const codes = new Map();
  const ended = new Set();
  let resolve;
  const end = new Promise(r => { resolve = r; });
  const id = task => task.definition.gebExecution;
  const processEnd = vscode.tasks.onDidEndTaskProcess(e => codes.set(id(e.execution.task), e.exitCode));
  const taskEnd = vscode.tasks.onDidEndTask(e => {
    ended.add(id(e.execution.task));
    if (execution && id(e.execution.task) === id(execution.task)) resolve();
  });
  let timer;
  try {
    execution = await vscode.commands.executeCommand(`geb.${action}`, ...args);
    assert.ok(execution, `${action}: a process task started`);
    assert.ok(execution.task.execution instanceof vscode.ProcessExecution);
    assert.ok(id(execution.task), 'command task retains its invocation identity');
    if (ended.has(id(execution.task))) resolve();
    await Promise.race([end, new Promise((_, reject) => {
      timer = setTimeout(() => { execution.terminate(); reject(new Error(`${action} timed out`)); }, 180000);
    })]);
    return { code: codes.get(id(execution.task)), task: execution.task };
  } finally {
    clearTimeout(timer);
    processEnd.dispose();
    taskEnd.dispose();
  }
}

async function replace(file, text) {
  const document = await vscode.workspace.openTextDocument(file);
  const editor = await vscode.window.showTextDocument(document);
  assert.ok(await editor.edit(edit => edit.replace(
    new vscode.Range(document.positionAt(0), document.positionAt(document.getText().length)), text)));
  return document;
}

async function diagnostics(document, accept) {
  const deadline = Date.now() + 5000;
  while (Date.now() < deadline) {
    const found = vscode.languages.getDiagnostics(document.uri);
    if (accept(found)) return found;
    await new Promise(resolve => setTimeout(resolve, 100));
  }
  assert.fail(`Unexpected diagnostics for ${document.uri.fsPath}: ` +
    JSON.stringify(vscode.languages.getDiagnostics(document.uri)));
}

exports.run = async test => {
  const project = process.env.GEB_TEST_AUTHORING_PROJECT;
  assert.ok(project);
  const file = name => path.join(project, name);
  const source = file('Pair.geb');
  assert.ok(process.env.GEB_TEST_AUTHORING_PROOFS);
  const proofs = path.join(process.env.GEB_TEST_AUTHORING_PROOFS, 'Pair.proofs.geb');
  const image = file('out/program.img');
  const certificate = file('out/proof.cert');
  const record = file('records/first λ record');
  const original = readFileSync(source, 'utf8');
  const originalProofs = readFileSync(proofs, 'utf8');
  await vscode.commands.executeCommand('geb.selectProgram', 'Editor fixture');

  await test('compile saves source buffers and uses a separate workspace folder', async () => {
    const text = original + '\n; Editor-saved documentation.\n';
    const doc = await replace(source, text);
    assert.ok(doc.isDirty);
    const result = await command('compile');
    assert.equal(result.code, 0);
    assert.equal(doc.isDirty, false);
    assert.equal(readFileSync(source, 'utf8'), text);
    assert.ok(readFileSync(image).length > 0);
    assert.deepEqual(result.task.execution.args,
      ['exe', 'geb-author', 'compile', file('pair.manifest'), image]);
    assert.equal(result.task.execution.options.cwd, path.resolve(__dirname, '../../..'));
  });
  await test('prove and replay use the same selected program and certificate', async () => {
    assert.equal((await command('prove')).code, 0);
    assert.ok(readFileSync(certificate).length > 0);
    assert.equal((await command('replay')).code, 0);
  });
  await test('imported proof is saved and diagnosed; its previous certificate still replays', async () => {
    const before = readFileSync(certificate);
    const doc = await replace(proofs, originalProofs.replaceAll('normalize 64', 'normalize 0'));
    assert.equal((await command('prove')).code, 1);
    assert.equal(doc.isDirty, false);
    await diagnostics(doc, found => found.some(d => d.message.includes('does not prove it')));
    assert.deepEqual(readFileSync(certificate), before);
    assert.equal((await command('replay')).code, 0);
  });
  await test('record reuses a saved proof without searching, then verifies, checks and compares', async () => {
    assert.equal((await command('record', record)).code, 0);
    assert.ok(existsSync(path.join(record, 'record.json')));
    const info = JSON.parse(readFileSync(path.join(record, 'record.json'), 'utf8'));
    assert.equal(info.format, 'geb-development/v2');
    assert.deepEqual(info.imports, ['Pair.proofs.geb']);
    assert.equal(readFileSync(path.join(record, 'proofs/Pair.proofs.geb'), 'utf8'),
      readFileSync(proofs, 'utf8'));
    assert.equal((await command('verify')).code, 0);
    assert.equal((await command('check')).code, 0);
    assert.equal((await command('compare')).code, 0);
    const index = readFileSync(path.join(record, 'record.json'));
    assert.equal((await command('record', record)).code, 1);
    assert.deepEqual(readFileSync(path.join(record, 'record.json')), index);
  });
  await test('documentation changes preserve the checked core and saved proof', async () => {
    await replace(source, original + '\n; Changed after recording.\n');
    assert.equal((await command('compare')).code, 0);
  });
  await test('compile failure leaves the image in place and the next command can run', async () => {
    const before = readFileSync(image);
    const doc = await replace(source, original + '\n(def broken (add unit 0))\n');
    assert.equal((await command('compile')).code, 1);
    const [error] = await diagnostics(doc,
      found => found.length === 1 && found[0].message.includes('broken does not check'));
    assert.deepEqual(error.range.start, doc.positionAt(doc.getText().indexOf('broken')));
    assert.deepEqual(readFileSync(image), before);
    await replace(source, original);
    assert.equal((await command('compile')).code, 0);
    await diagnostics(doc, found => found.length === 0);
  });
  await test('kernel holes report obligations separately from a completed program', async () => {
    await vscode.commands.executeCommand('geb.selectProgram', 'Kernel fixture');
    assert.equal((await command('holes')).code, 2);
    writeFileSync(file('open.geb'), '(def f (lam ((x T)) (add x 1)))\n');
    assert.equal((await command('holes')).code, 0);
    await vscode.commands.executeCommand('geb.selectProgram', 'Editor fixture');
    assert.equal((await command('replay')).code, 0);
  });
  await test('terminating a task releases the next command', async () => {
    const started = vscode.tasks.onDidStartTask(e => {
      if (e.execution.task.definition.type === 'geb') e.execution.terminate();
    });
    try { assert.notEqual((await command('compile')).code, 0); }
    finally { started.dispose(); }
    assert.equal((await command('compile')).code, 0);
  });
};
