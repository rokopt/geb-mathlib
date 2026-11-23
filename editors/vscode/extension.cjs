// Editor commands delegate compilation, proofs and preservation to the Geb host tools.
const vscode = require('vscode');
const path = require('node:path');
const { mkdir } = require('node:fs/promises');
const { execFile } = require('node:child_process');
const { promisify } = require('node:util');

const launcher = path.join(__dirname, 'tools.py');
const proofCache = folder => path.join(folder, '.lake', 'geb-proof-cache');

const actions = {
  compile: 'Compile program',
  run: 'Run program on a file',
  interact: 'Run program with requests',
  prove: 'Prove statements',
  replay: 'Replay certificate',
  holes: 'Show kernel holes',
  record: 'Record development',
  verify: 'Verify record integrity',
  check: 'Check recorded development',
  compare: 'Compare sources with record',
};

function programs() {
  return (vscode.workspace.workspaceFolders || []).flatMap(folder => {
    const config = vscode.workspace.getConfiguration('geb', folder.uri);
    const entries = config.get('programs', []);
    if (!Array.isArray(entries)) throw new Error('geb.programs must be an array');
    const names = new Set();
    return entries.map(p => {
      if (!p || typeof p.name !== 'string' || !p.name.trim() || names.has(p.name)) {
        throw new Error('Each Geb program needs a distinct, nonempty name within its workspace folder');
      }
      names.add(p.name);
      const resolve = (value, field) => {
        if (typeof value !== 'string' || !value.trim()) {
          throw new Error(`${p.name}: configure ${field} in geb.programs`);
        }
        return path.resolve(folder.uri.fsPath, value);
      };
      const output = path.join('.lake', 'geb-editor', `program-${encodeURIComponent(p.name)}`);
      return {
        name: p.name, folder, key: `${folder.uri.toString()}#${p.name}`,
        cwd: resolve(config.get('toolchainDirectory', '.'), 'geb.toolchainDirectory'),
        manifest: resolve(p.manifest, 'manifest'),
        proofs: p.proofs ? resolve(p.proofs, 'proofs') : undefined,
        image: resolve(p.image || path.join(output, 'program.img'), 'image'),
        certificate: resolve(p.certificate || path.join(output, 'proof.cert'), 'certificate'),
        record: p.record ? resolve(p.record, 'record') : undefined,
        records: resolve('records', 'record directory'),
      };
    });
  });
}

// The selected checkout supplies the tools. The client workspace owns its proof cache.
const fileTasks = {
  'format saved file': () => ['run', 'geb-fmt', '${file}'],
  'check saved file': folder => ['run', 'geb-author', 'check',
    '--cache', proofCache(folder), '${file}'],
};

function fileTask(folder, name) {
  const cwd = path.resolve(folder.uri.fsPath,
    vscode.workspace.getConfiguration('geb', folder.uri).get('toolchainDirectory', '.'));
  return new vscode.Task({ type: 'geb', task: name }, folder, name, 'Geb',
    new vscode.ProcessExecution('python3', [launcher, ...fileTasks[name](folder.uri.fsPath)], { cwd }),
    name === 'check saved file' ? ['$geb'] : []);
}

// Arguments of a run with requests: a JSON array of strings, or words separated by white space.
function argumentsOf(text) {
  const value = text.trim();
  if (!value.startsWith('[')) return value ? value.split(/\s+/) : [];
  const parsed = JSON.parse(value);
  if (!Array.isArray(parsed) || !parsed.every(a => typeof a === 'string')) {
    throw new Error('Program arguments in brackets must be a JSON array of strings');
  }
  return parsed;
}

function invocation(action, p, record, given) {
  const proof = () => {
    if (!p.proofs) throw new Error(`${p.name}: configure proofs in geb.programs`);
    return p.proofs;
  };
  switch (action) {
    case 'compile': return ['python3', [launcher, 'run', 'geb-author', 'compile', p.manifest, p.image]];
    case 'run': return ['python3', [launcher, 'run', 'geb-author', 'run', p.manifest,
      given.entry, given.input, given.output]];
    // Relative paths in the program's requests resolve against its workspace folder.
    case 'interact': return ['python3', [launcher, 'run', '--directory', p.folder.uri.fsPath,
      'geb-author', 'interact', p.manifest, given.entry, ...given.arguments]];
    case 'prove': return ['python3', [launcher, 'run', 'geb-author', action, '--cache',
      proofCache(p.folder.uri.fsPath), p.manifest, proof(), p.certificate]];
    case 'replay':
      return ['python3', [launcher, 'run', 'geb-author', action, p.manifest, proof(), p.certificate]];
    case 'holes': return ['python3', [launcher, 'run', 'geb-kernel', 'holes', '--manifest', p.manifest]];
    default: {
      const args = action === 'verify' ? [path.join(p.cwd, 'scripts/preserve.py'), action]
        : [launcher, 'preserve', action];
      if (action === 'record') {
        args.push(p.manifest);
        if (p.proofs) args.push(p.proofs);
        args.push(record);
        if (p.proofs) args.push('--certificate', p.certificate);
      } else {
        args.push(record);
        if (action === 'compare') {
          args.push(p.manifest);
          if (p.proofs) args.push(p.proofs);
        }
      }
      return ['python3', args];
    }
  }
}

exports.activate = context => {
  let busy = false;
  let serial = 0;
  const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
  status.command = 'geb.selectProgram';
  status.tooltip = 'Select the program used by Geb commands';
  const current = entries => entries.find(p => p.key === context.workspaceState.get('geb.program'))
    || (entries.length === 1 ? entries[0] : undefined);
  require('./navigation.cjs').register(context, () => current(programs()));
  const editing = require('./editing.cjs').register(context, () => current(programs()));
  function refresh() {
    try { status.text = `Geb: ${current(programs())?.name || 'Select program'}`; }
    catch { status.text = 'Geb: Configure programs'; }
    status.show();
  }
  async function select(force = false, name) {
    const entries = programs();
    if (!entries.length) throw new Error('Configure geb.programs in workspace settings first');
    let chosen = !force ? current(entries) : undefined;
    if (name !== undefined) {
      const matches = entries.filter(p => p.name === name || p.key === name);
      if (matches.length !== 1) throw new Error(`Geb program is missing or ambiguous: ${name}`);
      chosen = matches[0];
    }
    if (!chosen) {
      const item = await vscode.window.showQuickPick(entries.map(p => ({
        label: p.name, description: p.folder.name, detail: p.manifest, program: p,
      })), { title: 'Select Geb program', placeHolder: 'Used by compile, proofs and preservation' });
      chosen = item?.program;
    }
    if (chosen) {
      await context.workspaceState.update('geb.program', chosen.key);
      editing.invalidate();
      refresh();
    }
    return chosen;
  }
  async function saved(p) {
    // Sources and proof imports live below their entry documents, even outside the workspace.
    const roots = [p.manifest, p.proofs].filter(Boolean).map(file => path.dirname(file));
    const belowEntry = file => roots.some(root => {
      const relative = path.relative(root, file);
      return !path.isAbsolute(relative) && relative !== '..' && !relative.startsWith(`..${path.sep}`);
    });
    for (const doc of vscode.workspace.textDocuments) {
      if (doc.isDirty && doc.uri.scheme === 'file' &&
          (vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.toString() === p.folder.uri.toString()
            || belowEntry(doc.uri.fsPath))) {
        if (!await doc.save()) throw new Error(`Could not save ${doc.uri.fsPath}; command cancelled`);
      }
    }
  }
  async function recordPath(p, create, choose = false) {
    const previous = context.workspaceState.get(`geb.record:${p.key}`) || p.record;
    if (!create && !choose && previous) return previous;
    const uri = create
      ? await vscode.window.showSaveDialog({
        title: 'New immutable development record', saveLabel: 'Record development',
        defaultUri: vscode.Uri.file(path.join(p.records, `program-${encodeURIComponent(p.name)}`)),
      })
      : (await vscode.window.showOpenDialog({
        title: 'Select development record', canSelectFiles: false, canSelectFolders: true,
        canSelectMany: false, defaultUri: vscode.Uri.file(previous || p.records),
      }))?.[0];
    return uri?.fsPath;
  }
  // The entry, files and arguments of a run: those given to the command, or else chosen, the
  // previous choices for the program offered first.
  async function runParameters(action, p, given = {}) {
    const key = `geb.run:${p.key}`;
    const previous = context.workspaceState.get(key) || {};
    let entry = given.entry;
    if (entry === undefined) {
      const { stdout } = await promisify(execFile)('python3',
        [launcher, 'run', 'geb-kernel', 'entries', p.manifest], { cwd: p.cwd });
      const entries = stdout.split('\n').filter(Boolean);
      if (!entries.length) throw new Error(`${p.name}: the manifest names no entry point`);
      entry = entries.length === 1 ? entries[0] : (await vscode.window.showQuickPick(
        [...entries].sort((a, b) => (b === previous.entry) - (a === previous.entry)),
        { title: `${actions[action]}: entry point`, placeHolder: p.name }));
      if (!entry) return;
    }
    const folder = uri => uri || p.folder.uri;
    const result = { entry };
    if (action === 'run') {
      const file = value => value && path.resolve(p.folder.uri.fsPath, value);
      result.input = file(given.input) || (await vscode.window.showOpenDialog({
        title: `${actions[action]}: input`, canSelectMany: false,
        defaultUri: folder(previous.input && vscode.Uri.file(previous.input)),
      }))?.[0]?.fsPath;
      if (!result.input) return;
      result.output = file(given.output) || (await vscode.window.showSaveDialog({
        title: `${actions[action]}: output`, saveLabel: 'Write output',
        defaultUri: folder(previous.output && vscode.Uri.file(previous.output)),
      }))?.fsPath;
      if (!result.output) return;
      if ([p.manifest, result.input].includes(result.output)) {
        throw new Error('The output must differ from the manifest and the input');
      }
    } else {
      const text = given.arguments !== undefined ? undefined : await vscode.window.showInputBox({
        title: `${actions[action]}: arguments`, value: previous.text ?? '',
        prompt: 'Separated by white space, or a JSON array of strings; relative paths are ' +
          'resolved against the workspace folder',
      });
      if (text === undefined && given.arguments === undefined) return;
      result.arguments = given.arguments ?? argumentsOf(text);
      if (text !== undefined) result.text = text;
    }
    await context.workspaceState.update(key, { ...previous, ...result });
    return result;
  }
  async function run(action, destination) {
    if (!vscode.workspace.isTrusted) throw new Error('Geb commands require a trusted workspace');
    if (busy) throw new Error('A Geb command is running; wait for it or terminate its task');
    busy = true;
    let launched = false;
    let listener;
    let endListener;
    try {
      const p = await select();
      if (!p) return;
      const needsRecord = ['record', 'verify', 'check', 'compare'].includes(action);
      const running = ['run', 'interact'].includes(action);
      if (running && destination !== undefined && (typeof destination !== 'object' ||
          destination === null ||
          ['entry', 'input', 'output'].some(f => destination[f] !== undefined &&
            typeof destination[f] !== 'string') ||
          (destination.arguments !== undefined && !(Array.isArray(destination.arguments) &&
            destination.arguments.every(a => typeof a === 'string'))))) {
        throw new Error('Run parameters are an object of an entry, input, output and arguments');
      }
      if (!running && destination !== undefined &&
          (typeof destination !== 'string' || !destination.trim())) {
        throw new Error('A record destination must be a nonempty path');
      }
      const record = action === 'record' && destination !== undefined
        ? path.resolve(p.folder.uri.fsPath, destination)
        : needsRecord ? await recordPath(p, action === 'record') : undefined;
      if (needsRecord && !record) return;
      const given = running ? await runParameters(action, p, destination) : undefined;
      if (running && !given) return;
      const [command, args] = invocation(action, p, record, given);
      if (!['verify', 'check'].includes(action)) await saved(p);
      if (action === 'compile' || action === 'prove') {
        const output = action === 'compile' ? p.image : p.certificate;
        if ([p.manifest, p.proofs, action === 'compile' ? p.certificate : p.image].includes(output)) {
          throw new Error('The output must differ from the manifest, proof document and other output');
        }
        await mkdir(path.dirname(output), { recursive: true });
      }
      const id = `${Date.now()}:${++serial}`;
      const task = new vscode.Task({ type: 'geb', gebExecution: id }, p.folder,
        `${actions[action]} (${p.name})`, 'Geb',
        new vscode.ProcessExecution(command, args, { cwd: p.cwd }),
        ['compile', 'prove', 'replay', 'run', 'interact'].includes(action) ? ['$geb'] : []);
      task.presentationOptions = { reveal: vscode.TaskRevealKind.Always, panel: vscode.TaskPanelKind.Shared };
      listener = vscode.tasks.onDidEndTaskProcess(event => {
        if (event.execution.task.definition.gebExecution !== id) return;
        if (event.exitCode === 0) {
          if (needsRecord) void context.workspaceState.update(`geb.record:${p.key}`, record);
          vscode.window.setStatusBarMessage(`Geb: ${actions[action]} finished`, 5000);
        } else if (action === 'holes' && event.exitCode === 2) {
          vscode.window.setStatusBarMessage('Geb: open holes remain; see the task terminal', 8000);
        } else if (action === 'interact' && event.exitCode !== undefined) {
          vscode.window.setStatusBarMessage(
            `Geb: the program exited with status ${event.exitCode}; see the task terminal`, 8000);
        } else {
          void vscode.window.showErrorMessage(`Geb: ${actions[action]} did not complete ` +
            `(exit ${event.exitCode ?? 'unknown'}); see the task terminal`);
        }
      });
      // Task termination can occur before a process starts, without a process-end event.
      endListener = vscode.tasks.onDidEndTask(event => {
        if (event.execution.task.definition.gebExecution !== id) return;
        listener.dispose();
        endListener.dispose();
        busy = false;
      });
      context.subscriptions.push(listener, endListener);
      const execution = await vscode.tasks.executeTask(task);
      launched = true;
      return execution;
    } finally {
      if (!launched) { listener?.dispose(); endListener?.dispose(); busy = false; }
    }
  }
  const register = (name, action) => context.subscriptions.push(
    vscode.commands.registerCommand(name, async (...args) => {
      try { return await action(...args); }
      catch (error) { void vscode.window.showErrorMessage(`Geb: ${error.message}`); }
    }));
  register('geb.selectProgram', name => select(true, name));
  register('geb.selectRecord', async () => {
    const p = await select();
    if (!p) return;
    const record = await recordPath(p, false, true);
    if (record) await context.workspaceState.update(`geb.record:${p.key}`, record);
  });
  for (const action of Object.keys(actions)) register(`geb.${action}`, destination => run(action, destination));
  context.subscriptions.push(vscode.tasks.registerTaskProvider('geb', {
    provideTasks: () => (vscode.workspace.workspaceFolders || []).flatMap(folder =>
      Object.keys(fileTasks).map(name => fileTask(folder, name))),
    resolveTask: task => Object.hasOwn(fileTasks, task.definition.task) && task.scope?.uri
      ? fileTask(task.scope, task.definition.task) : undefined,
  }));
  context.subscriptions.push(status, vscode.workspace.onDidChangeConfiguration(refresh),
    vscode.workspace.onDidChangeWorkspaceFolders(refresh));
  refresh();
};
