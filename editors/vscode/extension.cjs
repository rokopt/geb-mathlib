// Editor commands delegate compilation, proofs and preservation to the Geb host tools.
const vscode = require('vscode');
const path = require('node:path');
const { mkdir } = require('node:fs/promises');

const actions = {
  compile: 'Compile program',
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

function invocation(action, p, record) {
  const proof = () => {
    if (!p.proofs) throw new Error(`${p.name}: configure proofs in geb.programs`);
    return p.proofs;
  };
  switch (action) {
    case 'compile': return ['lake', ['exe', 'geb-author', 'compile', p.manifest, p.image]];
    case 'prove':
    case 'replay':
      return ['lake', ['exe', 'geb-author', action, p.manifest, proof(), p.certificate]];
    case 'holes': return ['lake', ['exe', 'geb-kernel', 'holes', '--manifest', p.manifest]];
    default: {
      const args = [path.join(p.cwd, 'scripts/preserve.py'), action];
      if (action === 'record') args.push(p.manifest, proof(), record, '--certificate', p.certificate);
      else {
        args.push(record);
        if (action === 'compare') args.push(p.manifest, proof());
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
      if (destination !== undefined && (typeof destination !== 'string' || !destination.trim())) {
        throw new Error('A record destination must be a nonempty path');
      }
      const record = action === 'record' && destination !== undefined
        ? path.resolve(p.folder.uri.fsPath, destination)
        : needsRecord ? await recordPath(p, action === 'record') : undefined;
      if (needsRecord && !record) return;
      const [command, args] = invocation(action, p, record);
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
        ['compile', 'prove', 'replay'].includes(action) ? ['$geb'] : []);
      task.presentationOptions = { reveal: vscode.TaskRevealKind.Always, panel: vscode.TaskPanelKind.Shared };
      listener = vscode.tasks.onDidEndTaskProcess(event => {
        if (event.execution.task.definition.gebExecution !== id) return;
        if (event.exitCode === 0) {
          if (needsRecord) void context.workspaceState.update(`geb.record:${p.key}`, record);
          vscode.window.setStatusBarMessage(`Geb: ${actions[action]} finished`, 5000);
        } else if (action === 'holes' && event.exitCode === 2) {
          vscode.window.setStatusBarMessage('Geb: open holes remain; see the task terminal', 8000);
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
  context.subscriptions.push(status, vscode.workspace.onDidChangeConfiguration(refresh),
    vscode.workspace.onDidChangeWorkspaceFolders(refresh));
  refresh();
};
