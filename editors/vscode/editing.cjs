// Buffer formatting and navigable kernel obligations use the existing host services.
const vscode = require('vscode');
const path = require('node:path');
const host = require('./host.cjs');

exports.register = (context, selected) => {
  context.subscriptions.push(vscode.languages.registerDocumentFormattingEditProvider('geb', {
    async provideDocumentFormattingEdits(document, _options, token) {
      if (!vscode.workspace.isTrusted) return [];
      const folder = vscode.workspace.getWorkspaceFolder(document.uri) || vscode.workspace.workspaceFolders?.[0];
      const cwd = selected()?.cwd || (folder && path.resolve(folder.uri.fsPath,
        vscode.workspace.getConfiguration('geb', folder.uri).get('toolchainDirectory', '.')));
      if (!cwd) throw new Error('Select a Geb toolchain directory before formatting');
      const version = document.version;
      const result = await host.call(cwd, ['format-buffer'], {
        text: document.getText(), crlf: document.eol === vscode.EndOfLine.CRLF,
      }, token);
      if (!result || document.version !== version) return [];
      const formatted = host.decode(result.text);
      if (formatted === document.getText()) return [];
      return [vscode.TextEdit.replace(new vscode.Range(document.positionAt(0),
        document.positionAt(document.getText().length)), formatted)];
    },
  }));

  const changed = new vscode.EventEmitter();
  let roots = [], enabled = false, timer, running, selection;
  const provider = {
    onDidChangeTreeData: changed.event,
    getTreeItem: item => item,
    getChildren: item => item ? item.children || [] : roots,
  };
  const view = vscode.window.createTreeView('geb.obligations', { treeDataProvider: provider });
  context.subscriptions.push(view, changed);
  const message = text => { roots = [new vscode.TreeItem(text)]; changed.fire(); };
  async function refresh() {
    clearTimeout(timer);
    running?.cancel(); running?.dispose();
    const cancel = new vscode.CancellationTokenSource();
    running = cancel;
    const program = selected();
    if (!program || !vscode.workspace.isTrusted) { message('Select a Geb program'); return; }
    selection = program.key;
    enabled = true;
    message('Checking kernel obligations…');
    try {
      const snapshot = await host.capture();
      const result = await host.call(program.cwd, ['editor-holes', program.manifest],
        { documents: snapshot.documents }, cancel.token);
      if (!result || cancel.token.isCancellationRequested || selected()?.key !== program.key ||
          !snapshot.current()) return;
      roots = result.holes.map(h => {
        const name = host.decode(h.name), target = host.decode(h.target).trim();
        const item = new vscode.TreeItem(`?${name} : ${target}`, vscode.TreeItemCollapsibleState.Expanded);
        item.children = h.context.map(b =>
          new vscode.TreeItem(`${host.decode(b.name)} : ${host.decode(b.type).trim()}`));
        item.children.push(...h.occurrences.map(site => {
          const child = new vscode.TreeItem(`${path.basename(site.file)}:${site.span[0]}:${site.span[1]}`);
          child.command = { command: 'geb.openObligation', title: 'Open hole', arguments: [site] };
          return child;
        }));
        return item;
      });
      if (result.complete) message('Complete: no kernel holes'); else changed.fire();
      return result;
    } catch (error) {
      if (!cancel.token.isCancellationRequested) message(`Not checked: ${error.message}`);
    }
  }
  function invalidate() {
    if (!enabled) return;
    running?.cancel();
    clearTimeout(timer);
    message('Source changed: obligations need checking');
    timer = setTimeout(refresh, 400);
  }
  message('Refresh to inspect kernel holes');
  context.subscriptions.push(
    vscode.commands.registerCommand('geb.inspectHoles', refresh),
    vscode.commands.registerCommand('geb.openObligation', async site => {
      const document = await vscode.workspace.openTextDocument(vscode.Uri.file(site.file));
      await vscode.window.showTextDocument(document, { selection: host.range(document, site.span) });
    }),
    vscode.workspace.onDidChangeTextDocument(e => {
      if (e.document.languageId === 'geb' || e.document.fileName.endsWith('.manifest')) invalidate();
    }),
    vscode.workspace.onDidCloseTextDocument(invalidate),
    vscode.workspace.onDidChangeConfiguration(invalidate),
    vscode.window.onDidChangeActiveTextEditor(() => { if (selected()?.key !== selection) invalidate(); }),
    { dispose() { clearTimeout(timer); running?.cancel(); running?.dispose(); } },
  );
  // Program selection does not change configuration or necessarily change the active editor.
  return { invalidate };
};
