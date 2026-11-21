// Navigation uses the host's document reader and module resolution, with editor snapshots.
const vscode = require('vscode');
const { realpath } = require('node:fs/promises');
const host = require('./host.cjs');
const { connect } = require('./navigation-host.cjs');
const { range } = host;

exports.register = (context, selected) => {
  const output = vscode.window.createOutputChannel('Geb navigation');
  context.subscriptions.push(output);
  const previous = new Map();
  let service, serviceKey;
  context.subscriptions.push({ dispose: () => service?.dispose() });
  const identity = p => p && JSON.stringify([p.key, p.cwd, p.manifest, p.proofs]);
  async function request(operation, document, at, token) {
    if (!vscode.workspace.isTrusted || token.isCancellationRequested) return;
    const program = selected();
    if (!program) return;
    try {
      const snapshot = await host.capture();
      const file = document ? await realpath(document.uri.fsPath) : '';
      const payload = { operation, file, line: at ? at.line + 1 : 0,
        column: at ? Buffer.byteLength(document.lineAt(at.line).text.slice(0, at.character), 'utf8') + 1 : 0,
        documents: snapshot.documents, proofs: program.proofs || '', recover: true };
      if (token.isCancellationRequested) return;
      const { binary, revision } = await host.author(program.cwd);
      const current = () => !token.isCancellationRequested && identity(selected()) === identity(program) &&
        snapshot.current();
      if (!current()) return;
      const key = JSON.stringify([identity(program), revision]);
      if (key !== serviceKey || !service || service.closed) {
        service?.dispose();
        serviceKey = key;
        service = connect(binary, program.manifest, program.cwd,
          (payload, token) => host.call(program.cwd, ['navigation', program.manifest], payload, token));
        previous.clear();
      }
      const result = await service.send(payload, token);
      if (!result || key !== serviceKey || !current()) return;
      const decode = symbol => symbol && ({ ...symbol,
        name: host.decode(symbol.name),
        signature: symbol.signature && host.decode(symbol.signature),
        documentation: symbol.documentation && host.decode(symbol.documentation),
        insertText: symbol.insertText && host.decode(symbol.insertText) });
      const symbols = result.symbols.map(decode);
      const incomplete = new Set(result.incomplete);
      if (operation === 'document' || operation === 'workspace') {
        if (operation === 'workspace') {
          for (const f of previous.keys()) if (!incomplete.has(f)) previous.delete(f);
        }
        for (const f of new Set([...symbols.map(s => s.file), ...(document ? [file] : [])])) {
          if (!incomplete.has(f)) previous.set(f, symbols.filter(s => s.file === f));
        }
        // Previous symbols are offered only in outlines, with an explicit label. Their old
        // locations never answer definition, hover or completion queries.
        for (const f of incomplete) {
          if (document && f !== file) continue;
          for (const s of previous.get(f) || []) {
            if (!symbols.some(n => n.file === f && n.name === s.name)) symbols.push({ ...s, stale: true });
          }
        }
      }
      return { ...result, symbols, target: decode(result.target),
        completions: result.completions.map(decode), file };
    } catch (error) {
      if (!token.isCancellationRequested) output.appendLine(error.message);
      return undefined;
    }
  }
  const selector = { language: 'geb', scheme: 'file' };
  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(selector, {
      async provideDefinition(document, at, token) {
        let result = await request('target', document, at, token);
        // Keyboard navigation also works with the caret immediately after the atom.
        if (result && !result.target && at.character > 0) {
          result = await request('target', document, at.translate(0, -1), token);
        }
        if (!result?.target) return;
        const target = result.target;
        const dest = await vscode.workspace.openTextDocument(vscode.Uri.file(target.file));
        return new vscode.Location(dest.uri, range(dest, target.selection));
      },
    }),
    vscode.languages.registerHoverProvider(selector, {
      async provideHover(document, at, token) {
        const result = await request('target', document, at, token);
        if (!result?.target) return;
        const target = result.target;
        const content = new vscode.MarkdownString();
        content.appendCodeblock(target.signature.trim(), 'geb');
        if (target.documentation) content.appendText('\n' + target.documentation);
        // Prose is inert text, including Markdown links and command-like strings.
        return new vscode.Hover(content);
      },
    }),
    vscode.languages.registerDocumentSymbolProvider(selector, {
      async provideDocumentSymbols(document, token) {
        const result = await request('document', document, undefined, token);
        if (!result) return [];
        return result.symbols.filter(s => s.file === result.file).map(s =>
          new vscode.DocumentSymbol(s.name, s.stale ? 'previous successful parse' : s.kind,
            s.kind === 'module' ? vscode.SymbolKind.Module : vscode.SymbolKind.Function,
            range(document, s.span), range(document, s.selection)));
      },
    }),
    vscode.languages.registerCompletionItemProvider(selector, {
      async provideCompletionItems(document, at, token) {
        const result = await request('completion', document, at, token);
        if (!result) return [];
        // VS Code completion replacement ranges must lie on one line.
        if (result.atomSpan && result.atomSpan[0] !== result.atomSpan[2]) return [];
        return result.completions.map(s => {
          const item = new vscode.CompletionItem(s.name,
            s.kind === 'variable' ? vscode.CompletionItemKind.Variable : vscode.CompletionItemKind.Reference);
          item.insertText = s.insertText;
          item.filterText = s.insertText;
          item.detail = s.signature.trim();
          const prose = new vscode.MarkdownString();
          prose.appendText(s.documentation);
          item.documentation = prose;
          if (result.atomSpan) item.range = range(document, result.atomSpan);
          return item;
        });
      },
    }, '.', '"'),
    vscode.languages.registerWorkspaceSymbolProvider({
      async provideWorkspaceSymbols(query, token) {
        const result = await request('workspace', undefined, undefined, token);
        if (!result) return [];
        return Promise.all(result.symbols.filter(s => s.name.toLowerCase().includes(query.toLowerCase()))
          .map(async s => {
            const doc = await vscode.workspace.openTextDocument(vscode.Uri.file(s.file));
            return new vscode.SymbolInformation(s.name, vscode.SymbolKind.Function,
              s.stale ? 'previous successful parse' : '',
              new vscode.Location(doc.uri, range(doc, s.selection)));
          }));
      },
    }),
  );
};
