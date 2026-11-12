// Navigation uses the host's document reader and module resolution, with editor snapshots.
const vscode = require('vscode');
const { realpath } = require('node:fs/promises');
const host = require('./host.cjs');
const { range } = host;

exports.register = (context, selected) => {
  const output = vscode.window.createOutputChannel('Geb navigation');
  context.subscriptions.push(output);
  const previous = new Map();
  async function request(document, at, token) {
    if (!vscode.workspace.isTrusted || token.isCancellationRequested) return;
    const program = selected();
    if (!program) return;
    try {
      const snapshot = await host.capture();
      const file = document ? await realpath(document.uri.fsPath) : '';
      const payload = { file, line: at ? at.line + 1 : 0,
        column: at ? Buffer.byteLength(document.lineAt(at.line).text.slice(0, at.character), 'utf8') + 1 : 0,
        documents: snapshot.documents, proofs: program.proofs || '', recover: true };
      if (token.isCancellationRequested) return;
      const result = await host.call(program.cwd, ['navigation', program.manifest], payload, token);
      if (!result || token.isCancellationRequested || selected()?.key !== program.key ||
          !snapshot.current()) return;
      const decode = symbol => symbol && ({ ...symbol,
        name: host.decode(symbol.name),
        signature: host.decode(symbol.signature),
        documentation: host.decode(symbol.documentation),
        insertText: host.decode(symbol.insertText) });
      const symbols = result.symbols.map(decode);
      const incomplete = new Set(result.incomplete);
      for (const f of new Set([...symbols.map(s => s.file), ...(document ? [file] : [])])) {
        const key = `${program.key}:${f}`;
        if (!incomplete.has(f)) previous.set(key, symbols.filter(s => s.file === f));
      }
      // Previous symbols are offered only in outlines, with an explicit label. Their old
      // locations never answer definition, hover or completion queries.
      for (const f of incomplete) {
        for (const s of previous.get(`${program.key}:${f}`) || []) {
          if (!symbols.some(n => n.file === f && n.name === s.name)) symbols.push({ ...s, stale: true });
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
        let result = await request(document, at, token);
        // Keyboard navigation also works with the caret immediately after the atom.
        if (result && !result.target && at.character > 0) {
          result = await request(document, at.translate(0, -1), token);
        }
        if (!result?.target) return;
        const target = result.target;
        const dest = await vscode.workspace.openTextDocument(vscode.Uri.file(target.file));
        return new vscode.Location(dest.uri, range(dest, target.selection));
      },
    }),
    vscode.languages.registerHoverProvider(selector, {
      async provideHover(document, at, token) {
        const result = await request(document, at, token);
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
        const result = await request(document, undefined, token);
        if (!result) return [];
        return result.symbols.filter(s => s.file === result.file).map(s =>
          new vscode.DocumentSymbol(s.name, s.stale ? 'previous successful parse' : s.kind,
            s.kind === 'module' ? vscode.SymbolKind.Module : vscode.SymbolKind.Function,
            range(document, s.span), range(document, s.selection)));
      },
    }),
    vscode.languages.registerCompletionItemProvider(selector, {
      async provideCompletionItems(document, at, token) {
        const result = await request(document, at, token);
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
        const result = await request(undefined, undefined, token);
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
