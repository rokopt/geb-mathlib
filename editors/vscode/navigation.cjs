// Navigation uses the host's document reader and module resolution, with editor snapshots.
const vscode = require('vscode');
const { execFile } = require('node:child_process');
const { realpath } = require('node:fs/promises');
const path = require('node:path');

function position(document, line, byteColumn) {
  const row = Math.min(Math.max(line - 1, 0), document.lineCount - 1);
  const text = document.lineAt(row).text;
  const prefix = Buffer.from(text, 'utf8').subarray(0, Math.max(byteColumn - 1, 0));
  return new vscode.Position(row, prefix.toString('utf8').length);
}

function range(document, span) {
  const start = position(document, span[0], span[1]);
  // Host spans include the final byte, whereas editor ranges exclude their end.
  const end = position(document, span[2], span[3] + 1);
  return new vscode.Range(start, end);
}

exports.register = (context, selected) => {
  const output = vscode.window.createOutputChannel('Geb navigation');
  context.subscriptions.push(output);
  async function request(document, at, token) {
    if (!vscode.workspace.isTrusted || token.isCancellationRequested) return;
    const program = selected();
    if (!program) return;
    const open = vscode.workspace.textDocuments.filter(d => d.uri.scheme === 'file');
    const versions = open.map(d => [d, d.version]);
    try {
      const documents = (await Promise.all(open.map(async d => {
        try { return { path: await realpath(d.uri.fsPath), text: d.getText() }; }
        catch (error) {
          // An unrelated buffer can remain open after its file has been removed.
          if (error.code === 'ENOENT') return undefined;
          throw error;
        }
      }))).filter(Boolean);
      const file = document ? await realpath(document.uri.fsPath) : '';
      const payload = JSON.stringify({ file, line: at ? at.line + 1 : 0,
        column: at ? Buffer.byteLength(document.lineAt(at.line).text.slice(0, at.character), 'utf8') + 1 : 0,
        documents });
      if (token.isCancellationRequested) return;
      const result = await new Promise((resolve, reject) => {
        const child = execFile(path.join(program.cwd, '.lake/build/bin/geb-author'),
          ['navigation', program.manifest], { cwd: program.cwd, timeout: 15000,
            maxBuffer: 16 * 1024 * 1024, encoding: 'utf8' }, (error, stdout, stderr) => {
            cancellation.dispose();
            if (error) reject(new Error(stderr.trim() || error.message));
            else { try { resolve(JSON.parse(stdout)); } catch (e) { reject(e); } }
          });
        const cancellation = token.onCancellationRequested(() => child.kill());
        child.stdin.on('error', () => {}); // A rejected request may close its input early.
        child.stdin.end(payload);
      });
      if (token.isCancellationRequested || selected()?.key !== program.key ||
          versions.some(([d, version]) => d.isClosed || d.version !== version)) return;
      const decode = symbol => symbol && ({ ...symbol,
        name: Buffer.from(symbol.name).toString('utf8'),
        signature: Buffer.from(symbol.signature).toString('utf8'),
        documentation: Buffer.from(symbol.documentation).toString('utf8') });
      return { ...result, symbols: result.symbols.map(decode), target: decode(result.target), file };
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
          new vscode.DocumentSymbol(s.name, s.kind,
            s.kind === 'module' ? vscode.SymbolKind.Module : vscode.SymbolKind.Function,
            range(document, s.span), range(document, s.selection)));
      },
    }),
    vscode.languages.registerWorkspaceSymbolProvider({
      async provideWorkspaceSymbols(query, token) {
        const result = await request(undefined, undefined, token);
        if (!result) return [];
        return Promise.all(result.symbols.filter(s => s.name.toLowerCase().includes(query.toLowerCase()))
          .map(async s => {
            const doc = await vscode.workspace.openTextDocument(vscode.Uri.file(s.file));
            return new vscode.SymbolInformation(s.name, vscode.SymbolKind.Function, '',
              new vscode.Location(doc.uri, range(doc, s.selection)));
          }));
      },
    }),
  );
};
