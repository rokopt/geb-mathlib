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
  async function request(operation, document, at, token, extra = {}) {
    if (!vscode.workspace.isTrusted || token.isCancellationRequested) return;
    const program = selected();
    if (!program) return;
    try {
      const snapshot = await host.capture();
      const file = document ? await realpath(document.uri.fsPath) : '';
      const payload = { operation, file, line: at ? at.line + 1 : 0,
        column: at ? Buffer.byteLength(document.lineAt(at.line).text.slice(0, at.character), 'utf8') + 1 : 0,
        proofs: program.proofs || '', recover: true, ...extra,
        documents: [...(extra.documents || []), ...snapshot.documents] };
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
        completions: result.completions.map(decode), file, current };
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
    vscode.languages.registerReferenceProvider(selector, {
      async provideReferences(document, at, options, token) {
        const result = await request('references', document, at, token);
        if (!result?.references) return [];
        const refs = result.references.filter(ref => options.includeDeclaration || !ref.declaration);
        const locations = await Promise.all(refs.map(async ref => {
          const dest = await vscode.workspace.openTextDocument(vscode.Uri.file(ref.file));
          return new vscode.Location(dest.uri, range(dest, ref.span));
        }));
        return result.current() ? locations : [];
      },
    }),
    vscode.languages.registerRenameProvider(selector, {
      async prepareRename(document, at, token) {
        const result = await request('prepareRename', document, at, token);
        if (!result?.baseName || !result.atomSpan) return;
        return { range: range(document, result.atomSpan), placeholder: host.decode(result.baseName) };
      },
      async provideRenameEdits(document, at, newName, token) {
        if (!newName || /^[?%]|^\d+$/u.test(newName)) throw new Error('Enter a Geb declaration name');
        const result = await request('rename', document, at, token, { newName });
        if (!result?.references?.length) return;
        if (result.errors.length || result.incomplete.length) {
          throw new Error('Resolve incomplete or ambiguous Geb sources before renaming');
        }
        // Resolve the proposed buffers too. A capture can lose a reference, or acquire one
        // that already used the new spelling. Compare both sets at their post-edit positions.
        const edit = new vscode.WorkspaceEdit(), files = new Map(), expected = new Set();
        let declaration;
        const key = (file, line, column) => JSON.stringify([file, line, column]);
        for (const ref of result.references) {
          if (!files.has(ref.file)) files.set(ref.file, []);
          files.get(ref.file).push(ref);
        }
        const documents = [];
        for (const [file, refs] of files) {
          const dest = await vscode.workspace.openTextDocument(vscode.Uri.file(file));
          const original = dest.getText();
          let end = 0, revised = '';
          for (const ref of refs) {
            const r = range(dest, ref.span), replacement = host.decode(ref.replacement);
            revised += original.slice(end, dest.offsetAt(r.start));
            const lines = revised.split('\n');
            const line = lines.length, column = Buffer.byteLength(lines.at(-1), 'utf8') + 1;
            expected.add(key(file, line, column));
            if (ref.declaration) declaration = { file, line, column };
            revised += replacement;
            end = dest.offsetAt(r.end);
            edit.replace(dest.uri, r, replacement);
          }
          documents.push({ path: file, text: revised + original.slice(end) });
        }
        if (!declaration || !result.current()) return;
        const checked = await request('references', document, at, token, { documents, ...declaration });
        if (!checked || !result.current()) return;
        if (checked.errors.length || checked.incomplete.length ||
            checked.references.length !== expected.size ||
            !checked.references.every(r => expected.has(key(r.file, r.span[0], r.span[1])))) {
          throw new Error('This rename would change which declaration a name refers to');
        }
        return edit;
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
