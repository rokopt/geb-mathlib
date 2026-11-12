// JSON requests use snapshots of open buffers and never save them.
const vscode = require('vscode');
const { execFile } = require('node:child_process');
const { realpath } = require('node:fs/promises');
const path = require('node:path');

exports.capture = async () => {
  const open = vscode.workspace.textDocuments.filter(d => d.uri.scheme === 'file');
  const versions = open.map(d => [d, d.version]);
  const documents = (await Promise.all(open.map(async d => {
    try { return { path: await realpath(d.uri.fsPath), text: d.getText() }; }
    catch (error) { if (error.code === 'ENOENT') return undefined; throw error; }
  }))).filter(Boolean);
  return { documents, current: () => versions.every(([d, v]) => !d.isClosed && d.version === v) &&
    vscode.workspace.textDocuments.every(d => d.uri.scheme !== 'file' || !d.isDirty || open.includes(d)) };
};

exports.call = (cwd, args, payload, token) => new Promise((resolve, reject) => {
  if (!vscode.workspace.isTrusted || token.isCancellationRequested) return resolve(undefined);
  const child = execFile(path.join(cwd, '.lake/build/bin/geb-author'), args,
    { cwd, timeout: 15000, maxBuffer: 16 * 1024 * 1024, encoding: 'utf8' },
    (error, stdout, stderr) => {
      cancellation.dispose();
      if (token.isCancellationRequested) resolve(undefined);
      else if (error) reject(new Error(stderr.trim() || error.message));
      else { try { resolve(JSON.parse(stdout)); } catch (e) { reject(e); } }
    });
  const cancellation = token.onCancellationRequested(() => child.kill());
  child.stdin.on('error', () => {});
  child.stdin.end(JSON.stringify(payload));
});

exports.position = (document, line, byteColumn) => {
  const row = Math.min(Math.max(line - 1, 0), document.lineCount - 1);
  const prefix = Buffer.from(document.lineAt(row).text, 'utf8').subarray(0, Math.max(byteColumn - 1, 0));
  return new vscode.Position(row, prefix.toString('utf8').length);
};

exports.range = (document, span) => new vscode.Range(
  exports.position(document, span[0], span[1]), exports.position(document, span[2], span[3] + 1));

exports.decode = bytes => {
  const buffer = Buffer.from(bytes), text = buffer.toString('utf8');
  if (Buffer.from(text, 'utf8').equals(buffer)) return text;
  // Names may contain arbitrary bytes even though the editor's strings are Unicode.
  return Array.from(buffer, b => b === 10 ? '\n' : b >= 32 && b <= 126
    ? String.fromCharCode(b) : `\\x${b.toString(16).toUpperCase().padStart(2, '0')}`).join('');
};
