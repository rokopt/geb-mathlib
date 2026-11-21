// One ordered stream per selected manifest. A cancelled request still consumes its reply.
const { spawn } = require('node:child_process');
const { createInterface } = require('node:readline');

exports.connect = (binary, manifest, cwd, oneShot) => {
  const child = spawn(binary, ['navigation-server', manifest], { cwd, stdio: 'pipe' });
  const lines = createInterface({ input: child.stdout });
  let pending, closed, legacy = false, stderr = '', queue = Promise.resolve();
  function stop(error = new Error('Geb navigation stopped')) {
    if (closed) return;
    closed = error;
    pending?.reject(error);
    lines.close();
    child.kill();
  }
  child.on('error', stop);
  child.stdin.on('error', error => { if (error.code !== 'EPIPE') stop(error); });
  child.stderr.setEncoding('utf8').on('data', s => { stderr = (stderr + s).slice(-4096); });
  child.on('close', code => {
    // A project may pin a checkout that advertises only the original navigation command.
    legacy = !closed && code === 2 && Boolean(oneShot) && stderr.includes('geb-author navigation MANIFEST')
      && !stderr.includes('navigation-server');
    stop(new Error(stderr.trim() || `Geb navigation exited (${code})`));
  });
  lines.on('line', line => {
    try {
      const result = JSON.parse(line);
      if (result.error) pending.reject(new Error(result.error));
      else pending.resolve(result);
    } catch (e) { stop(e); }
  });
  function send(payload, token) {
    const response = queue.then(async () => {
      if (token.isCancellationRequested) return;
      if (closed) throw closed;
      const timer = setTimeout(() => stop(new Error('Geb navigation timed out')), 15000);
      try {
        const result = await new Promise((resolve, reject) => {
          pending = { resolve, reject };
          child.stdin.write(JSON.stringify(payload) + '\n');
        });
        if (!token.isCancellationRequested) return result;
      } finally { clearTimeout(timer); pending = undefined; }
    });
    const reply = response.catch(error => {
      if (!legacy) throw error;
      if (!token.isCancellationRequested) return oneShot(payload, token);
    });
    queue = reply.catch(() => {});
    return reply;
  }
  return { send, dispose() { legacy = false; stop(); }, get closed() { return Boolean(closed) && !legacy; } };
};
