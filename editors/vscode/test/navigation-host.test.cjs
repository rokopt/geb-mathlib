const assert = require('node:assert/strict');
const { mkdtempSync, rmSync, writeFileSync } = require('node:fs');
const { tmpdir } = require('node:os');
const path = require('node:path');
const { test } = require('node:test');
const { connect } = require('../navigation-host.cjs');

test('cancellation discards a reply in flight and skips a queued request', async () => {
  const cwd = mkdtempSync(path.join(tmpdir(), 'geb-navigation-'));
  // Node runs this stand-in for the host, counting each request it actually receives.
  writeFileSync(path.join(cwd, 'navigation-server'), `
    let sequence = 0;
    require('node:readline').createInterface({ input: process.stdin }).on('line', line =>
      console.log(JSON.stringify({ request: JSON.parse(line), sequence: ++sequence })));
  `);
  const service = connect(process.execPath, 'manifest', cwd);
  try {
    const token = { isCancellationRequested: false };
    const outdated = service.send('old contents', token);
    const queued = service.send('intermediate contents', token);
    await new Promise(resolve => setImmediate(resolve));
    token.isCancellationRequested = true;
    const current = service.send('edited contents', { isCancellationRequested: false });
    assert.equal(await outdated, undefined);
    assert.equal(await queued, undefined);
    assert.deepEqual(await current, { request: 'edited contents', sequence: 2 });
  } finally {
    service.dispose();
    rmSync(cwd, { recursive: true, force: true });
  }
});

test('a project pinned to the one-request host can still navigate', async () => {
  const cwd = mkdtempSync(path.join(tmpdir(), 'geb-navigation-'));
  writeFileSync(path.join(cwd, 'navigation-server'),
    "console.error('usage: geb-author navigation MANIFEST < REQUEST.json'); process.exitCode = 2;");
  const service = connect(process.execPath, 'manifest', cwd, async request => request);
  try {
    for (const payload of ['first', 'second']) {
      assert.equal(await service.send(payload, { isCancellationRequested: false }), payload);
      assert.equal(service.closed, false);
    }
  } finally {
    service.dispose();
    rmSync(cwd, { recursive: true, force: true });
  }
});
