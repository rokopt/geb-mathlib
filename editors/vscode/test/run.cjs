// VS Code's extension-test runner; downloads and user state stay below node_modules.
const { downloadAndUnzipVSCode, resolveCliArgsFromVSCodeExecutablePath,
  runTests } = require('@vscode/test-electron');
const { execFileSync } = require('node:child_process');
const { mkdirSync, mkdtempSync, rmSync, writeFileSync } = require('node:fs');
const path = require('node:path');
const { editorTest } = require('../package.json');

async function main() {
  const extension = path.resolve(__dirname, '..');
  const root = path.resolve(extension, '../..');
  const cache = path.join(extension, 'node_modules/.cache/editor');
  mkdirSync(cache, { recursive: true });
  const executable = await downloadAndUnzipVSCode({ version: editorTest.vscode, cachePath: cache });
  const [cli, ...args] = resolveCliArgsFromVSCodeExecutablePath(executable, { reuseMachineInstall: true });
  const extensions = path.join(cache, 'extensions');
  const state = mkdtempSync(path.join(cache, 'run-'));
  try {
    mkdirSync(path.join(state, 'User'));
    writeFileSync(path.join(state, 'User/settings.json'), JSON.stringify({
      'extensions.autoUpdate': false,
      'extensions.autoCheckUpdates': false,
      'update.mode': 'none',
    }));
    const paredit = process.argv.includes('--paredit');
    if (paredit) {
      execFileSync(cli, [...args, '--extensions-dir', extensions, '--user-data-dir', state,
        '--install-extension', editorTest.paredit, '--force'], {
        stdio: 'inherit', env: { ...process.env, DONT_PROMPT_WSL_INSTALL: '1' },
      });
    }
    await runTests({
      vscodeExecutablePath: executable,
      extensionDevelopmentPath: extension,
      extensionTestsPath: path.join(__dirname, 'editor.cjs'),
      extensionTestsEnv: { GEB_TEST_PAREDIT: paredit ? '1' : '0' },
      launchArgs: [root, '--extensions-dir', extensions, '--user-data-dir', state,
        '--disable-gpu', '--skip-welcome', '--skip-release-notes', '--disable-workspace-trust',
        ...(!paredit ? ['--disable-extension', 'MikeDelmonaco.paredit'] : [])],
    });
  } finally {
    rmSync(state, { recursive: true, force: true });
  }
}

main().catch(error => { console.error(error); process.exitCode = 1; });
