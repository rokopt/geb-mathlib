// VS Code's extension-test runner; downloads and user state stay below node_modules.
const { downloadAndUnzipVSCode, resolveCliArgsFromVSCodeExecutablePath,
  runTests } = require('@vscode/test-electron');
const { execFileSync } = require('node:child_process');
const { copyFileSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } = require('node:fs');
const path = require('node:path');
const { editorTest } = require('../package.json');

async function main() {
  const extension = path.resolve(__dirname, '..');
  const root = path.resolve(extension, '../..');
  const cache = path.join(extension, 'node_modules/.cache/editor');
  mkdirSync(cache, { recursive: true });
  const executable = await downloadAndUnzipVSCode({ version: editorTest.vscode, cachePath: cache });
  const [cli, ...args] = resolveCliArgsFromVSCodeExecutablePath(executable, { reuseMachineInstall: true });
  const state = mkdtempSync(path.join(cache, 'run-'));
  // --paredit installs the build of the pinned patch, which patches/build.sh writes,
  // and --paredit-release the Marketplace release it patches, to reproduce its failures.
  const release = process.argv.includes('--paredit-release');
  const paredit = release || process.argv.includes('--paredit');
  const pin = editorTest.paredit;
  const [pareditSource, pareditVersion] = release
    ? [pin.release, pin.release.split('@')[1]]
    : [path.join(extension, `paredit-${pin.version}.vsix`), pin.version];
  // The build gets a fresh extension directory, so it cannot reuse the installed
  // Marketplace release or replace it for subsequent comparison runs.
  const extensions = paredit && !release ? path.join(state, 'extensions')
    : path.join(cache, 'extensions');
  try {
    // A separate workspace folder exercises explicit manifests and distinct project/toolchain roots.
    const project = path.join(state, 'authoring λ with spaces');
    mkdirSync(path.join(project, '.vscode'), { recursive: true });
    for (const file of ['pair.manifest', 'Pair.geb', 'Lists.geb']) {
      copyFileSync(path.join(root, 'examples/authoring', file), path.join(project, file));
    }
    // Proof imports outside the selected workspace folder must also be saved before execution.
    const proofs = path.join(state, 'proofs λ with spaces');
    mkdirSync(proofs);
    copyFileSync(path.join(root, 'examples/authoring/Pair.proofs.geb'),
      path.join(proofs, 'Pair.proofs.geb'));
    writeFileSync(path.join(proofs, 'More.proofs.geb'),
      '(proofs 2 (program pair) (import Pair.proofs.geb)\n' +
      '  (theorem internal-id (internal (X) (forall ((x X)) (equal x x)))\n' +
      '    (by (reduce weak))))\n');
    writeFileSync(path.join(project, 'open.geb'), '(def f (lam ((x T)) (add x ?body)))\n');
    writeFileSync(path.join(project, 'open.manifest'),
      '(program open (edition 0) (document (syntax authoring 0) (schema 0) (prose verso 0)) ' +
      '(sources open.geb) (entries f))\n');
    writeFileSync(path.join(project, '.vscode/settings.json'), JSON.stringify({
      'geb.toolchainDirectory': root,
      'geb.programs': [{ name: 'Editor fixture', manifest: 'pair.manifest',
        proofs: path.join(proofs, 'More.proofs.geb'),
        image: 'out/program.img', certificate: 'out/proof.cert' },
      { name: 'Kernel fixture', manifest: 'open.manifest' }],
    }));
    const workspace = path.join(state, 'editor.code-workspace');
    writeFileSync(workspace, JSON.stringify({ folders: [{ path: root }, { path: project }] }));
    mkdirSync(path.join(state, 'User'));
    writeFileSync(path.join(state, 'User/settings.json'), JSON.stringify({
      'extensions.autoUpdate': false,
      'extensions.autoCheckUpdates': false,
      'update.mode': 'none',
    }));
    if (paredit) {
      execFileSync(cli, [...args, '--extensions-dir', extensions, '--user-data-dir', state,
        '--install-extension', pareditSource, '--force'], {
        stdio: 'inherit', env: { ...process.env, DONT_PROMPT_WSL_INSTALL: '1' },
      });
    }
    await runTests({
      vscodeExecutablePath: executable,
      extensionDevelopmentPath: extension,
      extensionTestsPath: path.join(__dirname, 'editor.cjs'),
      extensionTestsEnv: { GEB_TEST_PAREDIT_VERSION: paredit ? pareditVersion : '',
        GEB_TEST_NAVIGATION_ONLY: process.argv.includes('--navigation') ? '1' : '',
        GEB_TEST_AUTHORING_PROJECT: project, GEB_TEST_AUTHORING_PROOFS: proofs },
      launchArgs: [workspace, '--extensions-dir', extensions, '--user-data-dir', state,
        '--disable-gpu', '--skip-welcome', '--skip-release-notes', '--disable-workspace-trust',
        ...(!paredit ? ['--disable-extension', 'MikeDelmonaco.paredit'] : [])],
    });
  } finally {
    rmSync(state, { recursive: true, force: true });
  }
}

main().catch(error => { console.error(error); process.exitCode = 1; });
