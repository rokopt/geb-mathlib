#!/usr/bin/env bash
# Check the Geb language grammar, package and formatter task in VS Code,
# alone and with the pinned build of Mike's Paredit, whose structural
# fixture it also checks. Install dependencies with
# `npm ci --prefix editors/vscode`. The editor test downloads its pinned
# VS Code host on the first run, and the Paredit build fetches its
# upstream source whenever its pinned inputs change; lake build geb-fmt
# geb-kernel supplies the formatter and checker it invokes.

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

if [ ! -d editors/vscode/node_modules/vscode-textmate ]; then
  echo "test-editor: dependencies absent; run npm ci --prefix editors/vscode; skipping"
  exit 0
fi

npm test --prefix editors/vscode
npm run package --prefix editors/vscode
if [ -n "${DISPLAY:-}${WAYLAND_DISPLAY:-}" ]; then
  npm run test:editor --prefix editors/vscode
  npm run test:paredit --prefix editors/vscode
elif command -v xvfb-run >/dev/null 2>&1; then
  xvfb-run -a npm run test:editor --prefix editors/vscode
  xvfb-run -a npm run test:paredit --prefix editors/vscode
else
  echo "test-editor: grammar and package passed; VS Code needs a display or xvfb-run; skipping"
fi
