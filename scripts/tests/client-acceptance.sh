#!/usr/bin/env bash
# The acceptance of a client of the shared library from a fresh clone, in VS Code Insiders.
#
#   scripts/tests/client-acceptance.sh WORKDIR [REVISION]
#
# A client repository is made under the new directory WORKDIR from the template examples/client/
# of REVISION (default HEAD), with its submodule geb/ at REVISION of this checkout and a bare
# repository as its remote. A clone of the remote with its submodule then follows the client
# README's steps: it fetches Lake's caches, builds the host executables and packages the Geb and
# patched Paredit extensions, which editors/vscode/test/run.cjs --client installs into VS Code
# Insiders before running editors/vscode/test/client.cjs on the clone. The run needs a display
# and the network, and from an empty Lake directory the build takes an hour or more.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
work=${1:?usage: client-acceptance.sh WORKDIR [REVISION]}
revision=$(git -C "$root" rev-parse "${2:-HEAD}^{commit}")
[ ! -e "$work" ] || { echo "client-acceptance: $work exists" >&2; exit 1; }
mkdir -p "$work"
work=$(cd "$work" && pwd)
# Local paths stand in for the URLs of the Geb repository and the client's remote, and the
# client's commit is made under a fixed unsigned identity.
git=(git -c protocol.file.allow=always -c commit.gpgsign=false
  -c user.name='Geb client' -c user.email=client@example.invalid)

template="$work/template"
"${git[@]}" init -q "$template"
"${git[@]}" -C "$template" submodule add -q "$root" geb
"${git[@]}" -C "$template/geb" checkout -q "$revision"
cp -R "$template/geb/examples/client/." "$template"
"${git[@]}" -C "$template" add .
"${git[@]}" -C "$template" commit -q -m 'Client of the shared Geb library'
"${git[@]}" clone -q --bare "$template" "$work/remote.git"

client="$work/client"
"${git[@]}" clone -q --recurse-submodules "$work/remote.git" "$client"
cd "$client"
(cd geb && lake exe cache get)
lake -d geb build geb-author geb-kernel geb-fmt geb-compile geb-defs
npm ci --prefix geb/editors/vscode
npm run package --prefix geb/editors/vscode
npm run build:paredit --prefix geb/editors/vscode
node "$root/editors/vscode/test/run.cjs" --client "$client"
