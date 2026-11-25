#!/usr/bin/env bash
# The acceptance of a client of the shared library from a fresh clone, in VS Code Insiders.
#
#   scripts/tests/client-acceptance.sh WORKDIR [REVISION]
#   scripts/tests/client-acceptance.sh WORKDIR --release TAG
#
# A client repository is made under the new directory WORKDIR from the template examples/client/
# of REVISION (default HEAD), with its submodule geb/ at REVISION of this checkout and a bare
# repository as its remote. A clone of the remote with its submodule then follows the client
# README's steps: it fetches Lake's caches, builds the host executables and packages the Geb and
# patched Paredit extensions, which editors/vscode/test/run.cjs --client installs into VS Code
# Insiders before running editors/vscode/test/client.cjs on the clone. The run needs a display
# and the network, and from an empty Lake directory the build takes an hour or more.
# With --release, the clone pins the published archive for the current platform, runs its
# CI check and installs the VSIX files from the same release. GEB_RELEASE_URL can also name
# a directory of staged releases served by file://. Run from the checkout matching the tag.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
work=${1:?usage: client-acceptance.sh WORKDIR [REVISION | --release TAG]}
release_tag=
if [ "${2:-}" = --release ]; then
  release_tag=${3:?--release requires a tag}
else
  revision=$(git -C "$root" rev-parse "${2:-HEAD}^{commit}")
fi
[ ! -e "$work" ] || { echo "client-acceptance: $work exists" >&2; exit 1; }
mkdir -p "$work"
work=$(cd "$work" && pwd)
if [ -z "$release_tag" ]; then
  # elan selects the nearest enclosing lean-toolchain when the client invokes Lake.
  dir=$work
  while [ "$dir" != / ]; do
    dir=$(dirname "$dir")
    [ ! -e "$dir/lean-toolchain" ] || {
      echo "client-acceptance: $work is below $dir/lean-toolchain" >&2; rmdir "$work"; exit 1; }
  done
fi
# Local paths stand in for the URLs of the Geb repository and the client's remote, and the
# client's commit is made under a fixed unsigned identity.
git=(git -c protocol.file.allow=always -c commit.gpgsign=false
  -c user.name='Geb client' -c user.email=client@example.invalid)

template="$work/template"
"${git[@]}" init -q "$template"
if [ -n "$release_tag" ]; then
  base=${GEB_RELEASE_URL:-https://github.com/rokopt/geb-mathlib/releases/download}
  platform="$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)"
  cp -R "$root/examples/client/." "$template"
  printf '/geb/\n' >> "$template/.gitignore"
  curl -fsSL "$base/$release_tag/geb-$release_tag-$platform.tar.gz.sha256" \
    -o "$template/geb-release.sha256"
else
  "${git[@]}" -C "$template" submodule add -q "$root" geb
  "${git[@]}" -C "$template/geb" checkout -q "$revision"
  cp -R "$template/geb/examples/client/." "$template"
fi
"${git[@]}" -C "$template" add .
"${git[@]}" -C "$template" commit -q -m 'Client of the shared Geb library'
"${git[@]}" clone -q --bare "$template" "$work/remote.git"

client="$work/client"
"${git[@]}" clone -q --recurse-submodules "$work/remote.git" "$client"
cd "$client"
packages=()
if [ -n "$release_tag" ]; then
  # Record even a failed attempt to invoke Lake from CI or the extension host.
  mkdir "$work/bin" "$work/editors"
  printf '#!/bin/sh\ntouch "$GEB_LAKE_CALLED"\nexit 1\n' > "$work/bin/lake"
  chmod +x "$work/bin/lake"
  export PATH="$work/bin:$PATH" GEB_LAKE_CALLED="$work/lake-called"
  bash fetch-geb.sh
  python3 - "$release_tag" "$platform" <<'PY'
import json, sys
with open('geb/geb-release.json') as f:
    release = json.load(f)
if [release['version'], release['platform']] != sys.argv[1:]:
    sys.exit('client-acceptance: fetched release differs from the requested tag or platform')
PY
  for vsix in geb-language.vsix geb-paredit.vsix; do
    curl -fsSL "$base/$release_tag/$vsix" -o "$work/editors/$vsix"
  done
  packages=(--packages "$work/editors")
else
  (cd geb && lake exe cache get)
  lake -d geb build geb-author geb-kernel geb-fmt geb-compile geb-defs
  npm ci --prefix geb/editors/vscode
  npm run package --prefix geb/editors/vscode
  npm run build:paredit --prefix geb/editors/vscode
fi
bash check.sh
node "$root/editors/vscode/test/run.cjs" --client "$client" "${packages[@]}"
if [ -e "$work/lake-called" ]; then
  echo "client-acceptance: the release client invoked Lake" >&2
  exit 1
fi
