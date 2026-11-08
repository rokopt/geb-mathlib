#!/usr/bin/env bash
# Build Mike's Paredit from the upstream commit and patch that
# package.json pins under editorTest.paredit, with the version it names,
# run upstream's unit tests, and package editors/vscode/paredit-<version>.vsix.
# The build is skipped while the VSIX of the same inputs exists. Requires
# git, patch, network access and the extension's own dependencies, which
# provide vsce (npm ci --prefix editors/vscode).

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
extension="$PWD"

pin() { node -p "require('./package.json').editorTest.paredit.$1"; }
repository="$(pin repository)"
commit="$(pin commit)"
patch_file="$(pin patch)"
version="$(pin version)"
out="paredit-$version.vsix"
inputs="$repository $commit $version $(sha256sum "$patch_file" | cut -d' ' -f1)"

if [ -f "$out" ] && [ "$(cat "$out.inputs" 2>/dev/null)" = "$inputs" ]; then
  echo "paredit: $out is up to date"
  exit 0
fi

vsce="$extension/node_modules/.bin/vsce"
if [ ! -x "$vsce" ]; then
  echo "paredit: $vsce is absent; run npm ci --prefix editors/vscode" >&2
  exit 1
fi
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
git -C "$work" init -q
git -C "$work" fetch -q --depth 1 "$repository" "$commit"
git -C "$work" checkout -q --detach FETCH_HEAD
patch --batch --fuzz=0 -s -d "$work" -p1 < "$patch_file"
npm ci --ignore-scripts --prefix "$work"
npm test --prefix "$work" -- --runInBand
npm pkg set --prefix "$work" version="$version"
(
  cd "$work"
  "$vsce" package --no-dependencies \
    --allow-star-activation --out "$extension/$out.tmp"
)
mv "$out.tmp" "$out"
echo "$inputs" > "$out.inputs"
echo "paredit: built $out"
