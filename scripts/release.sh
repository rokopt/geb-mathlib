#!/usr/bin/env bash
# Package the host executables and the shared library of this checkout as a release archive.
#
#   scripts/release.sh package VERSION DIRECTORY
#
# builds the executables the editor runs and writes, in DIRECTORY, the archive
# geb-VERSION-PLATFORM.tar.gz and its SHA-256 sum geb-VERSION-PLATFORM.tar.gz.sha256, where
# PLATFORM is the system and the machine (linux-x86_64, darwin-arm64, ...). The archive holds one
# directory, geb/, laid out as the checkout's directories a client reads: the executables under
# bin/, stripped of their symbols, the library's sources under library/, the toolchain pin and the
# license, and geb-release.json, which names the release's format, version, platform and revision
# and the SHA-256 of each executable. A client extracts it where it would place the checkout, at
# geb/, and the editor's launcher runs the executables in place, building none
# (editors/vscode/tools.py).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

[ "${1:-}" = package ] && [ $# -eq 3 ] || {
  echo "usage: scripts/release.sh package VERSION DIRECTORY" >&2
  exit 2
}
version=$2
out=$3
case "$version" in
  '' | */* | *[[:space:]]*) echo "release: invalid version: $version" >&2; exit 2 ;;
esac
tools=(geb-author geb-kernel geb-fmt geb-compile geb-defs)
platform="$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)"
revision=$(git rev-parse HEAD 2>/dev/null || jj log --no-graph -r @ -T commit_id 2>/dev/null)

lake build "${tools[@]}"

stage=$(mktemp -d "${TMPDIR:-/tmp}/geb-release-XXXXXX")
trap 'rm -rf "$stage"' EXIT
root="$stage/geb"
mkdir -p "$root/bin" "$root/library"
for tool in "${tools[@]}"; do
  cp .lake/build/bin/"$tool" "$root/bin/$tool"
  strip "$root/bin/$tool"
done
# The library's sources, the bootstrap's linked source among them, as files.
cp -L library/*.geb library/*.manifest "$root/library/"
cp lean-toolchain LICENSE "$root/"

python3 - "$root" "$version" "$platform" "$revision" "${tools[@]}" <<'EOF'
import hashlib, json, sys
from pathlib import Path
root, version, platform, revision, *tools = sys.argv[1:]
root = Path(root)
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
info = {"format": "geb-release/v1", "version": version, "platform": platform,
        "revision": revision, "executables": {t: digest(root / "bin" / t) for t in tools}}
(root / "geb-release.json").write_text(json.dumps(info, indent=2, sort_keys=True) + "\n")
EOF

mkdir -p "$out"
archive="geb-$version-$platform.tar.gz"
tar -C "$stage" -czf "$out/$archive" geb
(cd "$out" && sha256sum "$archive" > "$archive.sha256" 2>/dev/null ||
  shasum -a 256 "$archive" > "$archive.sha256")
echo "release: $out/$archive"
