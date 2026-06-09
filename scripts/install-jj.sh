#!/usr/bin/env bash
#
# scripts/install-jj.sh
#
# Install the pinned `jj` release binary into /usr/local/bin for
# CI. The version is read from scripts/jj-version (no leading `v`);
# the GitHub release tag and asset name add the `v` prefix.
#
# Target is the GitHub Actions ubuntu-latest runner: x86_64 Linux.
# A different platform fails loudly rather than installing a
# mismatched binary.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
version="$(tr -d '[:space:]' < "$here/jj-version")"

if [ -z "$version" ]; then
  echo "install-jj: scripts/jj-version is empty" >&2
  exit 1
fi

arch="$(uname -m)"
kernel="$(uname -s)"
if [ "$arch" != "x86_64" ] || [ "$kernel" != "Linux" ]; then
  echo "install-jj: unsupported platform ${kernel}/${arch};" \
       "this installer targets x86_64 Linux runners" >&2
  exit 1
fi

asset="jj-v${version}-x86_64-unknown-linux-musl.tar.gz"
url="https://github.com/jj-vcs/jj/releases/download/v${version}/${asset}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "install-jj: downloading ${url}" >&2
curl -fsSL "$url" -o "$tmp/jj.tar.gz"
tar -xzf "$tmp/jj.tar.gz" -C "$tmp"
sudo install -m 0755 "$tmp/jj" /usr/local/bin/jj

installed="$(jj --version)"
case "$installed" in
  *"$version"*) echo "install-jj: installed ${installed}" >&2 ;;
  *)
    echo "install-jj: version mismatch: wanted ${version}," \
         "got '${installed}'" >&2
    exit 1
    ;;
esac
