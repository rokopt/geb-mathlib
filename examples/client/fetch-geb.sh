#!/usr/bin/env bash
# Place the Geb release that geb-release.sha256 pins at geb/, in place of a Geb checkout. The pin
# holds the lines of the release's .sha256 files, one for each platform the client is built on;
# the line of this machine's platform names the archive, geb-VERSION-PLATFORM.tar.gz, which is
# downloaded from the release VERSION of GEB_RELEASE_URL (by default the Geb repository's
# releases), checked against the pinned digest and extracted. A geb/ that is not a release is left
# in place and the script fails.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
base=${GEB_RELEASE_URL:-https://github.com/rokopt/geb-mathlib/releases/download}
platform="$(uname -s | tr '[:upper:]' '[:lower:]')-$(uname -m)"
line=$(grep -E "^[0-9a-f]{64}  geb-[^/ ]+-$platform\.tar\.gz\$" geb-release.sha256) || {
  echo "fetch-geb: geb-release.sha256 pins no release for $platform" >&2
  exit 1
}
archive=${line#*  }
version=${archive#geb-}
version=${version%-"$platform".tar.gz}
if [ -e geb ] && [ ! -f geb/geb-release.json ]; then
  echo "fetch-geb: geb/ is not a release; remove it to place the release there" >&2
  exit 1
fi
work=$(mktemp -d .geb-release-XXXXXX)
trap 'rm -rf "$work"' EXIT
curl -fsSL -o "$work/$archive" "$base/$version/$archive"
if command -v sha256sum > /dev/null; then check=(sha256sum -c --quiet); else check=(shasum -a 256 -c -s); fi
(cd "$work" && printf '%s\n' "$line" | "${check[@]}")
tar -C "$work" -xzf "$work/$archive"
rm -rf geb
mv "$work/geb" geb
echo "fetch-geb: geb/ is release $version for $platform"
