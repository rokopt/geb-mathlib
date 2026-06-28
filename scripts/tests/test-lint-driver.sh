#!/usr/bin/env bash
#
# scripts/tests/test-lint-driver.sh
#
# Guards the lint-driver configuration that bounds runLinter memory.
# `lake lint` must invoke batteries/runLinter on the single root
# module `Geb`, which loads one flat environment, rather than the
# default no-argument path, under which runLinter re-imports every
# `Geb.*` module in its own environment (many times the memory) and
# exhausts a standard CI runner.
#
# Two properties are checked:
#   1. Invocation form: `lake lint` runs the driver on root module
#      `Geb`, not the "Automatically detecting modules" path. This
#      depends on `lintDriverArgs = ["Geb"]` in lakefile.toml.
#   2. Coverage completeness: every `Geb.*` source module is
#      transitively imported by the `Geb` umbrella, so linting the
#      root module reaches every declaration the no-argument path
#      would have. A module orphaned from the umbrella would escape
#      the linter entirely under the root-module invocation.
#
# Exit 0 if both hold; non-zero otherwise.

set -uo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
failed=0

# --- 1. Invocation form -------------------------------------------------
out="$(lake lint 2>&1)"
rc=$?
if [[ "$rc" -ne 0 ]]; then
  echo "FAIL: 'lake lint' did not pass" >&2
  echo "  output: $out" >&2
  failed=1
fi
if ! grep -qF 'Running linter on specified modules: [Geb]' <<<"$out"; then
  echo "FAIL: 'lake lint' did not invoke runLinter on root module Geb" >&2
  echo "  expected lintDriverArgs = [\"Geb\"] in lakefile.toml" >&2
  echo "  output: $out" >&2
  failed=1
fi
if grep -qF 'Automatically detecting modules to lint' <<<"$out"; then
  echo "FAIL: 'lake lint' took the per-module auto-detect path (high memory)" >&2
  failed=1
fi

# --- 2. Coverage completeness (no module orphaned from the umbrella) -----
# Module name to file path: dots map to slashes; the root module
# `Geb` lives at `Geb.lean`, the rest under `Geb/`.
mod_to_file() { echo "${1//.//}.lean"; }

all_mods="$( { echo Geb; find Geb -name '*.lean' | sed -E 's,/,.,g; s,\.lean$,,'; } | sort -u )"

# Transitive closure of `import Geb.*` reachable from the `Geb` root.
reachable="Geb"
frontier="Geb"
while [[ -n "$frontier" ]]; do
  next=""
  for m in $frontier; do
    f="$(mod_to_file "$m")"
    [[ -f "$f" ]] || continue
    imps="$(grep -oE '^(public )?import Geb(\.[A-Za-z0-9_]+)+' "$f" | sed -E 's/^(public )?import //')"
    for i in $imps; do
      if ! grep -qxF "$i" <<<"$reachable"; then
        reachable="$reachable"$'\n'"$i"
        next="$next $i"
      fi
    done
  done
  frontier="$next"
done
reachable="$(sort -u <<<"$reachable")"

orphans="$(comm -23 <(echo "$all_mods") <(echo "$reachable"))"
if [[ -n "$orphans" ]]; then
  echo "FAIL: Geb modules not reachable from the 'Geb' umbrella (would escape lint):" >&2
  echo "$orphans" | sed 's/^/  /' >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-lint-driver: FAIL" >&2
  exit 1
fi
echo "test-lint-driver: ok"
exit 0
