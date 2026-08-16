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
# Three properties are checked:
#   1. Invocation form: `lake lint` runs the driver on root module
#      `Geb`, not the "Automatically detecting modules" path. This
#      depends on `lintDriverArgs = ["Geb"]` in lakefile.toml.
#   2. Coverage completeness: every `Geb.*`, `GebLang.*` and
#      `GebManual.*` source module is transitively imported by its
#      own umbrella (`Geb`, `GebLang`, `GebManual`), so linting the
#      root module reaches every declaration the no-argument path
#      would have. A module orphaned from its umbrella would escape
#      the linter entirely under the root-module invocation.
#      `GebManual`'s generator root `Main` sits outside the
#      `manual/GebManual/` prefix by design and so outside this
#      scan. `lake lint` itself (§1 above) runs on `Geb` only, so
#      this section checks `GebLang` and `GebManual` coverage
#      statically rather than by executing their own lint
#      invocations.
#   3. `doc-build.yml` retains the `scripts/manual.sh build` and
#      `scripts/literate.sh build` steps, the only places the manual
#      is linted and the literate site is rendered.
#
# Exit 0 if all three hold; non-zero otherwise.

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
# Module name to file path within a library's srcDir; dots map to
# slashes. Geb and GebLang live at the package root; GebManual under
# manual/ (lakefile.toml srcDir), whose generator root Main is outside
# the GebManual prefix by design and so outside this scan.
mod_to_file() { echo "${2}${1//.//}.lean"; }

check_coverage() {
  local root="$1" prefix="$2"
  local all_mods reachable frontier next m f imps i orphans
  all_mods="$( { echo "$root"; find "${prefix}${root}" -name '*.lean' \
    | sed -E "s,^${prefix},,; s,/,.,g; s,\.lean$,,"; } | sort -u )"
  reachable="$root"
  frontier="$root"
  while [[ -n "$frontier" ]]; do
    next=""
    for m in $frontier; do
      f="$(mod_to_file "$m" "$prefix")"
      [[ -f "$f" ]] || continue
      imps="$(grep -oE "^(public )?import ${root}(\.[A-Za-z0-9_]+)+" "$f" \
        | sed -E 's/^(public )?import //')"
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
    echo "FAIL: $root modules not reachable from the '$root' umbrella (would escape lint):" >&2
    echo "$orphans" | sed 's/^/  /' >&2
    failed=1
  fi
}

check_coverage Geb ""
check_coverage GebLang ""
check_coverage GebManual "manual/"

# --- 3. doc-build.yml retains the product build steps --------------------
# The manual is linted only by scripts/manual.sh build, and the
# literate site is rendered only by scripts/literate.sh build, both in
# doc-build.yml; losing either step would silently drop that product.
if ! grep -qF 'scripts/manual.sh build' .github/workflows/doc-build.yml; then
  echo "FAIL: doc-build.yml lost the 'scripts/manual.sh build' step" >&2
  failed=1
fi
if ! grep -qF 'scripts/literate.sh build' .github/workflows/doc-build.yml; then
  echo "FAIL: doc-build.yml lost the 'scripts/literate.sh build' step" >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-lint-driver: FAIL" >&2
  exit 1
fi
echo "test-lint-driver: ok"
exit 0
