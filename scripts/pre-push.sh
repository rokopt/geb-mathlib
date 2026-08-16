#!/usr/bin/env bash
#
# scripts/pre-push.sh
#
# Check repository content before a push to a remote: the Lean
# sources and the Markdown that the build system acts on. The
# build system's own self-tests are a separate concern and live in
# scripts/test-tooling.sh; scripts/pre-push-full.sh runs both, and
# is the one to run for a change touching the build system itself.
#
# Exits non-zero on any failure.

set -euo pipefail

step() {
  echo "==> $*"
}

step "lake exe cache get"
# Fetch the full mathlib olean cache, mirroring CI's
# leanprover/lean-action. Without it, after a toolchain bump only the
# oleans that the root libraries `Geb` and `GebLang` directly import
# are present, and the `lake shake` smoke test below (which injects
# an arbitrary mathlib import) fails with "out of date oleans; fetch
# them from a cache".
#
# Fetch only when the dependency set changes. `cache get` unpacks
# every module whose local Lake trace records a `depHash` other than
# the one in the cache archive (mathlib's
# `Cache.IO.needsDecompression`). For part of the dependency tree the
# two disagree while the artifacts are byte-identical — among them
# `Mathlib.Tactic.Linter.Header`, which `Mathlib.Init` imports and
# hence nearly all of mathlib depends on — so an unconditional fetch
# overwrites a locally built tree that Lake then rebuilds, and the
# two tools alternate on every push.
#
# The cache directory (`MATHLIB_CACHE_DIR`, else `XDG_CACHE_HOME`,
# else `~/.cache/mathlib`) is shared by every jj workspace, and a
# download lands on the fixed name `<hash>.ltar.part` before being
# renamed into place, so two workspaces fetching at once write the
# same file. `flock` serialises them where it is available.
cache_stamp=".lake/cache-get.stamp"
if [ -f "$cache_stamp" ] \
   && cat lean-toolchain lake-manifest.json | cmp -s - "$cache_stamp"; then
  echo "dependency set unchanged since the last fetch; skipping."
else
  mkdir -p "$(dirname "$cache_stamp")"
  cache_dir="${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib}"
  if command -v flock >/dev/null 2>&1; then
    mkdir -p "$cache_dir"
    flock "$cache_dir/.pre-push.lock" lake exe cache get
  else
    lake exe cache get
  fi
  cat lean-toolchain lake-manifest.json > "$cache_stamp"
fi

step "lake build"
lake build

step "lake test"
lake test

step "lake lint"
lake lint

# `lake shake` requires built oleans for every library it scans.
# `lake build` alone honours `defaultTargets` (Geb and GebLang), so
# build `GebTests` explicitly here.
step "lake build GebTests (prerequisite for lake shake)"
lake build GebTests

step "lake lint GebTests (axiom + style linters on tests)"
lake lint -- GebTests

step "lake lint GebLang (axiom + style linters on the language library)"
lake lint -- GebLang

step "lake shake (minimised imports)"
lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang

step "scripts/lint-imports.sh"
bash scripts/lint-imports.sh

step "scripts/check-transitive-imports.sh"
bash scripts/check-transitive-imports.sh

step "scripts/check-commit-msg.sh (branch commits)"
jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
  -T 'description.first_line() ++ "\n"' | bash scripts/check-commit-msg.sh

step "doctoc --dryrun --update-only ."
if command -v doctoc >/dev/null 2>&1; then
  doctoc --dryrun --update-only . \
    || { echo "doctoc TOCs out of date; run 'doctoc --update-only .' and re-commit." >&2; exit 1; }
else
  echo "doctoc not installed; skipping TOC check." >&2
fi

step "markdownlint-cli2 '**/*.md'"
markdownlint-cli2 '**/*.md'

step "scripts/check-md-links.sh"
bash scripts/check-md-links.sh

step "scripts/lake-update-warning.sh"
bash scripts/lake-update-warning.sh

step "docs-coverage check (concept docs in same branch)"
# Project rule: any new concept added to source code must be
# documented in docs/index.md in the same branch.
# Stub implementation: surface a reminder when .lean files in
# Geb/Mathlib/, Geb/Cslib/, Geb/Internal/, or GebLang/ change
# without docs/index.md being touched in the same branch's diff. A
# full implementation would parse new top-level declarations and
# check docs/index.md mentions them; deferred to a future upgrade.
#
# diff_against_main (diff against the merge-base with main) is shared
# with lake-update-warning.sh.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/diff-against-main.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/diff-against-main.sh"

if diff_against_main | grep -qE '^(Geb/Mathlib|Geb/Cslib|Geb/Internal|GebLang)/.*\.lean$'; then
  if ! diff_against_main | grep -q '^docs/index.md$'; then
    echo "" >&2
    echo "REMINDER (docs-coverage):" >&2
    echo "  Lean files under Geb/Mathlib/, Geb/Cslib/," >&2
    echo "  Geb/Internal/, or GebLang/ changed, but" >&2
    echo "  docs/index.md was not touched. Verify each new" >&2
    echo "  concept is reflected in docs/index.md." >&2
  fi
fi

echo "pre-push: clean."
