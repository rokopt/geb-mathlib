#!/usr/bin/env bash
#
# scripts/pre-push.sh
#
# Check repository content before a push to a remote: the Lean
# sources, the Verso manual and literate site rendered from them,
# and the Markdown that the build system acts on. The build
# system's own self-tests are a separate concern and live in
# scripts/test-tooling.sh; scripts/pre-push-full.sh runs both, and
# is the one to run for a change touching the build system itself.
#
# Usage: scripts/pre-push.sh [--loading=proof|native]
#
# --loading selects how the loading of the metalogic's program is
# checked (Geb/Prototypes/Kernel/LoadCommand.lean), through the
# environment variable GEB_LOADING that the build and the axiom linter
# read. In the mode proof, the default, the kernel checks a proof of each
# step of the loading and the linter permits no axiom of it. In the mode
# native the steps are axioms, declared after the loading is evaluated
# by compiled code, and the linter permits them.
# Lake does not track the variable, so the mode proof, after a run in the
# mode native or with no record of the last run's mode
# (.lake/loading.stamp), deletes the outputs of the modules declaring
# the loading of the metalogic's program, and of those depending on
# them, which the build then remakes with every fact checked.
#
# Exits non-zero on any failure.

set -euo pipefail
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

loading=proof
for arg in "$@"; do
  case "$arg" in
    --loading=proof | --loading=native) loading="${arg#--loading=}" ;;
    *) echo "pre-push: unknown argument $arg" >&2; exit 2 ;;
  esac
done
export GEB_LOADING="$loading"

step() {
  echo "==> $*"
}

step "lake exe cache get"
# Fetch the full mathlib olean cache, mirroring CI's
# leanprover/lean-action. Without it, after a toolchain bump only the
# oleans that the root library `Geb` directly imports are present, and
# the `lake shake` smoke test below (which injects an arbitrary mathlib
# import) fails with "out of date oleans; fetch them from a cache".
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

loading_stamp=".lake/loading.stamp"
if [ "$loading" = proof ] && [ "$(cat "$loading_stamp" 2>/dev/null)" != proof ]; then
  step "delete the outputs of the programs' loading and its dependents (mode proof)"
  for m in GebMirror/Metalogic/Load GebTests/Prototypes/FreeTopos/Agreement/Load \
           GebTests/Prototypes/FreeTopos/Agreement; do
    rm -rf .lake/build/lib/lean/"$m".* .lake/build/ir/"$m".*
  done
  rm -rf .lake/build/lib/lean/GebMirror/Metalogic/Load .lake/build/ir/GebMirror/Metalogic/Load
fi
mkdir -p "$(dirname "$loading_stamp")"
echo "$loading" > "$loading_stamp"

step "lake build"
lake build

step "lake test"
lake test

step "scripts/bootstrap.sh check (bootstrap fixed points)"
bash scripts/bootstrap.sh check

step "scripts/authoring.sh check (recorded Geb development)"
bash scripts/authoring.sh check

# `lake shake` requires built oleans for every library it scans.
# `lake build` alone honours `defaultTargets` (Geb), so
# build `GebTests` explicitly here.
step "lake build GebTests (prerequisite for lake shake)"
lake build GebTests

# The searches' certificates are a function of the generator's compiled
# code and of the committed certificates it reads, as ci.yml keys a
# passing search (docs/rules/ci-and-workflow.md § Certificates), so the
# searches run only when those inputs differ from the ones recorded at
# their last passing check (.lake/certificates-check.stamp).
step "scripts/certificates.sh check (the searches, in parallel)"
lake build geb-certify
certificates_stamp=".lake/certificates-check.stamp"
certificates_inputs() {
  sha256sum .lake/build/bin/geb-certify bootstrap/certificates/*.cert scripts/certificates.sh
}
if [ -f "$certificates_stamp" ] && certificates_inputs | cmp -s - "$certificates_stamp"; then
  echo "the searches' inputs unchanged since their last passing check; skipping."
else
  GEB_CERTIFY=.lake/build/bin/geb-certify bash scripts/certificates.sh check
  certificates_inputs > "$certificates_stamp"
fi

step "lake exe batteries/runLinter GebTests (axiom + style linters on tests)"
lake exe batteries/runLinter GebTests

# literate.sh lints Geb before rendering.
step "scripts/literate.sh build (lint Geb, render the literate site)"
bash scripts/literate.sh build

step "scripts/manual.sh build (build, lint and generate the manual)"
bash scripts/manual.sh build

step "lake shake (minimised imports)"
lake shake --add-public --keep-implied --keep-prefix Geb GebTests

step "scripts/lint-imports.sh"
bash scripts/lint-imports.sh

step "scripts/check-commit-msg.sh (branch commits)"
# The branch's commit subjects under whichever VCS the checkout uses
# (scripts/lib/vcs.sh); sourced here rather than above so the lake
# steps run before anything reads the repository's VCS state.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/vcs.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/vcs.sh"
branch_commit_subjects() {
  case "$(vcs_in_use)" in
    jj)
      jj log --no-graph -r 'fork_point(main | @)..@ ~ merges()' \
        -T 'description.first_line() ++ "\n"'
      ;;
    git)
      git log --no-merges --format=%s "$(git merge-base main HEAD)..HEAD"
      ;;
  esac
}
branch_commit_subjects | bash scripts/check-commit-msg.sh

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
# Geb/Mathlib/, Geb/Cslib/ or Geb/Prototypes/ change without
# docs/index.md being touched in the same branch's diff. A full
# implementation would parse new top-level declarations and
# check docs/index.md mentions them; deferred to a future upgrade.
#
# diff_against_main (diff against the merge-base with main) is shared
# with lake-update-warning.sh.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/diff-against-main.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/diff-against-main.sh"

if diff_against_main | grep -qE '^(Geb/Mathlib|Geb/Cslib|Geb/Prototypes)/.*\.lean$'; then
  if ! diff_against_main | grep -q '^docs/index.md$'; then
    echo "" >&2
    echo "REMINDER (docs-coverage):" >&2
    echo "  Lean files under Geb/Mathlib/, Geb/Cslib/ or" >&2
    echo "  Geb/Prototypes/ changed, but" >&2
    echo "  docs/index.md was not touched. Verify each new" >&2
    echo "  concept is reflected in docs/index.md." >&2
  fi
fi

echo "pre-push: clean."
