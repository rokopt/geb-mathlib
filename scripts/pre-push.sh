#!/usr/bin/env bash
#
# scripts/pre-push.sh
#
# Run the pre-push checklist before any push to a remote. Exits
# non-zero on any failure; the user must explicitly authorise the
# push after a clean run.

set -euo pipefail

step() {
  echo "==> $*"
}

step "lake exe cache get"
# Fetch the full mathlib olean cache up front, mirroring CI's
# leanprover/lean-action. Without it, after a toolchain bump only
# the oleans that `Geb` directly imports are present, and the
# `lake shake` smoke test below (which injects an arbitrary mathlib
# import) fails with "out of date oleans; fetch them from a cache".
lake exe cache get

step "lake build"
lake build

step "lake test"
lake test

step "lake lint"
lake lint

# `lake shake` requires built oleans for every library it scans.
# `lake build` alone honours `defaultTargets` (Geb only), so build
# `GebTests` explicitly here.
step "lake build GebTests (prerequisite for lake shake)"
lake build GebTests

step "lake lint GebTests (axiom + style linters on tests)"
lake lint -- GebTests

step "lake shake (minimised imports)"
lake shake --add-public --keep-implied --keep-prefix Geb GebTests

step "scripts/tests/test-lake-shake.sh"
bash scripts/tests/test-lake-shake.sh

step "scripts/lint-imports.sh"
bash scripts/lint-imports.sh

step "scripts/tests/test-lint-imports.sh"
bash scripts/tests/test-lint-imports.sh

step "scripts/tests/test-extract-pr.sh"
bash scripts/tests/test-extract-pr.sh

step "scripts/tests/test-mathlib-bump-detect.sh"
bash scripts/tests/test-mathlib-bump-detect.sh

step "scripts/tests/test-jj-bump-detect.sh"
bash scripts/tests/test-jj-bump-detect.sh

step "scripts/tests/test-regenerate-integration.sh"
bash scripts/tests/test-regenerate-integration.sh

step "scripts/tests/test-diff-against-main.sh"
bash scripts/tests/test-diff-against-main.sh

step "scripts/hooks/tests/test-block-mutating-git.sh"
bash scripts/hooks/tests/test-block-mutating-git.sh

step "doctoc --dryrun --update-only ."
if command -v doctoc >/dev/null 2>&1; then
  doctoc --dryrun --update-only . \
    || { echo "doctoc TOCs out of date; run 'doctoc --update-only .' and re-commit." >&2; exit 1; }
else
  echo "doctoc not installed; skipping TOC check." >&2
fi

step "markdownlint-cli2 '**/*.md'"
markdownlint-cli2 '**/*.md'

step "scripts/tests/test-axiom-linter.sh"
bash scripts/tests/test-axiom-linter.sh

step "scripts/tests/test-lint-driver.sh"
bash scripts/tests/test-lint-driver.sh

step "scripts/lake-update-warning.sh"
bash scripts/lake-update-warning.sh

step "docs-coverage check (concept docs in same branch)"
# Project rule: any new concept added to source code must be
# documented in docs/index.md in the same branch.
# Stub implementation: surface a reminder when .lean files in
# Geb/Mathlib/, Geb/Cslib/, or Geb/Internal/ change without
# docs/index.md being touched in the same branch's diff. A full
# implementation would parse new top-level declarations and check
# docs/index.md mentions them; deferred to a future upgrade.
#
# diff_against_main (diff against the merge-base with main) is shared
# with lake-update-warning.sh.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/diff-against-main.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/diff-against-main.sh"

if diff_against_main | grep -qE '^(Geb/Mathlib|Geb/Cslib|Geb/Internal)/.*\.lean$'; then
  if ! diff_against_main | grep -q '^docs/index.md$'; then
    echo "" >&2
    echo "REMINDER (docs-coverage):" >&2
    echo "  Lean files under Geb/Mathlib/, Geb/Cslib/, or" >&2
    echo "  Geb/Internal/ changed, but docs/index.md was not" >&2
    echo "  touched. Verify each new concept is reflected in" >&2
    echo "  docs/index.md." >&2
  fi
fi

# PR-candidate reminder: triggers on feat/, fix/, refactor/, migrate/
# bookmarks anywhere in the unpushed range (commits reachable from @ but
# not from a remote bookmark). A jj bookmark pins a commit and does not
# follow the working copy, so the topic bookmark is rarely on @ itself;
# checking only @ would miss it. Exact-prefix matching (per-bookmark
# loop) so names like `chore/feat-tooling` do not spuriously match.
is_pr_candidate=0
while IFS= read -r bm; do
  case "$bm" in
    feat/*|fix/*|refactor/*|migrate/*) is_pr_candidate=1; break ;;
  esac
done < <(jj log -r 'bookmarks() & (remote_bookmarks()..@)' \
           -T 'local_bookmarks ++ "\n"' --no-graph 2>/dev/null \
         | tr ',' '\n' | sed 's/[[:space:]]*$//' | sed 's/^[[:space:]]*//')

if [ "$is_pr_candidate" -eq 1 ]; then
  cat >&2 <<'EOF'

REMINDER (PR-candidate branch detected):

- PR descriptions, Zulip messages, and GitHub issue/PR comments
  must be authored by the user, not by an AI agent. (Mathlib's
  LLM policy: "use your own words.")
- The user must review the diff line-by-line before any push.
EOF
fi

# Lean-content reminder (informational; does not prompt).
if diff_against_main | grep -qE '\.lean$'; then
  echo "" >&2
  echo "REMINDER (Lean content changed):" >&2
  echo "  - Run lean4:golf on changed proofs (polish step)." >&2
  echo "  - Run lean4:review on the diff." >&2
  echo "  - For PR-candidate branches, run pr-review-toolkit:review-pr." >&2
fi

echo "pre-push: clean. The user must still review the diff line-by-line and authorise the push."
