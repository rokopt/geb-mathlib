#!/usr/bin/env bash
#
# scripts/lib/diff-against-main.sh
#
# Shared helper for the pre-push checklist scripts (pre-push.sh and
# lake-update-warning.sh). Source this file; it defines
# diff_against_main, which prints the paths changed on the current
# branch relative to its merge-base with main, under whichever VCS
# the checkout uses (lib/vcs.sh).
#
# `fork_point(main | @)` is jj's merge-base revset function (see
# `https://docs.jj-vcs.dev/latest/revsets/` § "Revset functions").
# The `main..@` form is kept as a fallback for a jj that lacks it. If
# fork_point is renamed in a future jj, update the single primary
# definition below. The revsets are named so a regression test can
# assert the primary parses under the active jj
# (scripts/tests/test-diff-against-main.sh).
#
# Under git the diff is taken from the merge-base to the working
# tree, which matches jj's `..@` (the working copy is a commit there)
# except that a file git does not yet track is absent from it.
#
# Not meant to be executed directly.

# shellcheck source-path=SCRIPTDIR
# shellcheck source=vcs.sh
source "$(dirname "${BASH_SOURCE[0]}")/vcs.sh"

DIFF_AGAINST_MAIN_PRIMARY_REVSET='fork_point(main | @)..@'
DIFF_AGAINST_MAIN_FALLBACK_REVSET='main..@'

diff_against_main() {
  case "$(vcs_in_use)" in
    jj)
      jj diff --name-only -r "$DIFF_AGAINST_MAIN_PRIMARY_REVSET" 2>/dev/null \
        || jj diff --name-only -r "$DIFF_AGAINST_MAIN_FALLBACK_REVSET" 2>/dev/null \
        || true
      ;;
    git)
      git diff --name-only "$(git merge-base main HEAD 2>/dev/null)" 2>/dev/null \
        || true
      ;;
  esac
}
