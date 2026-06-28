#!/usr/bin/env bash
#
# scripts/lib/diff-against-main.sh
#
# Shared helper for the pre-push checklist scripts (pre-push.sh and
# lake-update-warning.sh). Source this file; it defines
# diff_against_main, which prints the paths changed on the current
# branch relative to its merge-base with main.
#
# `fork_point(main | @)` is jj's merge-base revset function (see
# `https://docs.jj-vcs.dev/latest/revsets/` § "Revset functions").
# The `main..@` form is kept as a fallback for a jj that lacks it. If
# fork_point is renamed in a future jj, update the single primary
# definition below. The revsets are named so a regression test can
# assert the primary parses under the active jj
# (scripts/tests/test-diff-against-main.sh).
#
# Not meant to be executed directly.

DIFF_AGAINST_MAIN_PRIMARY_REVSET='fork_point(main | @)..@'
DIFF_AGAINST_MAIN_FALLBACK_REVSET='main..@'

diff_against_main() {
  jj diff --name-only -r "$DIFF_AGAINST_MAIN_PRIMARY_REVSET" 2>/dev/null \
    || jj diff --name-only -r "$DIFF_AGAINST_MAIN_FALLBACK_REVSET" 2>/dev/null \
    || true
}
