#!/usr/bin/env bash
#
# scripts/regenerate-integration.sh
#
# Regenerate the `integration` bookmark as a fan-in merge of `main`
# plus the tips of all currently-active topic branches whose
# changes are not already reachable from `main`.
#
# The integration bookmark is force-pushed to origin; main is never
# touched.
#
# Each run regenerates an equivalent fan-in (same parents) and
# force-pushes it; the published commit_id differs every run.
#
# Sourceable: `working_copy_has_conflicts` is defined above the
# `main` guard so scripts/tests/test-regenerate-integration.sh can
# exercise the conflict check without running the network IO.

# Return 0 if the working-copy commit (@) records any conflict.
# After the fan-in `jj new`, @ is the candidate integration commit;
# a textual conflict in any merged path makes @ a member of the
# `conflicts()` revset.
working_copy_has_conflicts() {
  [ -n "$(jj log -r 'conflicts() & @' --no-graph \
           -T 'commit_id ++ "\n"')" ]
}

main() {
  set -euo pipefail

  # Refresh lease state before touching the remote. Requires the
  # `origin` remote to be configured; without it, the fetch fails
  # loudly and the script aborts before any local rewrite.
  jj git fetch --remote origin

  # Promote fetched remote bookmarks to local tracking bookmarks so
  # the topic-branch revset (bookmarks(glob:"feat/*"), local)
  # matches them. CI does not carry the per-developer auto-track
  # configuration; an untracked feat/x@origin would otherwise
  # collapse the fan-in to `main` alone. Idempotent: already-tracked
  # bookmarks are left unchanged (jj warns and exits 0).
  jj bookmark track 'glob:*' --remote=origin

  # Guard against unborn `main` (e.g., on a freshly init'd repo
  # before any commits land on main). The fan-in revset's
  # `~ ::main` clauses depend on `::main` being a non-empty set;
  # if main is unborn, this script's behaviour is undefined.
  if [ -z "$(jj log -r main --no-graph -T 'change_id ++ "\n"' \
             2>/dev/null)" ]; then
    echo "regenerate-integration: 'main' bookmark unborn or" \
         "missing; nothing to fan in" >&2
    exit 1
  fi

  # Revset contract: topic-branch tips whose changes are not yet
  # reachable from `main`. See scripts/lib/topic-revset.sh.
  # shellcheck source=scripts/lib/topic-revset.sh
  . "$(dirname "${BASH_SOURCE[0]}")/lib/topic-revset.sh"

  revset="main | $TOPIC_TIPS_NOT_ON_MAIN_REVSET"

  # Resolve the revset to commit IDs to pass to `jj new`
  # (commit_id is stable for scripts that may be retried).
  parents=$(jj log -r "$revset" -T 'commit_id ++ " "' --no-graph)

  if [ -z "$(echo "$parents" | tr -d '[:space:]')" ]; then
    echo "regenerate-integration: empty revset (no main?" \
         "misconfiguration)" >&2
    exit 1
  fi

  # Fan-in merge into a new commit. `date +%F` (not `date -I`, which
  # is GNU-only) for a portable ISO-8601 date.
  # shellcheck disable=SC2086  # parents must word-split into args
  jj new $parents -m "integration: fan-in @ $(date +%F)"

  # Refuse to publish a conflicted fan-in. `jj new` succeeds on a
  # textual conflict, recording it in @ rather than failing; CI
  # does not carry the local `git.private-commits = 'conflicts()'`
  # configuration that would otherwise make the push refuse. The
  # red check on this job is the textual-conflict signal.
  if working_copy_has_conflicts; then
    echo "::error::fan-in has textual conflicts; not publishing" \
         "integration" >&2
    jj resolve --list || true
    exit 1
  fi

  # Move the bookmark to the new fan-in commit. Each regeneration
  # produces a new fan-in that is a sibling of the previous one
  # (the old fan-in is intentionally orphaned and
  # garbage-collected). `--allow-backwards` permits jj to move the
  # bookmark to a non-descendant revision.
  jj bookmark set integration -r @ --allow-backwards

  # Move @ off the fan-in commit. Without this, the working copy is
  # integration: jj's snapshot-on-every-command would amend the
  # fan-in in place, and the bookmark (anchored to @) would
  # silently follow.
  jj new main

  # Push (lease-protected; jj uses git's force-with-lease semantics
  # and has no separate --force flag). First-time push auto-tracks
  # `integration` via the -b <name> form.
  jj git push --remote origin -b integration
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  main "$@"
fi
