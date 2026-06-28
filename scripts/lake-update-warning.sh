#!/usr/bin/env bash
#
# scripts/lake-update-warning.sh
#
# Print a warning when lake-manifest.json is modified outside a
# bump/* or chore/bootstrap branch. Intended for use in the
# pre-push checklist.
#
# Exit 0 always (informational only).

set -euo pipefail

if ! command -v jj >/dev/null 2>&1; then
  exit 0
fi

# diff_against_main (diff against the merge-base with main) is shared
# with pre-push.sh.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/diff-against-main.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/diff-against-main.sh"

# Get current bookmark(s) one per line; trim each, then exact-prefix
# match against allowed forms.
allowed=0
while IFS= read -r bm; do
  case "$bm" in
    bump/*|chore/bootstrap)
      allowed=1
      break
      ;;
  esac
done < <(jj log -r @ -T 'bookmarks ++ "\n"' --no-graph 2>/dev/null \
         | tr ',' '\n' | sed 's/[[:space:]]*$//' | sed 's/^[[:space:]]*//')

if [ "$allowed" -eq 0 ]; then
  changed=$(diff_against_main)
  if echo "$changed" | grep -q '^lake-manifest.json$'; then
    echo "lake-update-warning: lake-manifest.json modified outside bump/* or chore/bootstrap branch" >&2
    echo "  Consider creating a bump/<lean-version> branch for mathlib SHA changes." >&2
  fi
fi

exit 0
