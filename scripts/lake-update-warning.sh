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

# diff_against_main (diff against the merge-base with main) is shared
# with pre-push.sh; it sources lib/vcs.sh, which defines vcs_in_use.
# shellcheck source-path=SCRIPTDIR
# shellcheck source=lib/diff-against-main.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/diff-against-main.sh"

# The current branch names, one per line: under jj the bookmarks of
# @, under git the checked-out branch.
branch_names() {
  case "$(vcs_in_use)" in
    jj)
      jj log -r @ -T 'bookmarks ++ "\n"' --no-graph 2>/dev/null \
        | tr ',' '\n' | sed 's/[[:space:]]*$//' | sed 's/^[[:space:]]*//'
      ;;
    git)
      git branch --show-current 2>/dev/null
      ;;
  esac
}

# Exact-prefix match each name against the allowed forms.
allowed=0
while IFS= read -r bm; do
  case "$bm" in
    bump/*|chore/bootstrap)
      allowed=1
      break
      ;;
  esac
done < <(branch_names)

if [ "$allowed" -eq 0 ]; then
  changed=$(diff_against_main)
  if echo "$changed" | grep -q '^lake-manifest.json$'; then
    echo "lake-update-warning: lake-manifest.json modified outside bump/* or chore/bootstrap branch" >&2
    echo "  Consider creating a bump/<lean-version> branch for mathlib SHA changes." >&2
  fi
fi

exit 0
