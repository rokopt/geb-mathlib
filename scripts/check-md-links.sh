#!/usr/bin/env bash
#
# scripts/check-md-links.sh [file...]
#
# Report Markdown links whose target does not exist.
#
# With no arguments, scans the tracked `.md` files reported from the
# repository root, so an uncommitted scratch document is not held to the
# rule. With arguments, scans exactly those files, resolving them
# against the current directory.
#
# A link target is resolved relative to the directory of the file
# containing it, which is GitHub's rendering rule and, for a file at the
# repository root, coincides with the repo-relative form
# docs/rules/markdown-writing.md § Link conventions prescribes.
#
# Out of scope, deliberately:
#
#   - External targets (http, https, mailto) and pure fragments
#     (`#section`), which name nothing in the working tree.
#   - Whether a `#fragment` on an existing file names a heading in it.
#     Path existence is what goes stale when a file is deleted or
#     moved; a heading check would have to reproduce doctoc's slug
#     algorithm to avoid false positives.
#
# Link-shaped text inside an inline code span is prose about links, not
# a link, so code spans are stripped before extraction.
#
# Exit 0 when every target resolves; exit 1 with one line per unresolved
# target otherwise.

set -uo pipefail

failed=0

# Report the tracked `.md` files, one per line, relative to the
# repository root (the caller's directory).
#
# jj is the working VCS, so it is authoritative wherever `.jj` exists: a
# workspace added with `jj workspace add` has no `.git` at all, and in a
# colocated workspace the git index is an export of jj's state that is
# refreshed only when a jj command snapshots the working copy. `git
# ls-files` covers the remaining case, a plain git checkout such as CI's.
list_tracked_md() {
  if [ -d .jj ]; then
    jj file list -- 'glob:**/*.md'
  else
    git ls-files '*.md'
  fi
}

check_file() {
  local file="$1" dir target path resolved
  # The file listing reports a file whose deletion is recorded but whose
  # removal has not been committed; it has no links left to check.
  [ -f "$file" ] || return 0
  dir="$(dirname "$file")"
  while IFS= read -r target; do
    case "$target" in
      http://*|https://*|mailto:*|'#'*) continue ;;
    esac
    # Drop any fragment; a link to a fragment of the current file has an
    # empty path and is skipped by the '#'* case above.
    path="${target%%#*}"
    [ -n "$path" ] || continue
    if [ "$dir" = "." ]; then
      resolved="$path"
    else
      resolved="$dir/$path"
    fi
    if [ ! -e "$resolved" ]; then
      echo "$file: link target does not exist: $target" >&2
      failed=$((failed + 1))
    fi
  done < <(sed 's/`[^`]*`//g' "$file" | grep -oE '\]\([^)]+\)' | sed -E 's/^\]\(//; s/\)$//')
}

if [ "$#" -gt 0 ]; then
  for f in "$@"; do
    check_file "$f"
  done
else
  cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)" || exit 1
  # A listing that fails is not a listing of nothing: reporting success
  # on it would report a check that never ran. A repository tracking no
  # Markdown is a listing of nothing, and passes.
  if ! files="$(list_tracked_md)"; then
    echo "check-md-links: could not list the tracked .md files" >&2
    exit 1
  fi
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    check_file "$f"
  done <<<"$files"
fi

if [ "$failed" -ne 0 ]; then
  echo "check-md-links: $failed unresolved link target(s)" >&2
  exit 1
fi

echo "check-md-links: all Markdown link targets resolve"
