#!/usr/bin/env bash
#
# scripts/lib/vcs.sh
#
# Shared helper for the pre-push checklist scripts: which VCS the
# checkout uses, per AGENTS.md § Version control follows the
# checkout. Source this file; it defines vcs_in_use, which prints
# `jj` or `git`.
#
# jj is in use when `jj root` succeeds and names the directory
# `git rev-parse --show-toplevel` names, or git names none (a
# workspace added with `jj workspace add` has no .git). Otherwise git
# is in use: in a git worktree nested inside a colocated repository
# `jj root` walks up to the parent's .jj/ and the two differ, and in
# one placed outside the repository `jj root` fails. The comparison
# is by inode (`-ef`) so a symlinked path does not read as different.
#
# Not meant to be executed directly.

vcs_in_use() {
  local jj_root git_root
  if command -v jj >/dev/null 2>&1 && jj_root="$(jj root 2>/dev/null)"; then
    if ! git_root="$(git rev-parse --show-toplevel 2>/dev/null)" \
       || [ "$jj_root" -ef "$git_root" ]; then
      echo jj
      return 0
    fi
  fi
  echo git
}
