#!/usr/bin/env bash
#
# scripts/check-transitive-imports.sh
#
# Floodgate check on import closures, run beside
# scripts/lint-imports.sh, which bounds direct imports only.
#
# A `Geb/Mathlib/` or `GebTests/Mathlib/` module whose `GebLang`
# dependencies reach `Cslib.*` has become Cslib-track and belongs
# under `Geb/Cslib/` or `GebTests/Cslib/`: extraction would otherwise
# ship it to mathlib4 carrying a Cslib dependency mathlib does not
# have.
#
# Pass 1 walks the repository-internal import closure of every
# `Geb/Mathlib/` and `GebTests/Mathlib/` module, following `Geb.*`,
# `GebTests.*` and `GebLang.*` imports in all four import forms
# (`import`, `public import`, `meta import`, `public meta import`),
# and fails when any file in a closure carries a `Cslib.*` import. On
# a lint-clean tree the walk cannot enter `Geb/Cslib/`, no allowed
# import reaching it from a mathlib-track root, so a failure is a
# genuine misplacement rather than a false positive.
#
# Pass 2 covers the test subtree's mixed case: every `GebTests.Lang.`
# sibling of a Cslib-track `GebTests/Lang/` module is itself
# Cslib-track, since a mathlib-track sibling ships to a test tree the
# Cslib test tree cannot import. One direction suffices: track is
# closure-defined, so a module importing a Cslib-track sibling is
# itself Cslib-track, and the reverse crossing cannot occur.
#
# Runs against the working directory, as scripts/lint-imports.sh does,
# so the self-test can stage a synthetic tree.
#
# Pass 1 recomputes each root's closure from scratch and greps every
# file in it twice, so the cost grows with the number of roots times
# the average closure size, and runs several times slower than
# scripts/lint-imports.sh over the same files. Caching reaches_cslib
# per file is the repair when that ratio starts to matter.
#
# Exit 0 on clean. Exit 1 on any violation.

set -uo pipefail

errors=0
total=0

# The module system's four import-line keyword forms.
import_kw_re='(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+'

# module_file <Module.Name>: the repository path of a module, whose
# name maps onto directories.
module_file() {
  echo "${1//./\/}.lean"
}

# imported_internal <file>: the repository-internal modules a file
# imports, one per line.
imported_internal() {
  grep -E "^${import_kw_re}(Geb|GebTests|GebLang)\." "$1" 2>/dev/null \
    | sed -E "s/^${import_kw_re}//; s/[[:space:]].*$//"
}

# closure <file>: every existing repository file reachable from <file>
# through repository-internal imports, itself included, one path per
# line. The worklist is carried in space-separated strings rather than
# an associative array, which bash 3.2 (the system bash on macOS) does
# not provide; repository paths contain no spaces.
closure() {
  local seen=" " frontier="$1" next f m
  while [ -n "$frontier" ]; do
    next=""
    for f in $frontier; do
      case "$seen" in
        *" $f "*) continue ;;
      esac
      seen="$seen$f "
      [ -f "$f" ] || continue
      echo "$f"
      for m in $(imported_internal "$f"); do
        next="$next $(module_file "$m")"
      done
    done
    frontier="$next"
  done
}

# reaches_cslib <file>: exit 0 when the closure of <file> carries any
# `Cslib.*` import.
reaches_cslib() {
  local f
  for f in $(closure "$1"); do
    if grep -qE "^${import_kw_re}Cslib\." "$f"; then
      return 0
    fi
  done
  return 1
}

# --- Pass 1: no mathlib-track root reaches Cslib ------------------------
for f in $(find Geb/Mathlib GebTests/Mathlib -type f -name '*.lean' \
             2>/dev/null || true); do
  total=$((total + 1))
  if reaches_cslib "$f"; then
    echo "$f: its import closure reaches Cslib.*; the module is Cslib-track and belongs under Geb/Cslib/ or GebTests/Cslib/" >&2
    errors=$((errors + 1))
  fi
done

# --- Pass 2: GebTests/Lang/ siblings do not cross tracks ----------------
for f in $(find GebTests/Lang -type f -name '*.lean' 2>/dev/null || true); do
  total=$((total + 1))
  reaches_cslib "$f" || continue
  for m in $(imported_internal "$f"); do
    case "$m" in
      GebTests.Lang.*) ;;
      *) continue ;;
    esac
    sib="$(module_file "$m")"
    [ -f "$sib" ] || continue
    if ! reaches_cslib "$sib"; then
      echo "$f: Cslib-track test imports the mathlib-track sibling $m; the Cslib test tree cannot import mathlib's" >&2
      errors=$((errors + 1))
    fi
  done
done

if [ "$errors" -gt 0 ]; then
  echo "check-transitive-imports.sh: $errors violation(s) found" >&2
  exit 1
fi

echo "check-transitive-imports.sh: clean ($total file(s) checked)"
exit 0
