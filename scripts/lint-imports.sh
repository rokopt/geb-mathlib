#!/usr/bin/env bash
#
# scripts/lint-imports.sh
#
# Floodgate-CI per-branch import-rule linter.
#
# Each upstream-eligible subtree has an allowed-import list and a
# self-prefix that must not appear outside import lines. Files in
# Geb/Cslib/ and GebTests/Cslib/ additionally must import `Cslib.Init`
# per CSLib's `checkInitImports` requirement. Every upstream-eligible
# `.lean` file must use Lean 4's module system (start with the
# `module` keyword), since `lake shake` minimised-imports
# enforcement only operates on module-form files.
#
#   Geb/Mathlib/       →  Mathlib.*, Batteries.*, Geb.Mathlib.*
#   GebTests/Mathlib/  →  Mathlib.*, Batteries.*, Geb.Mathlib.*,
#                         GebTests.Mathlib.*
#   Geb/Cslib/         →  Mathlib.*, Cslib.*, Geb.Cslib.*
#   GebTests/Cslib/    →  Mathlib.*, Cslib.*, Geb.Cslib.*, GebTests.Cslib.*
#                         (plus mandatory `import Cslib.Init`)
#
# `Batteries.*` is admitted to the mathlib-targeted subtrees because
# mathlib depends on Batteries and imports its modules directly, so a
# Batteries import survives extraction to mathlib4. That rationale
# applies to a module whose own upstream target is mathlib4; the
# restriction to these prefixes can also force a module into
# Geb/Mathlib/ whose target is Lean core or Batteries, since a
# dependency of a Geb/Mathlib/ module cannot live in Geb/Internal/.
# Such a module is not extracted to mathlib4 at all, and its
# destination is open, per TODO.md § Upstream destination of core- and
# Batteries-targeted content.
#
# Test roots additionally permit their own `GebTests.<subtree>.*`
# siblings (mirroring source self-imports); source roots cannot import
# test modules. Both the source self-prefix (`Geb.<subtree>.`) and the
# test self-prefix (`GebTests.<subtree>.`) must not appear outside
# import lines in test files.
#
# Bare umbrella imports (`import Mathlib`, `import Batteries`,
# `import Cslib`, whether plain or `public import` form) are forbidden in
# upstream-eligible files: extraction requires specific module
# imports.
#
# `public import` lines are recognised the same as plain `import`
# (the same allowed-prefix and forbidden-umbrella rules apply,
# and they count as import lines for the no-prefix-leakage rule).
# The module system's `meta import` and `public meta import` forms are
# recognised the same way. The one rule that stays narrow is the
# required-init check: a `meta import Cslib.Init` does not bring
# `Cslib.Init` into a file's ordinary scope, so it does not satisfy
# CSLib's requirement.
#
# Exit 0 on clean. Exit 1 on any violation.

set -euo pipefail

errors=0
total=0

# check_subtree <leakage-prefix>... -- <required-init> <find-root>... -- <allowed-prefix>...
#
# Two `--` separators: the first terminates the leakage-prefix list
# (each such prefix must not appear outside import lines), the second
# separates the find-roots from the allowed-import prefixes.
# <required-init> is the module path of an init file every file
# in this subtree must import (e.g., "Cslib.Init"), or "" for
# subtrees with no such requirement.
check_subtree() {
  local leakage_prefixes=()
  while [[ "$1" != "--" ]]; do
    leakage_prefixes+=("$1"); shift
  done
  shift                      # drop first --
  local required_init="$1"; shift
  local find_roots=()
  while [[ "$1" != "--" ]]; do
    find_roots+=("$1"); shift
  done
  shift                      # drop second --
  local allowed_prefixes=("$@")

  local allowed_str=""
  local p
  for p in "${allowed_prefixes[@]}"; do
    allowed_str+="${p}*, "
  done
  allowed_str="${allowed_str%, }"

  # Collect via a read loop rather than `mapfile`/`readarray`, which
  # are absent from bash 3.2 (the system bash on macOS).
  local files=()
  local _file
  while IFS= read -r _file; do
    files+=("$_file")
  done < <(find "${find_roots[@]}" -type f -name '*.lean' 2>/dev/null || true)

  # The accepted import-line keyword forms: `import`, `public import`,
  # `meta import`, `public meta import`. Bound once and referenced by
  # both Rule 1's collection and Rule 2's exclusion, so the two cannot
  # come to disagree about what an import line is.
  local import_kw_re='(public[[:space:]]+)?(meta[[:space:]]+)?import '
  local f line canonical ok ln lp prefix_re
  for f in "${files[@]}"; do
    total=$((total + 1))

    # Rule 0: module-form requirement. Every upstream-eligible
    # `.lean` file starts with the `module` keyword. Files that
    # omit it cannot participate in lake shake's minimised-imports
    # check (and aren't extractable to either upstream).
    if ! grep -qE '^module([[:space:]]|$|--)' "$f"; then
      echo "$f: missing 'module' header (required for upstream extractability and lake shake)" >&2
      errors=$((errors + 1))
    fi

    # Rule 1: imports. The `public` and `meta` keywords are stripped
    # before pattern matching, so the allowed-prefix and
    # forbidden-umbrella rules apply identically to all four forms.
    while IFS= read -r line; do
      canonical="${line#public }"
      canonical="${canonical#meta }"
      case "$canonical" in
        'import Mathlib'|'import Batteries'|'import Cslib')
          echo "$f: bare umbrella '$line' is forbidden in upstream-eligible files" >&2
          errors=$((errors + 1))
          continue
          ;;
      esac
      ok=0
      for p in "${allowed_prefixes[@]}"; do
        if [[ "$canonical" == "import ${p}"* ]]; then
          ok=1
          break
        fi
      done
      if [[ "$ok" -eq 0 ]]; then
        echo "$f: forbidden import '$line' (allowed: $allowed_str)" >&2
        errors=$((errors + 1))
      fi
    done < <(grep -E "^${import_kw_re}" "$f" || true)

    # Rule 1b: required init import. When the subtree mandates a
    # specific init module (e.g., CSLib's Cslib.Init), every file
    # imports it directly. Transitive satisfaction is not checked
    # here; CSLib's own `checkInitImports` performs the
    # post-extraction verification.
    if [[ -n "$required_init" ]]; then
      if ! grep -qE "^(public[[:space:]]+)?import ${required_init//./\\.}([[:space:]]|$)" "$f"; then
        echo "$f: missing required 'import $required_init'" >&2
        errors=$((errors + 1))
      fi
    fi

    # Rule 2: no-prefix-leakage, for each leakage prefix. A test
    # subtree forbids both the source self-prefix (e.g. `Geb.Mathlib.`)
    # and the test self-prefix (e.g. `GebTests.Mathlib.`) outside
    # import lines. `public import` counts as an import for the
    # exclusion regex, and so does a `meta import` line, in either
    # its bare or its `public` form: docs/rules/upstream-eligible.md
    # § Subtree import rules states the rule as "a self-prefix appears
    # only in ^import lines", which a `meta import` line satisfies.
    # The exclusion is anchored at the `grep -n` line-number prefix, so
    # a comment merely containing the word `import` is not exempted.
    for lp in "${leakage_prefixes[@]}"; do
      prefix_re="${lp//./\\.}"
      if grep -nE "\\b${prefix_re}" "$f" | grep -vE "^[0-9]+:${import_kw_re}" >/dev/null; then
        grep -nE "\\b${prefix_re}" "$f" | grep -vE "^[0-9]+:${import_kw_re}" | while IFS= read -r ln; do
          echo "$f:$ln: '${lp}' outside ^import line" >&2
        done
        errors=$((errors + 1))
      fi
    done
  done
}

# Source roots: cannot import test modules (the test prefix is absent
# from the allowed list). Test roots additionally allow their own
# `GebTests.<subtree>.*` siblings, and forbid leakage of both the
# source and the test self-prefix.
check_subtree "Geb.Mathlib." -- "" Geb/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib."
check_subtree "Geb.Mathlib." "GebTests.Mathlib." -- "" GebTests/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib." "GebTests.Mathlib."
check_subtree "Geb.Cslib." -- "Cslib.Init" Geb/Cslib \
  -- "Mathlib." "Cslib." "Geb.Cslib."
check_subtree "Geb.Cslib." "GebTests.Cslib." -- "Cslib.Init" GebTests/Cslib \
  -- "Mathlib." "Cslib." "Geb.Cslib." "GebTests.Cslib."

if [ "$errors" -gt 0 ]; then
  echo "lint-imports.sh: $errors violation(s) found" >&2
  exit 1
fi

echo "lint-imports.sh: clean ($total file(s) checked)"
exit 0
