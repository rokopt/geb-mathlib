#!/usr/bin/env bash
#
# scripts/lint-imports.sh
#
# Floodgate-CI per-branch import-rule linter.
#
# Each upstream-eligible subtree has an allowed-import list and one or
# more self-prefixes that must not appear outside the module path of
# an import line. Files in Geb/Cslib/ and GebTests/Cslib/ must import
# `Cslib.Init` per Cslib's `checkInitImports` requirement, and files
# in GebLang/ and GebTests/Lang/ must when they import any Cslib.*
# module. Every upstream-eligible `.lean` file must use Lean 4's
# module system (start with the `module` keyword), since `lake shake`
# minimised-imports enforcement only operates on module-form files.
#
#   Geb/Mathlib/       →  Mathlib.*, Batteries.*, Geb.Mathlib.*,
#                         GebLang.*
#   GebTests/Mathlib/  →  Mathlib.*, Batteries.*, Geb.Mathlib.*,
#                         GebTests.Mathlib.*, GebLang.*
#   Geb/Cslib/         →  Mathlib.*, Batteries.*, Cslib.*,
#                         Geb.Cslib.*, Geb.Mathlib.*, GebLang.*
#                         (plus mandatory `import Cslib.Init`)
#   GebTests/Cslib/    →  Mathlib.*, Batteries.*, Cslib.*,
#                         Geb.Cslib.*, GebTests.Cslib.*,
#                         Geb.Mathlib.*, GebLang.*
#                         (plus mandatory `import Cslib.Init`)
#   GebLang/           →  Mathlib.*, Batteries.*, Cslib.*, GebLang.*,
#                         GebMeta, Lean.DocString.Syntax (plus
#                         `import Cslib.Init` when the file imports
#                          any Cslib.* module)
#   GebTests/Lang/     →  Mathlib.*, Batteries.*, Cslib.*, GebLang.*,
#                         GebTests.Lang.* (same conditional init rule)
#
# `Batteries.*` is admitted to every upstream-eligible subtree because
# mathlib depends on Batteries and imports its modules directly, and
# Cslib depends on mathlib and does the same, so a Batteries import
# survives extraction to either upstream. A second rationale binds the
# mathlib-targeted subtrees alone: the restriction to these prefixes
# can force a module into Geb/Mathlib/ whose target is Lean core or
# Batteries, since a dependency of a Geb/Mathlib/ module cannot live
# in Geb/Internal/. Such a module is not extracted to mathlib4 at all,
# and its destination is open, per TODO.md § Upstream destination of
# core- and Batteries-targeted content.
#
# GebLang holds the Geb language's core data structures, at the bottom
# of the dependency order: its modules import no other library of this
# repository, and every subtree above it may depend on it once its
# allowed list admits the prefix. Each module is retargeted by its own
# import closure, mathlib-track when the closure reaches no Cslib.*
# and Cslib-track otherwise, so the Cslib.Init requirement is
# conditional here rather than per subtree, and
# scripts/check-transitive-imports.sh checks the closures that
# scripts/extract-pr.sh reads to pick a destination. GebMeta and
# Lean.DocString.Syntax are fixed exceptions to GebLang/'s
# allowed-import list rather than a `*`-suffixed prefix: they are the
# literate pipeline's own load-bearing imports, not extractable
# content, and extraction strips them.
#
# `Geb.Mathlib.*` is admitted to the Cslib subtrees because Cslib
# depends on mathlib: a Cslib-destined module may depend on
# mathlib-destined content, shipped in dependency order, after the
# mathlib PR merges and Cslib's mathlib pin advances. The reverse
# direction stays barred: mathlib does not depend on Cslib, so no
# ordering makes a Geb/Mathlib/ module's Cslib.* import extractable.
#
# Test roots additionally permit their own `GebTests.<subtree>.*`
# siblings (mirroring source self-imports); source roots cannot import
# test modules. Both the source self-prefix (`Geb.<subtree>.`) and the
# test self-prefix (`GebTests.<subtree>.`) must not appear outside an
# import line's module path in test files.
#
# Bare umbrella imports (`import Mathlib`, `import Batteries`,
# `import Cslib`, whether plain or `public import` form) are forbidden in
# upstream-eligible files: extraction requires specific module
# imports.
#
# `public import` lines are recognised the same as plain `import`
# (the same allowed-prefix and forbidden-umbrella rules apply, and
# their module path is exempt from the no-prefix-leakage rule).
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
# (each such prefix must not appear outside an import line's module
# path), the second separates the find-roots from the allowed-import
# prefixes.
# <required-init> is the module path of an init file every file
# in this subtree must import ("Cslib.Init"), or that same path
# prefixed with `?` to require it only of a file that imports the
# module's own namespace, or "" for subtrees with no such
# requirement.
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
    if [[ "$p" == *. ]]; then
      allowed_str+="${p}*, "
    else
      allowed_str+="${p}, "
    fi
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
  local import_kw_re='(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+'
  local f line canonical ok ln lp prefix_re
  local init_mod init_ns init_needed
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
      # An allowed entry ending in `.` is a namespace prefix; one that
      # does not is an exact module path (GebMeta,
      # Lean.DocString.Syntax), matched whole so it does not also
      # admit an unwanted submodule, with a trailing comment on the
      # import line still permitted.
      ok=0
      for p in "${allowed_prefixes[@]}"; do
        if [[ "$p" == *. ]]; then
          if [[ "$canonical" == "import ${p}"* ]]; then
            ok=1
            break
          fi
        elif [[ "$canonical" == "import ${p}" \
                || "$canonical" == "import ${p}"[[:space:]]* ]]; then
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
    # specific init module (Cslib's Cslib.Init), every file imports it
    # directly. A `?` prefix on the argument makes the requirement
    # conditional on the file importing that module's own namespace,
    # so a mathlib-track module of a mixed subtree is not forced to
    # import Cslib. The trigger accepts all four import forms; the
    # satisfying import must not be a `meta import`, which does not
    # bring the module into the file's ordinary scope. Transitive
    # satisfaction is not checked here; Cslib's own `checkInitImports`
    # performs the post-extraction verification, and an extracted
    # sibling carries the import through.
    if [[ -n "$required_init" ]]; then
      init_mod="${required_init#\?}"
      init_ns="${init_mod%%.*}."
      init_needed=1
      if [[ "$required_init" == \?* ]]; then
        init_needed=0
        if grep -qE "^${import_kw_re}${init_ns//./\\.}" "$f"; then
          init_needed=1
        fi
      fi
      if [[ "$init_needed" -eq 1 ]] \
         && ! grep -qE "^(public[[:space:]]+)?import ${init_mod//./\\.}([[:space:]]|$)" "$f"; then
        echo "$f: missing required 'import $init_mod'" >&2
        errors=$((errors + 1))
      fi
    fi

    # Rule 2: no-prefix-leakage, for each leakage prefix. A test
    # subtree forbids both the source self-prefix (`Geb.Mathlib.`)
    # and the test self-prefix (`GebTests.Mathlib.`) outside an import
    # path. The exemption covers the import path alone: the module
    # path of an import line is blanked before the search, in all four
    # import forms, so a prefix named in the line's trailing comment
    # is checked like any other prose. `grep -n` numbers the blanked
    # copy, whose line count is the file's; the diagnostic takes the
    # number from there and the text from the file, so it quotes what
    # the author wrote rather than the blanked copy.
    for lp in "${leakage_prefixes[@]}"; do
      prefix_re="${lp//./\\.}"
      if sed -E "s/^(${import_kw_re})[^[:space:]]+/\\1/" "$f" \
           | grep -nE "\\b${prefix_re}" >/dev/null; then
        sed -E "s/^(${import_kw_re})[^[:space:]]+/\\1/" "$f" \
          | grep -nE "\\b${prefix_re}" | cut -d: -f1 | while IFS= read -r ln; do
          echo "$f:$ln:$(sed -n "${ln}p" "$f"): '${lp}' outside an import path" >&2
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
check_subtree "Geb.Mathlib." "GebLang." -- "" Geb/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib." "GebLang."
check_subtree "Geb.Mathlib." "GebTests.Mathlib." "GebLang." -- "" GebTests/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib." "GebTests.Mathlib." "GebLang."
check_subtree "Geb.Cslib." "Geb.Mathlib." "GebLang." -- "Cslib.Init" Geb/Cslib \
  -- "Mathlib." "Batteries." "Cslib." "Geb.Cslib." "Geb.Mathlib." "GebLang."
check_subtree "Geb.Cslib." "GebTests.Cslib." "Geb.Mathlib." "GebLang." -- "Cslib.Init" GebTests/Cslib \
  -- "Mathlib." "Batteries." "Cslib." "Geb.Cslib." "GebTests.Cslib." "Geb.Mathlib." "GebLang."

# GebLang sits at the bottom of the dependency order: its modules
# import no other library of this repository. Its test mirror adds its
# own siblings. Both take the conditional Cslib.Init requirement,
# their modules being mathlib-track or Cslib-track per module rather
# than per subtree.
check_subtree "GebLang." -- "?Cslib.Init" GebLang \
  -- "Mathlib." "Batteries." "Cslib." "GebLang." "GebMeta" "Lean.DocString.Syntax"
check_subtree "GebLang." "GebTests.Lang." -- "?Cslib.Init" GebTests/Lang \
  -- "Mathlib." "Batteries." "Cslib." "GebLang." "GebTests.Lang."

if [ "$errors" -gt 0 ]; then
  echo "lint-imports.sh: $errors violation(s) found" >&2
  exit 1
fi

echo "lint-imports.sh: clean ($total file(s) checked)"
exit 0
