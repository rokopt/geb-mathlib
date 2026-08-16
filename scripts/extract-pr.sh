#!/usr/bin/env bash
#
# scripts/extract-pr.sh
#
# Path 1 PR extraction. Given an upstream-eligible source path under
# `Geb/Mathlib/`, `GebTests/Mathlib/`, `Geb/Cslib/`, `GebTests/Cslib/`,
# `GebLang/`, or `GebTests/Lang/`, and a target upstream-fork worktree
# path, copy the file to its upstream destination, rewriting the
# repository-internal module prefixes in each import line's module
# path, converting Verso role markup inside a docstring, and, for the
# `GebLang/` arm alone, deleting outside any docstring the lines that
# have no meaning upstream.
#
# Usage:
#   scripts/extract-pr.sh <src-path> <upstream-fork-root>
#
# Examples:
#   scripts/extract-pr.sh Geb/Mathlib/Foo/Bar.lean ../mathlib4-fork
#   # writes ../mathlib4-fork/Mathlib/Foo/Bar.lean with
#   # `Geb.Mathlib.` and `GebLang.` rewritten to `Mathlib.`
#
#   scripts/extract-pr.sh Geb/Cslib/Foo/Bar.lean ../cslib-fork
#   # writes ../cslib-fork/Cslib/Foo/Bar.lean with `Geb.Cslib.`
#   # rewritten to `Cslib.`, `Geb.Mathlib.` to `Mathlib.`, and each
#   # `GebLang.` import to the prefix of the imported module's own
#   # track
#
# Tracks. A `GebLang/` or `GebTests/Lang/` module is Cslib-track when
# its repository-internal import closure reaches any `Cslib.*` import,
# and mathlib-track otherwise. The track fixes both the module's own
# destination and the prefix an importer rewrites it to, so a
# destination-uniform rewrite would be wrong: a Cslib-track source may
# import a mathlib-track `GebLang` sibling, which ships under
# `Mathlib.`. In a mathlib-destined source the discrimination is
# vacuous, `scripts/check-transitive-imports.sh` keeping every
# mathlib-track closure free of `Cslib.*`.
#
# A `GebTests/Lang/` module's sibling imports do not cross tracks: a
# Cslib-track test importing a mathlib-track sibling would need the
# Cslib test tree to import mathlib's, which no upstream ordering
# makes compile. `scripts/check-transitive-imports.sh` enforces that;
# this script assumes it.
#
# Two repository files can name one upstream destination:
# GebLang/Foo.lean and Geb/Mathlib/Foo.lean both map to
# Mathlib/Foo.lean, and their test parallels both to
# MathlibTest/Foo.lean. The second extraction overwrites the first.
# Nothing detects the collision; the destination path is printed on
# every run, so read it.
#
# Test-directory layouts (verified per upstream):
#   mathlib4: source under Mathlib/, tests under MathlibTest/
#     (singular; renamed from `test/` historically).
#   Cslib:    source under Cslib/, tests under CslibTests/
#     (plural; per Cslib's CONTRIBUTING.md).
# Re-verify before extracting the first real PR for each upstream;
# directory names could change.

set -euo pipefail

if [ $# -ne 2 ]; then
  echo "Usage: $0 <src-path> <upstream-fork-root>" >&2
  exit 1
fi

# Tolerate a leading ./, which `find .` produces.
src="${1#./}"
fork="$2"

if [ ! -f "$src" ]; then
  echo "extract-pr.sh: source file not found: $src" >&2
  exit 1
fi

if [ ! -d "$fork" ]; then
  echo "extract-pr.sh: upstream fork directory not found: $fork" >&2
  exit 1
fi

# The module system's four import-line keyword forms: `import`,
# `public import`, `meta import`, `public meta import`. Bound once and
# used by both the track walk and the rewrite, so the two cannot come
# to disagree about what an import line is.
import_kw_re='(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+'
# Groups: 1 the keyword run, 4 the module path, 5 the rest of the line
# (a trailing comment, when there is one).
import_line_re="^(${import_kw_re})([^[:space:]]+)(.*)$"

# Verso role markup, converted inside a docstring in the one arm
# whose sources carry it: `{role}`x`` becomes `` `x` ``. `doc.verso`
# is set for the GebLang library alone, so an unconverted role would
# render as literal braces upstream, and no other arm, GebTests/Lang/
# included, has anything to convert.
#
# Two restrictions, and both are needed. The braces hold one of the
# role names this repository writes, which docs/rules/lean-coding.md
# § Literate modules fixes as a closed set: `name` for a constant that
# must resolve, `option` for a Lean option, `lit` for anything else.
# And the match runs through the code span's closing backtick, so the
# span is consumed in one pass.
#
# The second restriction is what keeps the substitution off Lean. A
# brace group holding an identifier is ordinary Lean and appears
# inside code spans constantly, the role names included, since `name`,
# `lit` and `option` are themselves ordinary identifiers:
#
#   `s ∪ {a}`   `theorem foo {n}`   `Type.{u}`   `{S}`
#   `freeVars (var name) = {name}`  `opts = {option}`
#
# Without consuming the span, sed's `g` flag resumes scanning inside
# the span it has just opened and eats the second group as another
# match, so the last two lose their singleton. With it, a group inside
# a span is never rescanned and every line above survives.
#
# Every leading context a role appears in converts: line start, space,
# parenthesis, bracket, list marker, emphasis underscore. The second
# of two abutting roles does not, the closing backtick of the first
# being in the excluded leading class; no Verso prose writes that.
#
# A role outside the set, including any role taking arguments, is left
# unconverted and ships as literal braces. That is the intended
# failure: braces upstream are visible and get fixed, where deleted
# mathematics is not. Add a new role's exact name here when one is
# first used.
role_strip='s/(^|[^A-Za-z0-9.`])[{](lit|name|option)[}]`([^`]*)`/\1`\3`/g'

# convert_roles is 1 for the one arm reading doc.verso sources. It
# gates applying role_strip at all; the docstring gate in the copy
# loop below further restricts each application to a line inside a
# docstring. A role-shaped brace group outside a docstring is
# ordinary Lean, not markup, e.g. in
# `def a : List Name := [{name}`foo, `bar]`, a singleton set literal
# followed by a `Name` literal, and role_strip would convert it
# wrongly if it ran there. `lit`, `name` and `option` are themselves
# ordinary identifiers, so the restriction cannot live in role_strip's
# own pattern (see its comment above); it has to be where the line is,
# which only the copy loop knows.
#
# An earlier form applied role_strip to every line unconditionally,
# on the reasoning that an import line's module path holds no braces
# and so needs no exemption; that reasoning does not extend to a code
# line's own brace groups, which is the regression this docstring
# gate exists to prevent.

# strip_line <line>: true when the GebLang/ arm's third pass deletes
# <line> outright: an import line naming `GebMeta` or
# `Lean.DocString.Syntax`, in any of the four import forms, with or
# without a trailing comment; or a line whose only content is the
# `mathlib_linters` command. None of the three has meaning upstream:
# `GebMeta` and its two import lines exist only to reach mathlib's
# linters from inside a `doc.verso` module (docs/rules/lean-coding.md
# § Literate modules), the `Lean.DocString.Syntax` import is an
# artifact of the Verso role markup the copy loop's docstring gate
# scopes role_strip to, and the command itself is registered nowhere
# upstream. Anchored the way the import-prefix rewrite is: an import
# line by the import-keyword regex the script already binds once, the
# command line by a whole-line match. A docstring line that merely
# contains the word `GebMeta`, or an English sentence whose first word
# is `import`, is prose and is not this function's concern, and
# neither is a fenced code block's body line reading `mathlib_linters`
# or `import GebMeta`: the copy loop's docstring gate keeps this
# function from being called on any line inside a docstring at all, a
# real import line or command line never being inside one.
strip_line() {
  [ "$1" = "mathlib_linters" ] && return 0
  if [[ "$1" =~ $import_line_re ]]; then
    case "${BASH_REMATCH[4]}" in
      GebMeta|Lean.DocString.Syntax) return 0 ;;
    esac
  fi
  return 1
}

# module_file <Module.Name>: the repository path of a module, whose
# name maps onto directories (`GebLang.Foo.Bar` is
# `GebLang/Foo/Bar.lean`).
module_file() {
  echo "${1//./\/}.lean"
}

# track_of <file>: prints `cslib` when the repository-internal import
# closure of <file>, followed through its `GebLang.` and
# `GebTests.Lang.` imports, carries any `Cslib.*` import; prints
# `mathlib` otherwise. A module with no file on disk contributes
# nothing to the walk, so an import naming one resolves to
# mathlib-track and is emitted under `Mathlib.`; `lake build` is what
# catches the missing module, neither this script nor
# scripts/lint-imports.sh checking existence. The worklist is carried
# in space-separated strings rather than an associative array, which
# bash 3.2 (the system bash on macOS) does not provide; repository
# paths contain no spaces.
track_of() {
  local seen=" " frontier="$1" next f m
  while [ -n "$frontier" ]; do
    next=""
    for f in $frontier; do
      case "$seen" in
        *" $f "*) continue ;;
      esac
      seen="$seen$f "
      [ -f "$f" ] || continue
      if grep -qE "^${import_kw_re}Cslib\." "$f"; then
        echo cslib
        return 0
      fi
      for m in $(grep -E "^${import_kw_re}(GebLang|GebTests)\." "$f" \
                   | sed -E "s/^${import_kw_re}//; s/[[:space:]].*$//"); do
        case "$m" in
          GebLang.*|GebTests.Lang.*) next="$next $(module_file "$m")" ;;
        esac
      done
    done
    frontier="$next"
  done
  echo mathlib
}

# resolve_target <target-spec> <imported-module>: the destination
# prefix a rewrite emits. A literal spec is emitted as written; `@src`
# and `@test` resolve by the imported module's own track, into the
# upstream source tree and the upstream test tree respectively.
resolve_target() {
  case "$1" in
    @src)
      case "$(track_of "$(module_file "$2")")" in
        cslib) echo "Cslib." ;;
        *)     echo "Mathlib." ;;
      esac
      ;;
    @test)
      case "$(track_of "$(module_file "$2")")" in
        cslib) echo "CslibTests." ;;
        *)     echo "MathlibTest." ;;
      esac
      ;;
    *) echo "$1" ;;
  esac
}

# Map the source path to its destination and collect the arm's rewrite
# table: one `<source-prefix> <target-spec>` pair per line, first match
# winning. The prefixes within an arm are pairwise non-overlapping.
case "$src" in
  Geb/Mathlib/*)
    # Unconditional: a Geb/Mathlib/ module whose own upstream target is
    # Lean core or Batteries rather than mathlib4 extracts to the wrong
    # upstream here, silently. Such modules exist because the subtree
    # import rules leave nowhere else to put them; the destination is
    # open, per TODO.md § Upstream destination of core- and
    # Batteries-targeted content, and this mapping waits on its outcome.
    dst_rel="Mathlib/${src#Geb/Mathlib/}"
    convert_roles=0
    strip_pass=0
    rewrites='Geb.Mathlib. Mathlib.
GebLang. Mathlib.'
    ;;
  GebTests/Mathlib/*)
    # Unconditional in the same way as the arm above, and with the same
    # consequence for the test parallel of a core- or Batteries-targeted
    # module; this mapping waits on the same TODO.md item's outcome.
    dst_rel="MathlibTest/${src#GebTests/Mathlib/}"
    convert_roles=0
    strip_pass=0
    rewrites='Geb.Mathlib. Mathlib.
GebTests.Mathlib. MathlibTest.
GebLang. Mathlib.'
    ;;
  Geb/Cslib/*)
    dst_rel="Cslib/${src#Geb/Cslib/}"
    convert_roles=0
    strip_pass=0
    rewrites='Geb.Cslib. Cslib.
Geb.Mathlib. Mathlib.
GebLang. @src'
    ;;
  GebTests/Cslib/*)
    dst_rel="CslibTests/${src#GebTests/Cslib/}"
    convert_roles=0
    strip_pass=0
    rewrites='Geb.Cslib. Cslib.
GebTests.Cslib. CslibTests.
Geb.Mathlib. Mathlib.
GebLang. @src'
    ;;
  GebLang/*)
    # `@src` in a mathlib-track source resolves to `Mathlib.` for every
    # sibling, its closure being all mathlib-track; one code path
    # serves both tracks.
    case "$(track_of "$src")" in
      cslib) dst_rel="Cslib/${src#GebLang/}" ;;
      *)     dst_rel="Mathlib/${src#GebLang/}" ;;
    esac
    convert_roles=1
    strip_pass=1
    rewrites='GebLang. @src'
    ;;
  GebTests/Lang/*)
    case "$(track_of "$src")" in
      cslib) dst_rel="CslibTests/${src#GebTests/Lang/}" ;;
      *)     dst_rel="MathlibTest/${src#GebTests/Lang/}" ;;
    esac
    # GebTests/Lang/ belongs to the GebTests library, which does not
    # set doc.verso, so its docstrings are Markdown and carry no
    # roles to convert, and it carries neither `GebMeta` nor
    # `Lean.DocString.Syntax` (docs/rules/lean-coding.md
    # § Literate modules), so it has nothing for the strip pass to
    # remove either.
    convert_roles=0
    strip_pass=0
    rewrites='GebLang. @src
GebTests.Lang. @test'
    ;;
  *)
    echo "extract-pr.sh: source path must be under Geb/Mathlib/, GebTests/Mathlib/, Geb/Cslib/, GebTests/Cslib/, GebLang/, or GebTests/Lang/" >&2
    exit 1
    ;;
esac

dst="$fork/$dst_rel"

mkdir -p "$(dirname "$dst")"

# Docstring gate: Lean block comments nest (`/--` and `/-!` open a
# docstring, a bare `/-` opens an ordinary block comment, `-/` closes
# whichever is innermost), so the gate tracks nesting `depth` rather
# than a single open/closed flag: a line is inside a docstring when
# `depth` is at least one and `doc_outer` records that the opener at
# depth zero was `/--` or `/-!` rather than a bare `/-`. A `/- ... -/`
# block comment nested inside a docstring no longer ends the
# docstring at its own `-/`: that `-/` only returns `depth` to the
# outer docstring's level, `doc_outer` is set only when an opener is
# seen at depth zero, and role conversion and the strip pass both
# read `depth`/`doc_outer` together, so a role after the nested
# comment converts and an import or command line inside one is not
# silently deleted, the failure mode a single flag had.
#
# in_doc is evaluated from the state on entry to the line, before
# that state is updated by scanning the line's own tokens, so a role
# on a docstring's opening or closing line still converts (matching
# the single-flag gate's contract); it is then re-evaluated after
# every token the line contains, in case the line's own tokens enter
# a docstring (covering a single-line `/-- ... -/` docstring, which
# opens and closes on the same line) or a nested comment inside one.
#
# Tokens are extracted by `grep -oE`, which is leftmost-longest per
# POSIX ERE, so at a position where `/--` or `/-!` (three characters)
# matches, the shorter `/-` alternative does not also match there and
# is not double-counted; a plain `/-` is recognised where the third
# character is neither `-` nor `!`. Tokens are then walked in the
# order they appear on the line, rather than counting opens and
# closes separately, because a line can open and close more than
# once, in either order (e.g. `-/ /-- new doc -/`, a docstring
# closing then a new one opening and closing), and only an in-order
# walk gets every intermediate depth right.
#
# The counter follows Lean's own lexer rather than an approximation
# of it: block comments nest, and a docstring is one, so a `/-` left
# unbalanced inside a docstring — including one inside an inline code
# span, which the lexer does not exempt — is a compile error, not
# input the counter has to get right. Verified against the compiler
# for both halves: `/-- ... `a /- b` inline. -/` fails to compile
# ("unterminated comment"), and the same shape with the nested
# comment closed, `/-- ... /- ... -/ ... -/`, compiles. A file that
# builds, which is everything the pre-push checklist and CI accept,
# cannot contain the first shape, so the counter cannot desync on one
# that does.
#
# Copy, deleting the GebLang/ arm's non-upstream lines outside any
# docstring, rewriting each remaining import line's module path by
# the arm's table, and converting Verso roles inside a docstring in
# the arm that carries them. The strip pass runs before the rewrite
# table: a stripped line's module path (if any) never reaches it.
# After a stripped line, a single immediately following blank line is
# skipped too, so deleting a line that sits between two blank lines
# (the `mathlib_linters` command does) does not leave two consecutive
# blank lines behind; the flag is set on the stripped line and
# consumed, blank or not, by the very next line, so it never survives
# past one line's lookahead. Role conversion runs last, on the
# rewritten line, so a role in an import line's trailing comment
# still converts, on the arm where both apply.
#
# The read loop terminates every line, so a source with no final
# newline gains one; upstream wants it. The rewrite is anchored to the
# import keyword and applied to the module path alone, rather than by a
# within-line `\b` word boundary, which is non-portable (GNU sed only;
# not BSD or macOS, the same constraint block-mutating-git.sh
# documents). Anchoring also rules out matching a prefix embedded in a
# longer identifier, and confines the rewrite to the module path, so a
# prefix named in an import line's trailing comment survives as prose.
{
  strip_skip_blank=0
  depth=0
  doc_outer=0
  while IFS= read -r line || [ -n "$line" ]; do
    in_doc=0
    if [ "$depth" -ge 1 ] && [ "$doc_outer" -eq 1 ]; then in_doc=1; fi
    while IFS= read -r tok; do
      case "$tok" in
        -/)
          [ "$depth" -gt 0 ] && depth=$((depth - 1))
          ;;
        *)
          if [ "$depth" -eq 0 ]; then
            case "$tok" in
              '/--'|'/-!') doc_outer=1 ;;
              *)           doc_outer=0 ;;
            esac
          fi
          depth=$((depth + 1))
          ;;
      esac
      if [ "$depth" -ge 1 ] && [ "$doc_outer" -eq 1 ]; then in_doc=1; fi
    done < <(grep -oE '/--|/-!|-/|/-' <<< "$line")

    if [ "$strip_pass" -eq 1 ]; then
      if [ "$strip_skip_blank" -eq 1 ]; then
        strip_skip_blank=0
        [ -z "$line" ] && continue
      fi
      if [ "$in_doc" -eq 0 ] && strip_line "$line"; then
        strip_skip_blank=1
        continue
      fi
    fi
    if [[ "$line" =~ $import_line_re ]]; then
      kw="${BASH_REMATCH[1]}"
      mod="${BASH_REMATCH[4]}"
      rest="${BASH_REMATCH[5]}"
      while read -r prefix spec; do
        [ -n "$prefix" ] || continue
        case "$mod" in
          "$prefix"*)
            mod="$(resolve_target "$spec" "$mod")${mod#"$prefix"}"
            break
            ;;
        esac
      done <<REWRITES
$rewrites
REWRITES
      out="$kw$mod$rest"
    else
      out="$line"
    fi
    if [ "$convert_roles" -eq 1 ] && [ "$in_doc" -eq 1 ]; then
      printf '%s\n' "$out" | sed -E "${role_strip}"
    else
      printf '%s\n' "$out"
    fi
  done < "$src"
} > "$dst"

echo "extract-pr.sh: $src -> $dst"
