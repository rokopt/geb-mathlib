# GebLang floodgate integration implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Executor context](#executor-context)
- [File structure](#file-structure)
- [Commit ordering](#commit-ordering)
- [Task 1: extend `scripts/extract-pr.sh`](#task-1-extend-scriptsextract-prsh)
- [Task 2: add `scripts/check-transitive-imports.sh`](#task-2-add-scriptscheck-transitive-importssh)
- [Task 3: the `scripts/lint-imports.sh` mechanism and the new entries](#task-3-the-scriptslint-importssh-mechanism-and-the-new-entries)
- [Task 4: widen the four existing allowed-import lists](#task-4-widen-the-four-existing-allowed-import-lists)
- [Task 5: the rule documents](#task-5-the-rule-documents)
- [Task 6: the enumeration sweep](#task-6-the-enumeration-sweep)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** make every `GebLang` import shippable, by extending the
extraction tooling and the import lint before widening any
allowed-import list, and record the resulting policy in the rule
documents.

**Architecture:** `GebLang` sits at the bottom of the dependency
order, and each of its modules is retargeted by its own import
closure: mathlib-track when the closure reaches no `Cslib.*`,
Cslib-track otherwise. `scripts/extract-pr.sh` gains that track
determination and rewrites each import by the imported module's own
track; `scripts/check-transitive-imports.sh` keeps the mathlib-track
roots free of Cslib-track dependencies; `scripts/lint-imports.sh`
gains the two new subtree entries and then the widened lists. The
rule documents follow the mechanism, not the reverse.

**Tech Stack:** bash (portable to bash 3.2, the system bash on
macOS), GitHub Actions, Lean 4, Lake, `jj`.

**Spec:** `docs/superpowers/specs/2026-08-15-geblang-literate-design.md`

This is the second of the two plans that spec mandates
(§ Import rules). It executes after
`docs/superpowers/plans/2026-08-15-geblang-library.md`, which creates
`GebLang.lean`, `GebLang/Basic.lean`, `GebTests/Lang.lean`,
`GebTests/Lang/Basic.lean`, `literate.toml` and
`scripts/literate.sh`, and which makes no floodgate change.

## Global constraints

Copied from the spec and the repository rules; every task's
requirements implicitly include this section.

- **The floodgate invariant holds commit by commit, from this plan's
  first commit on.** At every commit from Task 1 onward, every file in
  an upstream-eligible location can be extracted to a compiling
  upstream PR with no source-code changes. This is what fixes the
  commit ordering below: a widened allowed-import list must not
  precede the tooling that keeps the newly permitted imports
  shippable.

  One window escapes it, and that window is inside plan 1 rather than
  here. Plan 1 creates `GebLang/Basic.lean` and
  `GebTests/Lang/Basic.lean`, and until this plan's Task 1
  `scripts/extract-pr.sh` rejects both roots outright and leaves their
  Verso role markup unconverted. The window is a consequence of the
  spec's mandated plan split, which puts the library before the
  floodgate work; no ordering of the two plans closes it, since the
  extraction extension has nothing to extract until the library
  exists. Task 1 is this plan's first commit precisely so the window
  is as short as the split allows. It is on the list of items for the
  user's review.
- Shell scripts stay portable to bash 3.2: no `mapfile`, no
  `readarray`, no associative arrays (`declare -A`), no `\b` inside a
  `sed` expression (GNU only; `grep -E` already uses `\b` in this
  repository and stays as it is).
- The repository's own module prefixes are `Geb.`, `GebTests.` and
  `GebLang.`. The four import forms are `import`, `public import`,
  `meta import` and `public meta import`; every rule that enumerates
  import forms covers all four, except the `Cslib.Init` requirement,
  which a `meta import` does not satisfy because it does not bring
  the module into the file's ordinary scope.
- Upstream test-directory layouts: mathlib4 keeps sources under
  `Mathlib/` and tests under `MathlibTest/`; Cslib keeps sources
  under `Cslib/` and tests under `CslibTests/`.
- Cross-track dependency runs in one direction only. Cslib-destined
  content may depend on mathlib-destined content, shipping after its
  dependencies merge and Cslib's mathlib pin advances, exactly as
  Cslib itself depends on mathlib. Content destined for mathlib
  depends on no Cslib-destined content.
- Markdown: 80-character lines outside tables and code blocks;
  `doctoc` markers in every committed document with more than one
  `##` heading; internal links are repository-relative paths.
- Commit subjects: `<type>(<scope>): <subject>`, imperative present
  tense, lowercase first letter, no trailing period, under 72
  characters (`scripts/check-commit-msg.sh`).

## Executor context

Context a fresh executor cannot recover from the spec.

- **Version control is `jj`, not raw `git`.** Mutating raw `git`
  commands are blocked by a `PreToolUse` hook. Commit with
  `jj commit -m '...'`; after `jj commit` the working copy is already
  a fresh empty change, so do not run `jj new` afterward. Advance the
  bookmark after each commit with
  `jj bookmark move feat/geblang-literate --to @-`. Never push.
- **Run the Markdown linters on every document you write**, rather
  than relying on a hook to run them: whether one fires depends on
  the harness configuration, but `markdownlint-cli2` binds through
  `scripts/pre-push.sh` and Vale through `.vale.ini` regardless. Vale
  at error level rejects spaced em dashes, the Latin abbreviation for
  `for example`, the capitalised spelling of `Cslib`, the clipped
  form of `repository`, and colloquialisms. Its project vocabulary is
  `styles/config/vocabularies/GebMathlib/accept.txt`, one term per
  line; add a genuinely recurring technical term there rather than
  contorting prose, and reword a one-off informal word instead.
  Identifiers inside backticks are outside Vale's scope, so write
  `GebLang` in backticks in prose. The check is
  `vale --minAlertLevel=error <file>` and
  `markdownlint-cli2 '**/*.md'`.
- **The script self-tests stage synthetic trees.** Read
  `scripts/tests/test-lint-imports.sh` and
  `scripts/tests/test-extract-pr.sh` before writing a new case:
  the first builds a temporary tree with `setup_empty`, runs the
  linter from inside it, and asserts on exit code plus an expected
  fragment of the output; the second writes fixture files under a
  temporary
  working directory and asserts on the extracted file's contents.
  Neither linter resolves its own repository root, so both operate on
  the working directory; keep that property when adding
  `scripts/check-transitive-imports.sh`, whose self-test depends on
  it.
- **Build costs.** `lake build GebLang` is cheap. The first
  `lake build :literateHtml` compiles Verso's literate executables
  from source and takes minutes. This plan changes no Lean source, so
  only `scripts/pre-push.sh` rebuilds anything.
- **Foreground `sleep` is blocked** for executors. Poll with
  `curl --retry` rather than sleeping, and clean up a served site with
  `pkill -f verso-serve`.
- **Verification before completion.** A task is complete when its
  commands have been run and their output read. Report the output; do
  not infer a pass.

## File structure

Created by this plan:

- `scripts/check-transitive-imports.sh` (the closure check).
- `scripts/tests/test-check-transitive-imports.sh` (its self-test).

Modified by this plan: `scripts/extract-pr.sh`,
`scripts/tests/test-extract-pr.sh`, `scripts/lint-imports.sh`,
`scripts/tests/test-lint-imports.sh`, `scripts/pre-push.sh`,
`.github/workflows/ci.yml`, `docs/rules/upstream-eligible.md`,
`docs/rules/lean-coding.md`, `docs/rules/ci-and-workflow.md`,
`docs/index.md`, `docs/process.md`, `README.md`, `CONTRIBUTING.md`,
`AGENTS.md`, `GebMeta.lean`, `TODO.md`.

## Commit ordering

The order of the tasks below is load-bearing, per the spec's
§ Import rules: the extraction and lint-mechanism commits precede any
commit that widens an allowed-import list, so the floodgate invariant
holds at every commit rather than only at the branch tip.

1. Task 1: extraction handles every prefix the widened lists will
   permit.
2. Task 2: the transitive check bounds the closures the widened lists
   will open.
3. Task 3: the lint mechanism and the two new subtree entries.
4. Task 4: the widening itself, with its rationale in
   `docs/process.md`.
5. Task 5, then Task 6: the rule documents and the enumeration sweep,
   which describe the state the first four tasks reach.

Each of the three standing `TODO.md` entries this workstream resolves
is removed in the commit that resolves it: the extraction
`meta import` gap in Task 1, the Rule 2 comment-tail exemption in
Task 3, and the `Geb/Cslib/` imports of `Geb.Mathlib.*` in Task 4.

## Task 1: extend `scripts/extract-pr.sh`

**Files:**

- Modify: `scripts/extract-pr.sh` (rewritten below in full)
- Modify: `scripts/tests/test-extract-pr.sh`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: the `GebLang/` and `GebTests/Lang/` sources created by
  plan 1.
- Produces: `bash scripts/extract-pr.sh <src> <fork>` accepting the
  two new source roots; the track vocabulary (`mathlib-track`,
  `Cslib-track`) that Task 2's check and Task 5's rule documents use.

- [ ] **Step 1: replace `scripts/extract-pr.sh`**

The rewrite touches the header, the arm table and the copy step, so
write the file whole:

```bash
#!/usr/bin/env bash
#
# scripts/extract-pr.sh
#
# Path 1 PR extraction. Given an upstream-eligible source path under
# `Geb/Mathlib/`, `GebTests/Mathlib/`, `Geb/Cslib/`, `GebTests/Cslib/`,
# `GebLang/`, or `GebTests/Lang/`, and a target upstream-fork worktree
# path, copy the file to its upstream destination, rewriting the
# repository-internal module prefixes in import lines and converting
# Verso role markup in everything else.
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

src="$1"
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

# Verso role markup, applied off import lines: `{role}`x`` becomes
# `` `x` ``. `doc.verso` is set for the GebLang library alone, so an
# unconverted role would render as literal braces upstream. The
# pattern requires a brace-delimited identifier followed immediately
# by a backtick, which is rare outside a role: an implicit binder
# abutting a syntax quotation would match. The arms for the four
# `Geb`/`GebTests` subtrees run it too, their sources carrying
# Markdown docstrings where the pattern has nothing to match.
role_strip='s/\{[A-Za-z][A-Za-z0-9_]*[^}]*\}`/`/g'

# module_file <Module.Name>: the repository path of a module, whose
# name maps onto directories (`GebLang.Foo.Bar` is
# `GebLang/Foo/Bar.lean`).
module_file() {
  echo "${1//./\/}.lean"
}

# track_of <file>: prints `cslib` when the repository-internal import
# closure of <file>, followed through its `GebLang.` and
# `GebTests.Lang.` imports, carries any `Cslib.*` import; prints
# `mathlib` otherwise. The worklist is carried in space-separated
# strings rather than an associative array, which bash 3.2 (the system
# bash on macOS) does not provide; repository paths contain no spaces.
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
    rewrites='Geb.Mathlib. Mathlib.
GebLang. Mathlib.'
    ;;
  GebTests/Mathlib/*)
    # Unconditional in the same way as the arm above, and with the same
    # consequence for the test parallel of a core- or Batteries-targeted
    # module; this mapping waits on the same TODO.md item's outcome.
    dst_rel="MathlibTest/${src#GebTests/Mathlib/}"
    rewrites='Geb.Mathlib. Mathlib.
GebTests.Mathlib. MathlibTest.
GebLang. Mathlib.'
    ;;
  Geb/Cslib/*)
    dst_rel="Cslib/${src#Geb/Cslib/}"
    rewrites='Geb.Cslib. Cslib.
Geb.Mathlib. Mathlib.
GebLang. @src'
    ;;
  GebTests/Cslib/*)
    dst_rel="CslibTests/${src#GebTests/Cslib/}"
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
    rewrites='GebLang. @src'
    ;;
  GebTests/Lang/*)
    case "$(track_of "$src")" in
      cslib) dst_rel="CslibTests/${src#GebTests/Lang/}" ;;
      *)     dst_rel="MathlibTest/${src#GebTests/Lang/}" ;;
    esac
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

# Copy, rewriting each import line's module path by the arm's table and
# converting Verso roles elsewhere. The rewrite is anchored to the
# import keyword and applied to the module path alone, rather than by a
# within-line `\b` word boundary, which is non-portable (GNU sed only;
# not BSD or macOS, the same constraint block-mutating-git.sh
# documents). Anchoring also rules out matching a prefix embedded in a
# longer identifier, and confines the rewrite to the module path, so a
# prefix named in an import line's trailing comment survives as prose.
{
  while IFS= read -r line || [ -n "$line" ]; do
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
      printf '%s%s%s\n' "$kw" "$mod" "$rest"
    else
      printf '%s\n' "$line"
    fi
  done < "$src"
} | sed -E "/^${import_kw_re}/!${role_strip}" > "$dst"

echo "extract-pr.sh: $src -> $dst"
```

- [ ] **Step 2: check the arms reject an unknown root**

Run:

```bash
mkdir -p /tmp/extract-check/fork
bash scripts/extract-pr.sh Geb/Internal/ConcreteSyntax.lean /tmp/extract-check/fork
echo "exit=$?"
```

Expected: the usage error naming the six accepted roots, and
`exit=1`. If `Geb/Internal/ConcreteSyntax.lean` no longer exists,
name any file under `Geb/Internal/`.

- [ ] **Step 3: add the self-test cases**

Append to `scripts/tests/test-extract-pr.sh`, before the closing
`if [ "$failed" -ne 0 ]` block. The fixtures build a small tree with
both tracks in it, so the later cases reuse the earlier modules.

```bash
# A mathlib-track GebLang module: its closure reaches no Cslib.*, so
# it ships under Mathlib/ and importers rewrite it to `Mathlib.`.
mkdir -p GebLang/Foo fork4
cat > GebLang/Foo/Base.lean <<'EOF'
module
import Mathlib.Tactic
EOF
cat > GebLang/Foo/Bar.lean <<'EOF'
module
public import GebLang.Foo.Base

/-- Anchors {name}`Nat` in a docstring. -/
EOF
bash "$SCRIPT" GebLang/Foo/Bar.lean fork4 >/dev/null
out=fork4/Mathlib/Foo/Bar.lean
exists "mathlib-track GebLang -> Mathlib path" "$out"
has   "mathlib-track sibling rewritten" "public import Mathlib.Foo.Base" "$out"
lacks "Verso role markup removed" '{name}' "$out"
has   "code span survives the conversion" '`Nat`' "$out"

# A Cslib-track GebLang module importing a mathlib-track sibling: the
# sibling is rewritten by its own track, not by the destination.
mkdir -p GebLang/Cs fork5
cat > GebLang/Cs/Deep.lean <<'EOF'
module
import Cslib.Init
import Cslib.Foundations.Thing
EOF
cat > GebLang/Cs/Top.lean <<'EOF'
module
import Cslib.Init
public import GebLang.Cs.Deep
meta import GebLang.Foo.Base
EOF
bash "$SCRIPT" GebLang/Cs/Top.lean fork5 >/dev/null
out=fork5/Cslib/Cs/Top.lean
exists "cslib-track GebLang -> Cslib path" "$out"
has   "cslib-track sibling rewritten to Cslib" "public import Cslib.Cs.Deep" "$out"
has   "mathlib-track sibling keeps its own track" "meta import Mathlib.Foo.Base" "$out"
has   "foreign cslib import preserved" "import Cslib.Init" "$out"

# A mathlib-track GebTests/Lang module: subject and sibling each
# rewrite into the mathlib destination's source and test trees.
mkdir -p GebTests/Lang fork6
cat > GebTests/Lang/Sib.lean <<'EOF'
module
import GebLang.Foo.Base
EOF
cat > GebTests/Lang/Main.lean <<'EOF'
module
public import GebLang.Foo.Base
import GebTests.Lang.Sib
EOF
bash "$SCRIPT" GebTests/Lang/Main.lean fork6 >/dev/null
out=fork6/MathlibTest/Main.lean
exists "mathlib-track GebTests/Lang -> MathlibTest path" "$out"
has   "GebLang subject rewritten" "public import Mathlib.Foo.Base" "$out"
has   "test sibling rewritten to MathlibTest" "import MathlibTest.Sib" "$out"

# A Cslib-track GebTests/Lang module: the sibling ships to the Cslib
# test tree.
mkdir -p fork7
cat > GebTests/Lang/CsSib.lean <<'EOF'
module
import Cslib.Init
import GebLang.Cs.Deep
EOF
cat > GebTests/Lang/CsMain.lean <<'EOF'
module
import Cslib.Init
import GebTests.Lang.CsSib
EOF
bash "$SCRIPT" GebTests/Lang/CsMain.lean fork7 >/dev/null
out=fork7/CslibTests/CsMain.lean
exists "cslib-track GebTests/Lang -> CslibTests path" "$out"
has   "cslib test sibling rewritten to CslibTests" "import CslibTests.CsSib" "$out"

# The widened Mathlib arms rewrite GebLang. and the test self-prefix.
mkdir -p fork8
cat > Geb/Mathlib/Foo/Wide.lean <<'EOF'
module
import GebLang.Foo.Base
public meta import Geb.Mathlib.Other
EOF
bash "$SCRIPT" Geb/Mathlib/Foo/Wide.lean fork8 >/dev/null
out=fork8/Mathlib/Foo/Wide.lean
has   "Geb/Mathlib rewrites GebLang." "import Mathlib.Foo.Base" "$out"
has   "meta import form rewritten" "public meta import Mathlib.Other" "$out"

mkdir -p fork9
cat > GebTests/Mathlib/Wide.lean <<'EOF'
module
import GebLang.Foo.Base
public meta import Geb.Mathlib.X
import GebTests.Mathlib.Helper
EOF
bash "$SCRIPT" GebTests/Mathlib/Wide.lean fork9 >/dev/null
out=fork9/MathlibTest/Wide.lean
has   "GebTests/Mathlib rewrites GebLang." "import Mathlib.Foo.Base" "$out"
has   "GebTests/Mathlib rewrites its test self-prefix" \
      "import MathlibTest.Helper" "$out"

# The widened Cslib arms rewrite Geb.Mathlib., GebLang. by track, and
# the test self-prefix.
mkdir -p fork10
cat > Geb/Cslib/Wide.lean <<'EOF'
module
import Cslib.Init
import Geb.Mathlib.Thing
import GebLang.Foo.Base
import GebLang.Cs.Deep
EOF
bash "$SCRIPT" Geb/Cslib/Wide.lean fork10 >/dev/null
out=fork10/Cslib/Wide.lean
has   "Geb/Cslib rewrites Geb.Mathlib." "import Mathlib.Thing" "$out"
has   "Geb/Cslib rewrites a mathlib-track GebLang import" \
      "import Mathlib.Foo.Base" "$out"
has   "Geb/Cslib rewrites a cslib-track GebLang import" \
      "import Cslib.Cs.Deep" "$out"

mkdir -p GebTests/Cslib fork11
cat > GebTests/Cslib/Wide.lean <<'EOF'
module
import Cslib.Init
import Geb.Mathlib.Thing
import GebTests.Cslib.Helper
EOF
bash "$SCRIPT" GebTests/Cslib/Wide.lean fork11 >/dev/null
out=fork11/CslibTests/Wide.lean
has   "GebTests/Cslib rewrites Geb.Mathlib." "import Mathlib.Thing" "$out"
has   "GebTests/Cslib rewrites its test self-prefix" \
      "import CslibTests.Helper" "$out"
```

The conversion is stated by the pair of assertions on
`fork4/Mathlib/Foo/Bar.lean`: `lacks` on the role markup, `has` on the
code span it leaves behind. The fixture directories `Geb/Mathlib/Foo`,
`GebTests/Mathlib` and `Geb/Cslib` already exist in the temporary tree
from the file's earlier cases, which is why only the new ones are
created above; add `mkdir -p` for any that a reordering leaves absent.

- [ ] **Step 4: run the extraction self-test**

Run: `bash scripts/tests/test-extract-pr.sh`

Expected: `test-extract-pr.sh: all checks passed`, exit 0. A `FAIL`
line names the assertion and the file it read.

- [ ] **Step 5: exercise the tool against the real placeholder module**

Run:

```bash
rm -rf /tmp/geblang-extract && mkdir -p /tmp/geblang-extract
bash scripts/extract-pr.sh GebLang/Basic.lean /tmp/geblang-extract
cat /tmp/geblang-extract/Mathlib/Basic.lean
```

Expected: the destination is `Mathlib/Basic.lean` (the placeholder's
closure reaches no `Cslib.*`), and the printed file carries
`` `gebLangAnchor` `` and `` `Nat` `` as bare code spans with no
`{name}` markup. Nothing ships; inspect the output and discard it.

- [ ] **Step 6: remove the resolved `TODO.md` entry**

Delete the whole `TODO.md` § Triggers entry beginning

```markdown
- **`scripts/extract-pr.sh` does not rewrite `meta import` lines**:
```

through the end of its `Trigger:` sentence. The rewrite now covers all
four import forms, so the entry is resolved. Confirm the two lines it
names, in `GebTests/Mathlib/Data/UnionFind/OfEdges.lean` and
`GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, now
extract with their prefixes rewritten:

```bash
rm -rf /tmp/meta-extract && mkdir -p /tmp/meta-extract
bash scripts/extract-pr.sh GebTests/Mathlib/Data/UnionFind/OfEdges.lean /tmp/meta-extract
grep 'meta import' /tmp/meta-extract/MathlibTest/Data/UnionFind/OfEdges.lean
```

Expected: the `meta import` line names `Mathlib.`, not `Geb.Mathlib.`.

- [ ] **Step 7: commit**

```bash
jj commit -m 'feat(scripts): extract GebLang by import-closure track'
jj bookmark move feat/geblang-literate --to @-
```

## Task 2: add `scripts/check-transitive-imports.sh`

**Files:**

- Create: `scripts/check-transitive-imports.sh`
- Create: `scripts/tests/test-check-transitive-imports.sh`
- Modify: `scripts/pre-push.sh`
- Modify: `.github/workflows/ci.yml`
- Modify: `docs/rules/ci-and-workflow.md`

**Interfaces:**

- Consumes: the track definition of Task 1 (a module is Cslib-track
  when its repository-internal closure reaches any `Cslib.*` import).
- Produces: `bash scripts/check-transitive-imports.sh`, exit 0 on a
  clean tree; the guarantee Task 1's `Geb/Mathlib/` and
  `GebTests/Mathlib/` arms rely on when rewriting `GebLang.`
  unconditionally, and which Task 4's widening depends on.

- [ ] **Step 1: write the checker**

Create `scripts/check-transitive-imports.sh`:

```bash
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
```

- [ ] **Step 2: make the checker executable and run it**

Run:

```bash
chmod +x scripts/check-transitive-imports.sh
bash scripts/check-transitive-imports.sh
```

Expected: `check-transitive-imports.sh: clean (N file(s) checked)`,
exit 0, with `N` the number of files in the two mathlib-track roots
plus `GebTests/Lang/`.

- [ ] **Step 3: write the self-test**

Create `scripts/tests/test-check-transitive-imports.sh`:

```bash
#!/usr/bin/env bash
#
# scripts/tests/test-check-transitive-imports.sh
#
# Smoke test for scripts/check-transitive-imports.sh. Stages synthetic
# Geb/, GebTests/ and GebLang/ trees under a temp directory and runs
# the checker against a clean state and against induced failures from
# both root kinds and from the second pass.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
checker="$repo_root/scripts/check-transitive-imports.sh"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

failed=0
checked=0

setup_empty() {
  rm -rf "$test_dir"
  mkdir -p "$test_dir/Geb/Mathlib" "$test_dir/Geb/Cslib" \
           "$test_dir/GebTests/Mathlib" "$test_dir/GebTests/Cslib" \
           "$test_dir/GebTests/Lang" "$test_dir/GebLang"
}

assert_case() {
  local name="$1" expected_exit="$2" expected_substr="$3"
  checked=$((checked + 1))
  local output exit_code
  output="$(cd "$test_dir" && bash "$checker" 2>&1)"
  exit_code=$?
  if [[ "$exit_code" -ne "$expected_exit" ]]; then
    echo "FAIL: $name: expected exit $expected_exit, got $exit_code" >&2
    echo "  output: $output" >&2
    failed=$((failed + 1))
    return
  fi
  if [[ -n "$expected_substr" ]] && ! grep -qF "$expected_substr" <<<"$output"; then
    echo "FAIL: $name: expected substring '$expected_substr' not in output" >&2
    echo "  output: $output" >&2
    failed=$((failed + 1))
    return
  fi
  echo "PASS: $name"
}

# A mathlib-track GebLang dependency: clean.
setup_empty
printf 'module\nimport Mathlib.Tactic\n' > "$test_dir/GebLang/Base.lean"
printf 'module\nimport GebLang.Base\n' > "$test_dir/Geb/Mathlib/Foo.lean"
assert_case "mathlib-track GebLang dependency" 0 "clean"

# A Geb/Mathlib/ root whose GebLang dependency reaches Cslib.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebLang/Cs.lean"
printf 'module\nimport GebLang.Cs\n' > "$test_dir/Geb/Mathlib/Foo.lean"
assert_case "Geb/Mathlib root reaching Cslib" 1 \
  "Geb/Mathlib/Foo.lean: its import closure reaches Cslib.*"

# The same failure from the test mirror's root kind, and through one
# more hop, so the walk's transitivity is exercised.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebLang/Cs.lean"
printf 'module\nimport GebLang.Cs\n' > "$test_dir/GebLang/Mid.lean"
printf 'module\nimport GebLang.Mid\n' > "$test_dir/GebTests/Mathlib/Foo.lean"
assert_case "GebTests/Mathlib root reaching Cslib transitively" 1 \
  "GebTests/Mathlib/Foo.lean: its import closure reaches Cslib.*"

# Pass 2: a Cslib-track test importing a mathlib-track sibling.
setup_empty
printf 'module\nimport Mathlib.Tactic\n' > "$test_dir/GebLang/Base.lean"
printf 'module\nimport GebLang.Base\n' > "$test_dir/GebTests/Lang/MSib.lean"
printf 'module\nimport Cslib.Init\nimport GebTests.Lang.MSib\n' \
  > "$test_dir/GebTests/Lang/CsMain.lean"
assert_case "cslib-track test importing a mathlib-track sibling" 1 \
  "Cslib-track test imports the mathlib-track sibling GebTests.Lang.MSib"

# Pass 2: a Cslib-track test importing a Cslib-track sibling is clean.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebTests/Lang/CsSib.lean"
printf 'module\nimport Cslib.Init\nimport GebTests.Lang.CsSib\n' \
  > "$test_dir/GebTests/Lang/CsMain.lean"
assert_case "cslib-track test importing a cslib-track sibling" 0 "clean"

echo ""
echo "test-check-transitive-imports.sh: $checked case(s) checked, $failed failure(s)"
exit "$failed"
```

- [ ] **Step 4: run the self-test**

Run: `bash scripts/tests/test-check-transitive-imports.sh`

Expected: five `PASS` lines and `0 failure(s)`, exit 0.

- [ ] **Step 5: wire the check into the pre-push checklist**

In `scripts/pre-push.sh`, after the existing
`scripts/tests/test-lint-imports.sh` step, add:

```bash
step "scripts/check-transitive-imports.sh"
bash scripts/check-transitive-imports.sh

step "scripts/tests/test-check-transitive-imports.sh"
bash scripts/tests/test-check-transitive-imports.sh
```

- [ ] **Step 6: wire the check into CI**

In `.github/workflows/ci.yml`, in the `floodgate_imports` job, add
after the `scripts/tests/test-lint-imports.sh` step:

```yaml
      - name: scripts/check-transitive-imports.sh
        run: bash scripts/check-transitive-imports.sh
      - name: scripts/tests/test-check-transitive-imports.sh
        run: bash scripts/tests/test-check-transitive-imports.sh
```

- [ ] **Step 7: record the check in the workflow rules**

In `docs/rules/ci-and-workflow.md` § Pre-push checklist, extend the
script self-tests list. The bullet

```markdown
- `scripts/lint-imports.sh` and `scripts/tests/test-lint-imports.sh`.
```

becomes

```markdown
- `scripts/lint-imports.sh` and `scripts/tests/test-lint-imports.sh`.
- `scripts/check-transitive-imports.sh` and
  `scripts/tests/test-check-transitive-imports.sh`. The first bounds
  each module's direct imports, the second the closure: a
  `Geb/Mathlib/` or `GebTests/Mathlib/` module whose `GebLang`
  dependencies reach `Cslib.*` is Cslib-track and belongs under the
  Cslib subtree.
```

- [ ] **Step 8: run both checks and the Markdown checks**

Run:

```bash
bash scripts/check-transitive-imports.sh
bash scripts/tests/test-check-transitive-imports.sh
markdownlint-cli2 '**/*.md'
```

Expected: exit 0 from each.

- [ ] **Step 9: commit**

```bash
jj commit -m 'feat(scripts): check import closures for track misplacement'
jj bookmark move feat/geblang-literate --to @-
```

## Task 3: the `scripts/lint-imports.sh` mechanism and the new entries

**Files:**

- Modify: `scripts/lint-imports.sh`
- Modify: `scripts/tests/test-lint-imports.sh`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: nothing from Tasks 1 and 2 at the source level; it lands
  after them so that no permitted import outruns the tooling.
- Produces: the `GebLang/` and `GebTests/Lang/` subtree entries; the
  conditional required-init mechanism (`?`-prefixed init module) and
  the narrowed Rule 2 exemption, both of which Task 4 relies on.

- [ ] **Step 1: make the required-init check conditional**

In `scripts/lint-imports.sh`, replace the Rule 1b block (lines 141 to
151) with:

```bash
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
```

Declare the three new locals in the function's existing `local`
declaration line (`local f line canonical ok ln lp prefix_re`), which
becomes:

```bash
  local f line canonical ok ln lp prefix_re
  local init_mod init_ns init_needed
```

- [ ] **Step 2: narrow the Rule 2 exemption to the import path**

Replace the Rule 2 block (lines 153 to 171) with:

```bash
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
```

The message changes from `outside ^import line` to
`outside an import path`, since a trailing comment on an import line
is now a violation and the old wording would misdescribe it.

- [ ] **Step 3: add the two new subtree entries**

After the four existing `check_subtree` calls, add:

```bash
# GebLang sits at the bottom of the dependency order: its modules
# import no other library of this repository. Its test mirror adds its
# own siblings. Both take the conditional Cslib.Init requirement,
# their modules being mathlib-track or Cslib-track per module rather
# than per subtree.
check_subtree "GebLang." -- "?Cslib.Init" GebLang \
  -- "Mathlib." "Batteries." "Cslib." "GebLang."
check_subtree "GebLang." "GebTests.Lang." -- "?Cslib.Init" GebTests/Lang \
  -- "Mathlib." "Batteries." "Cslib." "GebLang." "GebTests.Lang."
```

The find roots are the directories, so the `GebLang.lean` umbrella
(which imports `GebMeta`) and the `GebTests/Lang.lean` index sit
outside the check, as `Geb/Mathlib.lean` and `GebTests/Mathlib.lean`
already do.

- [ ] **Step 4: extend the header comment**

In the header's subtree table, add the two new rows after the existing
four:

```bash
#   GebLang/           →  Mathlib.*, Batteries.*, Cslib.*, GebLang.*
#                         (plus `import Cslib.Init` when the file
#                          imports any Cslib.* module)
#   GebTests/Lang/     →  Mathlib.*, Batteries.*, Cslib.*, GebLang.*,
#                         GebTests.Lang.* (same conditional init rule)
```

and add, after the `Batteries.*` rationale paragraph:

```bash
# GebLang holds the Geb language's core data structures, at the bottom
# of the dependency order: its modules import no other library of this
# repository, and the subtrees above import them once their allowed
# lists admit the prefix (the commit after this one). Each module is
# retargeted by its own import closure — mathlib-track when the
# closure reaches no Cslib.*, Cslib-track otherwise — so the
# Cslib.Init requirement is conditional here rather than per subtree,
# and scripts/check-transitive-imports.sh checks the closures that
# scripts/extract-pr.sh reads to pick a destination.
```

Three further passages of the header state the superseded whole-line
exemption or the unconditional init rule, and change with the
mechanism.

The opening paragraph, which reads

```bash
# Each upstream-eligible subtree has an allowed-import list and a
# self-prefix that must not appear outside import lines. Files in
# Geb/Cslib/ and GebTests/Cslib/ additionally must import `Cslib.Init`
# per CSLib's `checkInitImports` requirement.
```

becomes

```bash
# Each upstream-eligible subtree has an allowed-import list and one or
# more self-prefixes that must not appear outside the module path of
# an import line. Files in Geb/Cslib/ and GebTests/Cslib/ must import
# `Cslib.Init` per Cslib's `checkInitImports` requirement, and files
# in GebLang/ and GebTests/Lang/ must when they import any Cslib.*
# module.
```

The `check_subtree` usage comment, which reads

```bash
# (each such prefix must not appear outside import lines), the second
```

becomes

```bash
# (each such prefix must not appear outside an import line's module
# path), the second
```

And the Rule 2 sentence, which reads

```bash
# `public import` lines are recognised the same as plain `import`
# (the same allowed-prefix and forbidden-umbrella rules apply,
# and they count as import lines for the no-prefix-leakage rule).
```

becomes

```bash
# `public import` lines are recognised the same as plain `import`
# (the same allowed-prefix and forbidden-umbrella rules apply, and
# their module path is exempt from the no-prefix-leakage rule).
```

- [ ] **Step 5: update the self-test's message assertions**

Run:

```bash
sed -i 's/outside \^import line/outside an import path/g' \
  scripts/tests/test-lint-imports.sh
grep -c 'outside an import path' scripts/tests/test-lint-imports.sh
```

Expected: the count matches the number of leakage assertions in the
file (cases 8, 9, 22, 23, 26, 27, 32 and 36 at the time of writing).
On macOS, `sed -i ''` takes the empty backup suffix.

Case 36 asserted that a comment containing the word `import` is not an
import line. Its fixture stays valid under the narrowed exemption, the
comment not starting the line; retitle it so the assertion it makes is
the one the rule now states:

```bash
assert_case "a self-prefix in a comment is not an import path" 1 \
  "'Geb.Mathlib.' outside an import path"
```

- [ ] **Step 6: add the new self-test cases**

Extend `setup_empty` so the two new roots exist:

```bash
setup_empty() {
  rm -rf "$test_dir"
  mkdir -p "$test_dir/Geb/Mathlib" "$test_dir/Geb/Cslib" \
           "$test_dir/GebTests/Mathlib" "$test_dir/GebTests/Cslib" \
           "$test_dir/GebLang" "$test_dir/GebTests/Lang"
}
```

Append these cases before the closing `echo`/`exit` lines:

```bash
# Case 37: a clean GebLang file with no Cslib import needs no init.
setup_empty
cat > "$test_dir/GebLang/Foo.lean" <<'EOF'
module

import Mathlib.Algebra.Group.Basic
import Batteries.Data.UnionFind
import GebLang.Bar

def foo : Nat := 0
EOF
assert_case "GebLang clean without Cslib" 0 "clean (1 file(s) checked)"

# Case 38: a GebLang file importing Cslib.* must import Cslib.Init.
setup_empty
cat > "$test_dir/GebLang/NoInit.lean" <<'EOF'
module

import Cslib.Foundations.Thing
EOF
assert_case "GebLang conditional init triggered" 1 \
  "missing required 'import Cslib.Init'"

# Case 39: the trigger fires on a `meta import` of a Cslib module,
# which is the form the unconditional rule's satisfying import
# excludes.
setup_empty
cat > "$test_dir/GebLang/MetaOnly.lean" <<'EOF'
module

meta import Cslib.Foundations.Thing
EOF
assert_case "GebLang conditional init triggered by a meta import" 1 \
  "missing required 'import Cslib.Init'"

# Case 40: an ordinary import of Cslib.Init satisfies the triggered
# requirement.
setup_empty
cat > "$test_dir/GebLang/MetaCslib.lean" <<'EOF'
module

import Cslib.Init
meta import Cslib.Foundations.Thing
EOF
assert_case "GebLang conditional init satisfied" 0 "clean (1 file(s) checked)"

# Case 41: a GebLang file importing Geb.
setup_empty
cat > "$test_dir/GebLang/Bad.lean" <<'EOF'
module

import Geb
EOF
assert_case "GebLang forbidding a Geb import" 1 \
  "forbidden import 'import Geb'"

# Case 42: GebLang self-prefix leakage.
setup_empty
cat > "$test_dir/GebLang/Leak.lean" <<'EOF'
module

import GebLang.Bar

def GebLang.foo : Nat := 0
EOF
assert_case "GebLang self-prefix leakage" 1 \
  "'GebLang.' outside an import path"

# Case 43: GebTests/Lang sibling imports are allowed.
setup_empty
cat > "$test_dir/GebTests/Lang/Index.lean" <<'EOF'
module

public import GebLang.Foo
public meta import GebLang.Foo
import GebTests.Lang.Sub
EOF
assert_case "GebTests/Lang sibling import" 0 "clean (1 file(s) checked)"

# Case 44: GebTests/Lang test self-prefix leakage.
setup_empty
cat > "$test_dir/GebTests/Lang/Leak.lean" <<'EOF'
module

import GebTests.Lang.Sub

def GebTests.Lang.foo : Nat := 0
EOF
assert_case "GebTests/Lang test self-prefix leakage" 1 \
  "'GebTests.Lang.' outside an import path"

# Case 45: a leakage prefix in an import line's trailing comment.
setup_empty
cat > "$test_dir/GebTests/Lang/CommentTail.lean" <<'EOF'
module

import GebTests.Lang.Sub  -- see also GebTests.Lang.Other
EOF
assert_case "leakage prefix in an import line's comment tail" 1 \
  "'GebTests.Lang.' outside an import path"
```

Case 45 is the narrowed exemption of Step 2; before it, the whole
import line was exempt and this fixture passed clean.

- [ ] **Step 7: run the linter and its self-test**

Run:

```bash
bash scripts/lint-imports.sh
bash scripts/tests/test-lint-imports.sh
```

Expected: the linter reports `clean` with a file count that now
includes `GebLang/Basic.lean` and `GebTests/Lang/Basic.lean`, and the
self-test reports `0 failure(s)`.

If the linter reports a violation in the two files plan 1 created,
fix the source rather than the rule: the spec's import rules bind
them.

- [ ] **Step 8: remove the resolved `TODO.md` entry**

Delete the whole `TODO.md` § Triggers entry beginning

```markdown
- **Check the leakage prefix in an import line's comment tail**:
```

through the end of its `Trigger:` sentence. Step 2 narrowed the
exemption, which is what the entry asked for.

- [ ] **Step 9: commit**

```bash
jj commit -m 'feat(scripts): lint the GebLang subtrees and narrow rule 2'
jj bookmark move feat/geblang-literate --to @-
```

## Task 4: widen the four existing allowed-import lists

**Files:**

- Modify: `scripts/lint-imports.sh`
- Modify: `scripts/tests/test-lint-imports.sh`
- Modify: `docs/process.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: the extraction rewrites of Task 1, the closure check of
  Task 2, and the lint mechanism of Task 3. Every import this task
  permits is already shippable because of them; that is why this task
  is fourth.
- Produces: the widened lists the rule documents of Task 5 describe.

- [ ] **Step 1: widen the four `check_subtree` calls**

Replace the four existing calls in `scripts/lint-imports.sh` with:

```bash
check_subtree "Geb.Mathlib." "GebLang." -- "" Geb/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib." "GebLang."
check_subtree "Geb.Mathlib." "GebTests.Mathlib." "GebLang." -- "" GebTests/Mathlib \
  -- "Mathlib." "Batteries." "Geb.Mathlib." "GebTests.Mathlib." "GebLang."
check_subtree "Geb.Cslib." "Geb.Mathlib." "GebLang." -- "Cslib.Init" Geb/Cslib \
  -- "Mathlib." "Batteries." "Cslib." "Geb.Cslib." "Geb.Mathlib." "GebLang."
check_subtree "Geb.Cslib." "GebTests.Cslib." "Geb.Mathlib." "GebLang." -- "Cslib.Init" GebTests/Cslib \
  -- "Mathlib." "Batteries." "Cslib." "Geb.Cslib." "GebTests.Cslib." "Geb.Mathlib." "GebLang."
```

Three widened prefixes across the four lists, with their leakage
consequences: `GebLang.*` joins all four allowed lists and all four
leakage-prefix lists; `Geb.Mathlib.*` and `Batteries.*` join the two
Cslib lists, and `Geb.Mathlib.` joins the two Cslib leakage-prefix
lists, a qualified reference in an extracted body otherwise dangling
upstream.

- [ ] **Step 2: update the header table**

The four existing rows of the header's table become:

```bash
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
```

and the `Batteries.*` rationale paragraph, whose whole text reads

```bash
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
```

becomes, re-flowed because the first sentence ends mid-line

```bash
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
```

Add after it:

```bash
# `Geb.Mathlib.*` is admitted to the Cslib subtrees because Cslib
# depends on mathlib: a Cslib-destined module may depend on
# mathlib-destined content, shipped in dependency order, after the
# mathlib PR merges and Cslib's mathlib pin advances. The reverse
# direction stays barred: mathlib does not depend on Cslib, so no
# ordering makes a Geb/Mathlib/ module's Cslib.* import extractable.
```

- [ ] **Step 3: invert the two self-test cases the widening falsifies**

In `scripts/tests/test-lint-imports.sh`, case 6 currently asserts that
a `Geb/Cslib/` file importing `Geb.Mathlib.Foo` fails. Replace it with:

```bash
# Case 6: Cslib file importing Geb.Mathlib (dependency-ordered).
setup_empty
cat > "$test_dir/Geb/Cslib/Dep.lean" <<'EOF'
module

import Cslib.Init
import Geb.Mathlib.Foo
EOF
assert_case "Cslib importing Geb.Mathlib" 0 "clean (1 file(s) checked)"
```

and case 29, which asserts that a `Geb/Cslib/` file importing
Batteries fails, with:

```bash
# Case 29: Geb/Cslib importing Batteries (Cslib depends on mathlib,
# which depends on Batteries).
setup_empty
cat > "$test_dir/Geb/Cslib/Batt.lean" <<'EOF'
module

import Cslib.Init
import Batteries.Data.UnionFind
EOF
assert_case "Geb/Cslib Batteries import" 0 "clean (1 file(s) checked)"
```

- [ ] **Step 4: add the widened lists' own cases**

Append:

```bash
# Case 46: GebLang.* is accepted in the source subtrees.
setup_empty
cat > "$test_dir/Geb/Mathlib/UsesLang.lean" <<'EOF'
module

import GebLang.Foo
EOF
cat > "$test_dir/Geb/Cslib/UsesLang.lean" <<'EOF'
module

import Cslib.Init
import GebLang.Foo
EOF
assert_case "GebLang import accepted in source subtrees" 0 \
  "clean (2 file(s) checked)"

# Case 47: GebLang.* is accepted in the test mirrors.
setup_empty
cat > "$test_dir/GebTests/Mathlib/UsesLang.lean" <<'EOF'
module

import GebLang.Foo
EOF
cat > "$test_dir/GebTests/Cslib/UsesLang.lean" <<'EOF'
module

import Cslib.Init
import Geb.Mathlib.Thing
import Batteries.Data.UnionFind
import GebLang.Foo
EOF
assert_case "GebLang import accepted in test mirrors" 0 \
  "clean (2 file(s) checked)"

# Case 48: the mathlib subtree still cannot import Cslib-destined
# content.
setup_empty
cat > "$test_dir/Geb/Mathlib/Bad.lean" <<'EOF'
module

import Geb.Cslib.Foo
EOF
assert_case "Geb/Mathlib forbidding Geb.Cslib import" 1 \
  "forbidden import 'import Geb.Cslib.Foo'"

# Case 49: GebLang. leakage in a Geb/Mathlib/ body.
setup_empty
cat > "$test_dir/Geb/Mathlib/LangLeak.lean" <<'EOF'
module

import GebLang.Foo

def GebLang.foo : Nat := 0
EOF
assert_case "GebLang leakage in Geb/Mathlib" 1 \
  "'GebLang.' outside an import path"

# Case 50: Geb.Mathlib. leakage in a Geb/Cslib/ body, which
# extraction would leave dangling upstream.
setup_empty
cat > "$test_dir/Geb/Cslib/MathlibLeak.lean" <<'EOF'
module

import Cslib.Init
import Geb.Mathlib.Foo

def Geb.Mathlib.foo : Nat := 0
EOF
assert_case "Geb.Mathlib leakage in Geb/Cslib" 1 \
  "'Geb.Mathlib.' outside an import path"

# Case 51: Geb.Mathlib. leakage in the GebTests/Cslib/ mirror.
setup_empty
cat > "$test_dir/GebTests/Cslib/MathlibLeak.lean" <<'EOF'
module

import Cslib.Init

def Geb.Mathlib.foo : Nat := 0
EOF
assert_case "Geb.Mathlib leakage in GebTests/Cslib" 1 \
  "'Geb.Mathlib.' outside an import path"

# Case 52: GebLang. leakage in the GebTests/Mathlib/ mirror.
setup_empty
cat > "$test_dir/GebTests/Mathlib/LangLeak.lean" <<'EOF'
module

import GebLang.Foo

def GebLang.foo : Nat := 0
EOF
assert_case "GebLang leakage in GebTests/Mathlib" 1 \
  "'GebLang.' outside an import path"

# Case 53: the test mirror still cannot import Cslib-destined content.
setup_empty
cat > "$test_dir/GebTests/Mathlib/BadCslib.lean" <<'EOF'
module

import Geb.Cslib.Foo
EOF
assert_case "GebTests/Mathlib forbidding Geb.Cslib import" 1 \
  "forbidden import 'import Geb.Cslib.Foo'"
```

Cases 52 and 53 are the mirror parallels the spec's § Verification
asks for beside cases 49 and 48: the mirror runs the same acceptance
and rejection cases as its source root.

- [ ] **Step 5: run the linter and both self-tests**

Run:

```bash
bash scripts/lint-imports.sh
bash scripts/tests/test-lint-imports.sh
bash scripts/check-transitive-imports.sh
bash scripts/tests/test-extract-pr.sh
```

Expected: exit 0 from each, and `0 failure(s)` from the lint
self-test.

- [ ] **Step 6: revise `docs/process.md` § Floodgate test**

Replace the section body, which currently reads

```markdown
At all times, the repo is ready to ship dependency-ordered PRs on
short notice with no source-code changes.
`scripts/lint-imports.sh` enforces the import-direction and
no-prefix-leakage rules. The test is what makes
"upstream-eligible" a binding property of `Geb/Mathlib/` and
`Geb/Cslib/` rather than an aspiration: at any moment, every
file in either subtree can be extracted to a PR upstream.
```

with

```markdown
At all times, the repository is ready to ship dependency-ordered PRs
on short notice with no source-code changes.
`scripts/lint-imports.sh` enforces the import-direction and
no-prefix-leakage rules, and
`scripts/check-transitive-imports.sh` enforces the closure rules the
direct-import lists cannot see. The test is what makes
"upstream-eligible" a binding property of `Geb/Mathlib/`,
`Geb/Cslib/` and `GebLang/` rather than an aspiration: at any
moment, every file in any of them can be extracted to a PR
upstream.

The three locations are not independent of one another. A `GebLang`
module is retargeted by its own import closure, mathlib-track when
the closure reaches no `Cslib.*` and Cslib-track otherwise, so
extraction is dependency-ordered through `GebLang` rather than
independent per subtree: a module's within-repository dependencies
ship first, each to the upstream its own closure selects.

Cross-track dependency is uniform policy in one direction.
Cslib-destined content may depend on mathlib-destined content,
shipping after its dependencies merge and Cslib's mathlib pin
advances, exactly as Cslib itself depends on mathlib. Three cadences
the project does not set stand between the two PRs, which is the cost
the floodgate test's "on short notice" weighs; the ordering is
nevertheless available, whereas the reverse is not. Mathlib-destined
content depends on no Cslib-destined content: mathlib does not depend
on Cslib, so no ordering makes such a PR extractable, and
`Geb/Mathlib/`'s allowed lists bar it directly while
`scripts/check-transitive-imports.sh` bars it through `GebLang`.
```

- [ ] **Step 7: extend `docs/process.md` § Two-track development**

The sentence

```markdown
Code is ported
into `Geb/Mathlib/` or `Geb/Cslib/` when it reaches upstream
quality, with dependents migrated via `jj rebase` after the
upstream PR is accepted.
```

becomes

```markdown
Code is ported
into `Geb/Mathlib/`, `Geb/Cslib/` or `GebLang/` when it reaches
upstream quality, with dependents migrated via `jj rebase` after the
upstream PR is accepted.
```

- [ ] **Step 8: remove the resolved `TODO.md` entry**

Delete the whole `TODO.md` § Triggers entry beginning

```markdown
- **Allowing `Geb/Cslib/` to import `Geb.Mathlib.*`**: the case for it is
```

through the end of its trailing `Trigger:` sentence, including the
nested change-set list. The decision is taken, its rationale is in
`docs/process.md` § Floodgate test, and the entry's own change set is
this task plus Tasks 1 and 5. The list's closing note, that
`Batteries.` is arguably missing from the `Geb/Cslib/` allowed list,
is resolved by Step 1 as well.

- [ ] **Step 9: run the Markdown checks and commit**

Run:

```bash
doctoc --update-only . && markdownlint-cli2 '**/*.md' && bash scripts/check-md-links.sh
```

Expected: exit 0 from each. Then:

```bash
jj commit -m 'feat(scripts): allow GebLang and cross-track imports'
jj bookmark move feat/geblang-literate --to @-
```

## Task 5: the rule documents

**Files:**

- Modify: `docs/rules/upstream-eligible.md`
- Modify: `docs/rules/lean-coding.md`
- Modify: `docs/index.md`
- Modify: `README.md`
- Modify: `CONTRIBUTING.md`
- Modify: `AGENTS.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: the mechanism of Tasks 1 to 4, which these documents
  describe.
- Produces: the binding statement of the rules the scripts enforce.
  Task 6 greps for anything this task misses.

- [ ] **Step 1: extend the `paths:` frontmatter and the applies-to line**

In `docs/rules/upstream-eligible.md`, the frontmatter becomes:

```yaml
---
paths:
  - "Geb/Mathlib.lean"
  - "Geb/Mathlib/**"
  - "GebTests/Mathlib.lean"
  - "GebTests/Mathlib/**"
  - "Geb/Cslib.lean"
  - "Geb/Cslib/**"
  - "GebTests/Cslib.lean"
  - "GebTests/Cslib/**"
  - "GebLang/**"
  - "GebTests/Lang.lean"
  - "GebTests/Lang/**"
---
```

`GebLang.lean` is excluded: the umbrella imports `GebMeta` to register
the axiom linter, so the content rules do not bind it. That is a
stated deviation from the umbrella-plus-directory shape of the
existing entries. The `GebTests/Lang.lean` index imports no `GebMeta`
and is included, following that shape.

The applies-to sentence

```markdown
Applies to anything under `Geb/Mathlib/`, `GebTests/Mathlib/`,
`Geb/Cslib/`, or `GebTests/Cslib/`.
```

becomes

```markdown
Applies to anything under `Geb/Mathlib/`, `GebTests/Mathlib/`,
`Geb/Cslib/`, `GebTests/Cslib/`, `GebLang/`, or `GebTests/Lang/`,
and to the `GebTests/Lang.lean` index. The `GebLang.lean` umbrella
is excluded: it imports `GebMeta` to register the axiom linter, so
the content rules do not bind it.
```

- [ ] **Step 2: extend § Two-track development**

The passage

```markdown
1. Port it into `Geb/Mathlib/Foo.lean` or `Geb/Cslib/Foo.lean`
   depending on the upstream target, satisfying the subtree
   import rules below. The two subtrees are the only destinations
   for ported content, but `Geb/Mathlib/` is not exclusively
   mathlib4-targeted: where the import rules below leave no
   alternative, a module there may instead target Lean core or
   Batteries, a destination open per `TODO.md` § Upstream
   destination of core- and Batteries-targeted content.
```

becomes

```markdown
1. Port it into `Geb/Mathlib/Foo.lean`, `Geb/Cslib/Foo.lean` or
   `GebLang/Foo.lean` depending on the upstream target, satisfying
   the subtree import rules below. `Geb/Mathlib/` is not exclusively
   mathlib4-targeted: where the import rules below leave no
   alternative, a module there may instead target Lean core or
   Batteries, a destination open per `TODO.md` § Upstream
   destination of core- and Batteries-targeted content. `GebLang/`
   is destination-open per module in a second sense: its modules
   carry the Geb language's core data structures and ship to mathlib
   or to Cslib according to each module's own import closure
   (§ Subtree import rules).
```

- [ ] **Step 3: revise § Floodgate test**

The section body

```markdown
At all times, the repo must be ready to ship dependency-ordered
PRs on short notice with no source-code changes. After any
non-trivial change, ask: "does this break extraction?" Each
upstream subtree's extractability is independent of the other
(the strict import rules below ensure this).
```

becomes

```markdown
At all times, the repository must be ready to ship
dependency-ordered PRs on short notice with no source-code changes.
After any non-trivial change, ask whether it breaks extraction.
Extraction is dependency-ordered through `GebLang/` rather than
independent between the subtrees: a module's within-repository
dependencies ship first, each retargeted by its own import closure,
mathlib-track when the closure reaches no `Cslib.*` and Cslib-track
otherwise. `scripts/lint-imports.sh` bounds each module's direct
imports and `scripts/check-transitive-imports.sh` bounds the
closures, so a `Geb/Mathlib/` module cannot acquire a Cslib-track
dependency unnoticed.
```

- [ ] **Step 4: revise the subtree import-rules section**

The table becomes:

```markdown
| Subtree | Allowed imports | Self-prefixes (no leakage) |
| --- | --- | --- |
| `Geb/Mathlib/` | `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Mathlib.`, `GebLang.` |
| `GebTests/Mathlib/` | `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`, `GebTests.Mathlib.*`, `GebLang.*` | `Geb.Mathlib.`, `GebTests.Mathlib.`, `GebLang.` |
| `Geb/Cslib/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `Geb.Cslib.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Cslib.`, `Geb.Mathlib.`, `GebLang.` |
| `GebTests/Cslib/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `Geb.Cslib.*`, `GebTests.Cslib.*`, `Geb.Mathlib.*`, `GebLang.*` | `Geb.Cslib.`, `GebTests.Cslib.`, `Geb.Mathlib.`, `GebLang.` |
| `GebLang/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `GebLang.*` (plus `Cslib.Init` when the file imports any `Cslib.*`) | `GebLang.` |
| `GebTests/Lang/` | `Mathlib.*`, `Batteries.*`, `Cslib.*`, `GebLang.*`, `GebTests.Lang.*` (plus `Cslib.Init` when the file imports any `Cslib.*`) | `GebLang.`, `GebTests.Lang.` |
```

The `Batteries.*` rationale paragraph

```markdown
`Batteries.*` is admitted to the mathlib-targeted subtrees because
mathlib depends on Batteries and imports its modules directly, so a
Batteries import survives extraction to mathlib4. Batteries modules
that no `Mathlib.*` module imports are reachable no other way.
```

becomes

```markdown
`Batteries.*` is admitted to every upstream-eligible location because
mathlib depends on Batteries and imports its modules directly, and
Cslib does the same, so a Batteries import survives extraction to
either upstream. Batteries modules that no `Mathlib.*` module imports
are reachable no other way.
```

Add after the table's rationale paragraphs:

```markdown
`GebLang/` and `GebTests/Lang/` carry a conditional form of Cslib's
`Cslib.Init` requirement: a module that imports any `Cslib.*` module,
in any of the four import forms, imports `Cslib.Init` itself, and a
module that imports none is not forced to. Only a plain or `public`
import of `Cslib.Init` satisfies the requirement, matching the two
Cslib subtrees' unconditional form. The direct-import form suffices
because Cslib's own check is transitive: a Cslib-track module
importing only extracted `GebLang` siblings inherits `Cslib.Init`
through them.

A `GebTests/Lang/` module's sibling imports do not cross tracks. A
Cslib-track test importing a mathlib-track sibling would need the
Cslib test tree to import mathlib's, which no upstream ordering makes
compile; `scripts/check-transitive-imports.sh` rejects it.
```

The self-prefix rule's opening sentence

```markdown
A self-prefix appears **only** in `^import` lines that
reference siblings in the same subtree. Do NOT use a self-prefix in:
```

becomes

```markdown
A self-prefix appears **only** in the module path of an import line
referencing a sibling in the same subtree. An import line's trailing
comment is checked like any other prose. Do not use a self-prefix in:
```

The enforcement sentence gains the second script:

```markdown
`scripts/lint-imports.sh` enforces these rules and
`scripts/check-transitive-imports.sh` enforces the closure rules
above them; the smoke tests are
`scripts/tests/test-lint-imports.sh` and
`scripts/tests/test-check-transitive-imports.sh`.
```

The closing cross-subtree paragraph

```markdown
The cross-subtree boundary follows the upstream dependency
relationship: mathlib does not depend on CSLib (so `Geb/Mathlib/`
files cannot import from `Cslib.*` or `Geb.Cslib.*`), and CSLib
depends on mathlib only through the upstream `Mathlib.*` modules
(so `Geb/Cslib/` files cannot import from `Geb.Mathlib.*` —
unupstreamed mathlib-targeted content is not yet available to a
CSLib PR). `Geb/Internal/` may import from any of the above.
```

becomes

```markdown
The cross-subtree boundary follows the upstream dependency
relationship, in one direction. Mathlib does not depend on Cslib, so
`Geb/Mathlib/` files cannot import from `Cslib.*` or `Geb.Cslib.*`,
and no `GebLang` module they import may reach `Cslib.*` either.
Cslib does depend on mathlib, so `Geb/Cslib/` files may import
`Geb.Mathlib.*` and mathlib-track `GebLang.*`: the dependency ships
first, and the Cslib PR follows once it merges and Cslib's mathlib
pin advances. `Geb/Internal/` may import from any of the above, with
no list to amend.
```

- [ ] **Step 5: extend § Cslib-specific constraints**

The section's opening

```markdown
CSLib's `CONTRIBUTING.md` adds the following requirements beyond
mathlib's style. Files in `Geb/Cslib/` (and `GebTests/Cslib/`):
```

becomes

```markdown
Cslib's `CONTRIBUTING.md` adds the following requirements beyond
mathlib's style. They bind files in `Geb/Cslib/` and
`GebTests/Cslib/`, and Cslib-track modules of `GebLang/` and
`GebTests/Lang/`, which ship to Cslib and so carry them at authoring
time:
```

and the `Cslib.Init` bullet gains its conditional form:

```markdown
- **Import `Cslib.Init`**: every Cslib-targeted file imports
  `Cslib.Init`, which configures Cslib's default linting and
  tactics. Cslib's CI runs `lake exe checkInitImports`. In
  `GebLang/` and `GebTests/Lang/` the requirement is conditional on
  the file importing any `Cslib.*` module (§ Subtree import rules).
```

- [ ] **Step 6: add the extraction bullet to `docs/rules/lean-coding.md`**

In § Literate modules (`GebLang`), which plan 1 created, add a fourth
bullet:

```markdown
- `scripts/extract-pr.sh` converts the roles to plain Markdown when a
  module is extracted, a checked name reference becoming a bare code
  span, so the checked markup stays local to this repository and the
  shipped file carries the converted form.
```

- [ ] **Step 7: revise `docs/index.md` § Directory structure**

The bullet list becomes:

```markdown
- `Geb/` — root namespace, split between upstream-eligible and
  downstream-only content.
  - `Geb/Mathlib/` — content authored in mathlib's style and
    intended for eventual upstream extraction to mathlib4;
    imports from `Mathlib.*`, `Batteries.*`, `Geb.Mathlib.*`, and
    `GebLang.*` only. Where those import rules leave no alternative,
    a module here may instead target Lean core or Batteries; that
    destination is open, per `TODO.md` § Upstream destination of
    core- and Batteries-targeted content.
  - `Geb/Cslib/` — content authored in Cslib's style and
    intended for eventual upstream extraction to Cslib;
    imports from `Mathlib.*`, `Batteries.*`, `Cslib.*`,
    `Geb.Cslib.*`, `Geb.Mathlib.*`, and `GebLang.*` only.
  - `Geb/Internal/` — content not intended for upstream
    extraction; may import from `Mathlib.*`, `Cslib.*`,
    `Geb.Mathlib.*`, `Geb.Cslib.*`, `GebLang.*`, or
    `Geb.Internal.*`.
- `GebLang/` — the Geb language's core data structures, at the
  bottom of the dependency order; imports from `Mathlib.*`,
  `Batteries.*`, `Cslib.*`, and `GebLang.*` only. Each module is
  upstream-eligible and ships to mathlib4 or to Cslib according to
  its own import closure. Written in Verso's literate style and
  rendered twice (`README.md` § Documentation).
- `GebTests/` — test library mirroring `Geb/`'s structure, with
  `GebTests/Mathlib/`, `GebTests/Cslib/`, and `GebTests/Internal/`
  subdirectories, plus `GebTests/Lang/`, which tests `GebLang/`.
- `manual/` — the Verso manual (build and serve commands:
  `README.md` § Documentation).
```

and the closing sentence

```markdown
The directory split denotes upstream eligibility; the
import-direction rules above are enforced by
`scripts/lint-imports.sh` and corresponding CI.
```

becomes

```markdown
The directory split denotes upstream eligibility; the
import-direction rules above are enforced by
`scripts/lint-imports.sh`, and the closure rules behind them by
`scripts/check-transitive-imports.sh`, both in the pre-push
checklist and in CI.
```

- [ ] **Step 8: revise `README.md`**

Four edits, in the one pass the spec's § Standards and rule documents
calls for; this is why plan 1 left the file alone.

In § Documentation, add after the manual bullet:

```markdown
- The `GebLang` literate site (Verso): `scripts/literate.sh build`
  builds the library, lints it, and renders the site;
  `scripts/literate.sh serve` serves it and prints the URL. There is
  no watch mode: after editing a docstring, re-run `build` and
  refresh the browser. Built in CI by `doc-build.yml`; the library
  itself is in the default `lake build`.
```

The introduction's second sentence

```markdown
The repository develops mathematical content in a style
shaped to be plausibly upstreamable to mathlib4 (via the
`Geb/Mathlib/` subtree) or CSLib (via `Geb/Cslib/`) alongside
downstream-only content (under `Geb/Internal/`).
```

becomes

```markdown
The repository develops mathematical content in a style
shaped to be plausibly upstreamable to mathlib4 (via the
`Geb/Mathlib/` subtree) or Cslib (via `Geb/Cslib/`), with the Geb
language's core data structures in `GebLang/`, which ships to either
upstream per module, alongside downstream-only content (under
`Geb/Internal/`).
```

In § Process, the path-scoped bullet

```markdown
- `upstream-eligible.md` — applies under `Geb/Mathlib/`,
  `Geb/Cslib/`, `GebTests/Mathlib/`, and `GebTests/Cslib/`.
```

becomes

```markdown
- `upstream-eligible.md` — applies under `Geb/Mathlib/`,
  `Geb/Cslib/`, `GebTests/Mathlib/`, `GebTests/Cslib/`, `GebLang/`,
  and `GebTests/Lang/`.
```

In § Upstream targets, add after the existing paragraph:

```markdown
Content in `GebLang/` is upstream-eligible per module: a module whose
import closure reaches no `Cslib.*` extracts to mathlib4, and one
whose closure reaches it extracts to Cslib. Some `Geb/Internal/` code
may eventually be recast into `GebLang/` in the same way it may be
recast into either `Geb/` subtree.
```

and extend the closing sentence of the existing paragraph

```markdown
Code in `Geb/Internal/`
is not eligible for upstream submission; some of it may eventually be
recast into an upstream-eligible form and moved to `Geb/Mathlib/` or
`Geb/Cslib/`, while other Internal code has no upstream home.
```

to

```markdown
Code in `Geb/Internal/`
is not eligible for upstream submission; some of it may eventually be
recast into an upstream-eligible form and moved to `Geb/Mathlib/`,
`Geb/Cslib/`, or `GebLang/`, while other Internal code has no
upstream home.
```

- [ ] **Step 9: revise `CONTRIBUTING.md`**

The § Submission policy bullet's first sentence

```markdown
- **LLM-contribution policy** binds any work in `Geb/Mathlib/`
  or `Geb/Cslib/`.
```

becomes

```markdown
- **LLM-contribution policy** binds any work in `Geb/Mathlib/`,
  `Geb/Cslib/`, or `GebLang/`.
```

and that bullet's closing sentence

```markdown
  We apply this bar to both subtrees.
```

becomes

```markdown
  We apply this bar to every upstream-eligible location.
```

The § Floodgate test section

```markdown
At all times, the repo is ready to ship dependency-ordered PRs on
short notice with no source-code changes. `scripts/lint-imports.sh`
enforces this by rejecting forbidden imports in `Geb/Mathlib/`
and `Geb/Cslib/` files, and the `Geb.Mathlib.` / `Geb.Cslib.`
prefixes outside import lines.
```

becomes

```markdown
At all times, the repository is ready to ship dependency-ordered PRs
on short notice with no source-code changes.
`scripts/lint-imports.sh` enforces this by rejecting forbidden
imports in `Geb/Mathlib/`, `Geb/Cslib/` and `GebLang/` files, and the
self-prefixes outside an import path;
`scripts/check-transitive-imports.sh` enforces the closure rules the
direct-import lists cannot see. Extraction is dependency-ordered
through `GebLang/`, each module retargeted by its own import closure.
```

The § Repo structure line

```markdown
`Geb/Mathlib/*` and `Geb/Cslib/*` upstream-eligible |
`Geb/Internal/*` downstream-only.
```

becomes

```markdown
`Geb/Mathlib/*`, `Geb/Cslib/*` and `GebLang/*` upstream-eligible |
`Geb/Internal/*` downstream-only.
```

- [ ] **Step 10: revise `AGENTS.md`**

The § AI authoring sentence

```markdown
An AI agent may draft code for upstream-eligible subtrees. Before
the user commits it to `Geb/Mathlib/` or `Geb/Cslib/`, the user
understands every line,
```

becomes

```markdown
An AI agent may draft code for upstream-eligible locations. Before
the user commits it to `Geb/Mathlib/`, `Geb/Cslib/` or `GebLang/`,
the user understands every line,
```

The path-scoped section heading

```markdown
### When editing files under Geb/Mathlib/ or Geb/Cslib/
```

becomes

```markdown
### When editing files under Geb/Mathlib/, Geb/Cslib/ or GebLang/
```

with the matching TOC entry updated. Run `doctoc --update-only .`
rather than hand-editing the anchor.

- [ ] **Step 11: record the spelling inconsistency this leaves**

The edits of Steps 4 and 5 write `Cslib`, the spelling the project
vocabulary accepts, into a document whose heading
`## CSLib-specific constraints` and several untouched sentences use
the other one. Normalising the whole document is a separate concern
under `CONTRIBUTING.md` § Concern shape, so record it rather than
bundling it. Add to `TODO.md` § Triggers:

```markdown
- **Normalise the spelling of `Cslib` in the committed corpus**: the
  project vocabulary
  (`styles/config/vocabularies/GebMathlib/accept.txt`) accepts
  `Cslib`, and Vale rejects the capitalised form, but documents
  predating the vocabulary carry it, `docs/rules/upstream-eligible.md`
  most heavily, including a section heading and its table-of-contents
  entry. Trigger: a branch whose concern is the documents themselves,
  which retitles the section and re-runs `doctoc`.
```

- [ ] **Step 12: run the Markdown checks**

Run:

```bash
doctoc --update-only . && markdownlint-cli2 '**/*.md' && bash scripts/check-md-links.sh
```

Expected: exit 0 from each. `doctoc` inserts a `**Table of Contents**`
title line into any TOC it regenerates; delete it, the repository's
TOCs carrying none.

- [ ] **Step 13: commit**

```bash
jj commit -m 'doc(geblang): state the GebLang layering and floodgate rules'
jj bookmark move feat/geblang-literate --to @-
```

## Task 6: the enumeration sweep

**Files:**

- Modify: `.github/workflows/ci.yml`
- Modify: `GebMeta.lean`
- Modify: any further file the greps below turn up

**Interfaces:**

- Consumes: the state Tasks 1 to 5 reach.
- Produces: a committed corpus with no statement left false by
  `GebLang`. This is a verified task: an instance the greps miss is a
  defect, not a gap in the list below.

- [ ] **Step 1: run the sweep greps**

Run, from the repository root:

```bash
grep -rn --include='*.md' --include='*.lean' --include='*.sh' \
  --include='*.yml' --include='*.toml' \
  --exclude-dir=.lake --exclude-dir=.jj --exclude-dir=.remember \
  --exclude-dir=.superpowers --exclude-dir=node_modules \
  --exclude-dir=superpowers \
  -e 'both subtrees' -e 'two subtrees' -e 'each subtree' \
  -e 'either subtree' -e 'defaultTargets' -e 'root librar' \
  -e 'mirror' -e 'Geb\.\*' -e 'GebTests\.\*' \
  -e 'Geb/Mathlib/ or Geb/Cslib/' -e 'Geb/Mathlib/`, `Geb/Cslib/' \
  . > /tmp/geblang-sweep.txt
wc -l /tmp/geblang-sweep.txt
```

Read every hit. A hit is a defect when the statement enumerates the
upstream-eligible locations, the porting destinations, the subtree or
mirror structure, or the root libraries, and omits `GebLang`. A hit
that names a specific subtree for its own sake is not.

`--exclude-dir=superpowers` drops `docs/superpowers/`: the spec, the
two plans and the review records are transient documents that the
branch's final commits remove, so they are not part of the committed
corpus the sweep is over. Without the exclusion they are roughly half
the hits.

- [ ] **Step 2: fix the `ci.yml` rationale comment**

The `mk_all-check` comment

```yaml
          # Everything builds via the `Geb.*`/`GebTests.*` globs
          # rather than a root import list, and bulk imports are
          # arranged per subdirectory; there is no flat root
          # aggregator for mk_all to check.
```

becomes

```yaml
          # Everything builds via the `Geb.*`/`GebTests.*`/`GebLang.*`
          # globs rather than a root import list, and bulk imports are
          # arranged per subdirectory; there is no flat root
          # aggregator for mk_all to check.
```

- [ ] **Step 3: fix the `GebMeta.lean` namespace enumeration**

The § Implementation notes sentence

```lean
The module lives
outside the `Geb`/`GebTests` namespaces so the linter does not
audit its own metaprogramming code.
```

becomes

```lean
The module lives
outside the `Geb`, `GebTests` and `GebLang` namespaces so the linter
does not audit its own metaprogramming code.
```

- [ ] **Step 4: confirm the instances the earlier work already covered**

These were fixed in the tasks that touched them; confirm each rather
than editing it twice.

```bash
grep -n 'GebTests.Lang' GebTests.lean
grep -n 'GebLang' scripts/pre-push.sh
grep -n 'GebLang' scripts/tests/test-lint-driver.sh
grep -n 'GebLang' docs/index.md
```

Expected: the `GebTests.lean` docstring's mirror enumeration names
`GebTests.Lang` (plan 1, Task 2); `scripts/pre-push.sh` names
`GebLang` in the docs-coverage pattern, its message, the shake
invocation, the lint step and the cache rationale (plan 1, Task 5);
`scripts/tests/test-lint-driver.sh` carries the coverage scan and the
literate workflow literal (plan 1, Task 5); `docs/index.md` carries
the `GebLang/` bullet (Task 5 above).

- [ ] **Step 5: fix whatever else the sweep found**

Apply the same treatment to every remaining defect from Step 1. Record
each file changed in the task report; the sweep is the spec's verified
task, so the report is the evidence that it ran.

- [ ] **Step 6: re-run the sweep and the full checklist**

Run:

```bash
bash scripts/pre-push.sh
```

Expected: exit 0, ending with the `pre-push: clean.` line. This runs
the build, the test driver, all three lint invocations, the widened
`lake shake`, every script self-test including the two added by this
plan, and the Markdown checks.

- [ ] **Step 7: commit**

```bash
jj commit -m 'doc(geblang): sweep the enumerations for GebLang'
jj bookmark move feat/geblang-literate --to @-
```

- [ ] **Step 8: report the state for user review**

Both plans are then executed. The workflow files are verified by CI
after the user's review and push, as for the manual workstream; no
push happens without that review.
</content>
