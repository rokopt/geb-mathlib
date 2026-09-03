#!/usr/bin/env bash
#
# scripts/tests/test-extract-pr.sh
#
# Tests scripts/extract-pr.sh: destination-path mapping per subtree,
# the import-line prefix rewrite (Geb.<Subtree>. -> <Subtree>.),
# GebLang/ and GebTests/Lang/ track resolution, Verso role-markup
# conversion, and the GebLang/ arm's non-upstream-line strip pass.
# Offline and deterministic.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="$here/../extract-pr.sh"

failed=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cd "$tmp" || exit 1

has() { # name needle file
  if ! grep -qF "$2" "$3"; then
    echo "FAIL: $1 (missing '$2' in $3)"; failed=1; fi
}
lacks() { # name needle file
  if grep -qF "$2" "$3"; then
    echo "FAIL: $1 (unexpected '$2' in $3)"; failed=1; fi
}
exists() { # name path
  if [ ! -f "$2" ]; then echo "FAIL: $1 (no $2)"; failed=1; fi
}
no_double_blank() { # name file
  # `exit 0` inside the main block would still run END, whose own
  # `exit` overrides it, so the found/not-found result is carried in
  # a variable read by END rather than an early exit code.
  if awk 'BEGIN { found = 0 }
          { blank = ($0 == ""); if (blank && prevblank) found = 1
            prevblank = blank }
          END { exit !found }' "$2"; then
    echo "FAIL: $1 (consecutive blank lines in $2)"; failed=1
  fi
}

# Geb/Mathlib -> Mathlib/, import and public import rewritten.
mkdir -p Geb/Mathlib/Foo fork1
cat > Geb/Mathlib/Foo/Bar.lean <<'EOF'
module
public import Geb.Mathlib.Foo.Baz
import Geb.Mathlib.Other
import Mathlib.Tactic
EOF
bash "$SCRIPT" Geb/Mathlib/Foo/Bar.lean fork1 >/dev/null
out=fork1/Mathlib/Foo/Bar.lean
exists "Geb/Mathlib -> Mathlib path" "$out"
has   "public import rewritten" "public import Mathlib.Foo.Baz" "$out"
has   "import rewritten"        "import Mathlib.Other" "$out"
has   "foreign mathlib import preserved" "import Mathlib.Tactic" "$out"
lacks "no Geb.Mathlib. prefix remains"  "Geb.Mathlib." "$out"

# GebTests/Mathlib -> MathlibTest/.
mkdir -p GebTests/Mathlib fork2
printf 'module\nimport Geb.Mathlib.X\n' > GebTests/Mathlib/Y.lean
bash "$SCRIPT" GebTests/Mathlib/Y.lean fork2 >/dev/null
exists "GebTests/Mathlib -> MathlibTest path" "fork2/MathlibTest/Y.lean"

# Geb/Cslib -> Cslib/; a prefix embedded in a non-import line is left
# alone (import-anchored rewrite).
mkdir -p Geb/Cslib fork3
cat > Geb/Cslib/Z.lean <<'EOF'
module
import Geb.Cslib.A
-- mentions XGeb.Cslib.embedded in a comment
EOF
bash "$SCRIPT" Geb/Cslib/Z.lean fork3 >/dev/null
has   "cslib import rewritten" "import Cslib.A" "fork3/Cslib/Z.lean"
has   "embedded non-import ref untouched" "XGeb.Cslib.embedded" "fork3/Cslib/Z.lean"

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

/-- Anchors {name}`Nat` in a docstring, beside Lean the conversion
must not touch: {lit}`Type.{u}` and {lit}`{S}` carry a brace group of
the same shape as a role, `{p}` is a code span with no role at all,
and {lit}`freeVars (var name) = {name}` ends a span with a group
spelled exactly like one. -/
EOF
bash "$SCRIPT" GebLang/Foo/Bar.lean fork4 >/dev/null
out=fork4/Mathlib/Foo/Bar.lean
exists "mathlib-track GebLang -> Mathlib path" "$out"
has   "mathlib-track sibling rewritten" "public import Mathlib.Foo.Base" "$out"
lacks "name role converted" '{name}`Nat`' "$out"
lacks "lit role converted" '{lit}' "$out"
has   "code span survives the conversion" '`Nat`' "$out"
has   "universe ascription survives conversion" '`Type.{u}`' "$out"
has   "binder group survives conversion" '`{S}`' "$out"
has   "role-less code span untouched" '`{p}`' "$out"
has   "singleton set at a span's end survives" \
      '`freeVars (var name) = {name}`' "$out"

# The first `lacks` names the exact role application rather than the
# bare word or the role form: the fixture's last span legitimately
# ends in `{name}` followed by the span's own closing backtick, so
# both looser tests would read surviving mathematics as unconverted
# markup. `{lit}` survives nowhere, so the bare word serves there.

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
# The docstring here carries Lean that the role-conversion pattern
# must not touch: a universe ascription and a subtype, each inside a
# code span. This arm does not convert roles at all; the GebLang/
# fixture below covers the same shapes in the arm that does.
mkdir -p fork8
cat > Geb/Mathlib/Foo/Wide.lean <<'EOF'
module
import GebLang.Foo.Base
public meta import Geb.Mathlib.Other

/-- Relates `F : C ⥤ Cat.{v, u}` to the fiber `{g : B → k // p g}`. -/
EOF
bash "$SCRIPT" Geb/Mathlib/Foo/Wide.lean fork8 >/dev/null
out=fork8/Mathlib/Foo/Wide.lean
has   "Geb/Mathlib rewrites GebLang." "import Mathlib.Foo.Base" "$out"
has   "meta import form rewritten" "public meta import Mathlib.Other" "$out"
has   "universe ascription survives" 'Cat.{v, u}' "$out"
has   "subtype in a code span survives" '{g : B → k // p g}' "$out"

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
import GebLang.Foo.Base
import GebLang.Cs.Deep
EOF
bash "$SCRIPT" GebTests/Cslib/Wide.lean fork11 >/dev/null
out=fork11/CslibTests/Wide.lean
has   "GebTests/Cslib rewrites Geb.Mathlib." "import Mathlib.Thing" "$out"
has   "GebTests/Cslib rewrites its test self-prefix" \
      "import CslibTests.Helper" "$out"
has   "GebTests/Cslib rewrites a mathlib-track GebLang import" \
      "import Mathlib.Foo.Base" "$out"
has   "GebTests/Cslib rewrites a cslib-track GebLang import" \
      "import Cslib.Cs.Deep" "$out"

# The GebLang/ arm's strip pass. `Lean.DocString.Syntax` is imported
# in all four keyword forms, and every form is deleted outright. The
# fixture mirrors a GebLang/ module's own shape rather than a shape
# picked for convenience: a blank line separates `module` from the
# import block, as it does in the real files, and content follows the
# block. The blank after the stripped run follows a blank already
# written out, so the blank-line rule must suppress it; a fixture with
# `module` abutting the imports cannot exhibit a doubled blank in
# either the correct or the broken version of the rule. A docstring
# mentioning the module's
# name as an ordinary word, and a docstring sentence whose first word
# is `import`, are prose and survive; the strip pass and the ordinary
# import-rewrite table both leave them untouched.
mkdir -p fork12
cat > GebLang/Foo/Strip.lean <<'EOF'
module

import Lean.DocString.Syntax
public import Lean.DocString.Syntax
public meta import Lean.DocString.Syntax
meta import Lean.DocString.Syntax  -- shake: keep; role markup

/-- This docstring mentions Lean.DocString.Syntax as an ordinary word,
to confirm that prose survives the strip pass.
import statements sometimes appear in prose text, not only as an
actual Lean import; neither the strip pass nor the rewrite table may
touch this sentence, since its module-shaped word matches neither. -/

@[expose] public section
EOF
bash "$SCRIPT" GebLang/Foo/Strip.lean fork12 >/dev/null
out=fork12/Mathlib/Foo/Strip.lean
exists "GebLang strip-pass fixture -> Mathlib path" "$out"
lacks "all four Lean.DocString.Syntax import forms stripped" \
      "import Lean.DocString.Syntax" "$out"
lacks "stripped meta import's trailing comment gone" \
      "shake: keep; role markup" "$out"
has   "docstring mentioning the module as prose survives" \
      "mentions Lean.DocString.Syntax as an ordinary word" "$out"
has   "docstring sentence starting with the word import survives" \
      "import statements sometimes appear in prose text" "$out"
has   "content after the stripped run survives" \
      "@[expose] public section" "$out"
no_double_blank \
      "no doubled blank line around the stripped run" "$out"

# A literate Geb/Mathlib/ module: the strip pass and the role
# conversion run on every arm, not on GebLang/ alone. The
# `set_option doc.verso true` line, with a trailing comment, the
# `Lean.DocString.Syntax` import and the `GebMeta` meta import are
# deleted; a `{cite}` role becomes mathlib's `[Key]` citation form,
# other roles become bare code spans, an escaped bracket becomes the
# bare bracket; and the mathematics between them is byte-identical.
mkdir -p fork19
cat > Geb/Mathlib/Foo/Lit.lean <<'EOF'
module

public import Mathlib.Foo.Base
import Lean.DocString.Syntax
meta import GebMeta  -- shake: keep; supplies the cite docstring role

set_option doc.verso true  -- checked docstrings

/-! # A literate module

{name}`Nat` and {lit}`x ↦ x`, citing {cite}`Key2001` and \[Key2002\].
-/

/-- The successor, per {cite}`Key2001`. -/
def a (n : Nat) : Nat := n + 1
EOF
bash "$SCRIPT" Geb/Mathlib/Foo/Lit.lean fork19 >/dev/null
out=fork19/Mathlib/Foo/Lit.lean
exists "literate Geb/Mathlib fixture -> Mathlib path" "$out"
lacks "set_option doc.verso line stripped" "doc.verso" "$out"
lacks "Lean.DocString.Syntax import stripped" "Lean.DocString.Syntax" "$out"
lacks "GebMeta meta import stripped" "GebMeta" "$out"
has   "module docstring roles and cite convert" \
      '`Nat` and `x ↦ x`, citing [Key2001] and [Key2002].' "$out"
has   "declaration docstring cite converts" \
      'The successor, per [Key2001].' "$out"
has   "the surviving import is rewritten in place" \
      "public import Mathlib.Foo.Base" "$out"
has   "code is byte-identical" "def a (n : Nat) : Nat := n + 1" "$out"
no_double_blank "no doubled blank line around the stripped run" "$out"
# The surviving import and the module docstring stay separated by the
# one blank line the source had: the blank after the stripped import
# follows a non-blank line and is kept, the one after the stripped
# command follows that kept blank and is dropped.
if [ "$(sed -n '3p' "$out")" != "public import Mathlib.Foo.Base" ] \
   || [ -n "$(sed -n '4p' "$out")" ] \
   || [ "$(sed -n '5p' "$out")" != "/-! # A literate module" ]; then
  echo "FAIL: one blank line kept between the imports and the module docstring"
  failed=1
fi

# The docstring gate (fix round 2): role conversion is scoped to
# lines inside a docstring, and the strip pass to lines outside one.
# `{name}`Nat`` appears in three contexts here — a single-line
# docstring, the opening line of a multi-line docstring, and a plain
# `/- ... -/` block comment — each wrapped in distinct prose so a
# single `has`/`lacks` check names the context unambiguously. The
# code line at the end is the reviewer's own regression example,
# checked byte-for-byte against the untouched source line: role
# conversion running on every line, rather than only inside a
# docstring, converted a `Name`-literal singleton set exactly this
# shape.
mkdir -p fork13
cat > GebLang/Foo/Gate.lean <<'EOF'
module

import Lean.DocString.Syntax

/-- Single-line docstring role converts: {name}`Nat`. -/

/-- Opening-line role: {name}`Nat`.
Middle-line role: {lit}`Type.{u}`.
Closing-line role: {option}`doc.verso` -/

/- Plain block comment, not a docstring: {name}`Nat` stays literal. -/

def a : List Name := [{name}`foo, `bar]
EOF
bash "$SCRIPT" GebLang/Foo/Gate.lean fork13 >/dev/null
out=fork13/Mathlib/Foo/Gate.lean
exists "docstring-gate fixture -> Mathlib path" "$out"
has   "single-line docstring role converts" \
      'Single-line docstring role converts: `Nat`.' "$out"
has   "multi-line docstring opening-line role converts" \
      'Opening-line role: `Nat`.' "$out"
has   "multi-line docstring middle-line role converts" \
      'Middle-line role: `Type.{u}`.' "$out"
has   "multi-line docstring closing-line role converts" \
      'Closing-line role: `doc.verso`' "$out"
has   "code line outside any docstring is byte-identical" \
      'def a : List Name := [{name}`foo, `bar]' "$out"
has   "plain block comment role stays unconverted" \
      'not a docstring: {name}`Nat` stays literal.' "$out"
lacks "real import Lean.DocString.Syntax outside a docstring is still stripped" \
      "import Lean.DocString.Syntax" "$out"

# A fenced code block inside a docstring, whose body line reads
# `import Lean.DocString.Syntax`: the strip pass, scoped to outside a
# docstring, must not touch it. A real import line is never inside a
# docstring, so nothing a real extraction needs is lost by the scope.
mkdir -p fork14
cat > GebLang/Foo/Fence.lean <<'EOF'
module

/-- A docstring containing a fenced code block.
```
import Lean.DocString.Syntax
```
-/
EOF
bash "$SCRIPT" GebLang/Foo/Fence.lean fork14 >/dev/null
out=fork14/Mathlib/Foo/Fence.lean
exists "docstring-fenced-code fixture -> Mathlib path" "$out"
has   "fenced import line survives inside the docstring" \
      "import Lean.DocString.Syntax" "$out"

# A `/- ... -/` block comment nested inside a docstring must not end
# the docstring at its own `-/`. A single doc_state flag would end it
# there, so a fenced import line past the nested comment would read
# as outside the docstring and be silently deleted; the depth counter
# only returns to the outer docstring's level at the nested comment's
# close, so the fence past it is still inside.
mkdir -p fork15
cat > GebLang/Foo/NestedFence.lean <<'EOF'
module

/-- Docstring text.
/- inner block comment -/
```
import Lean.DocString.Syntax
```
-/
EOF
bash "$SCRIPT" GebLang/Foo/NestedFence.lean fork15 >/dev/null
out=fork15/Mathlib/Foo/NestedFence.lean
exists "nested-comment fenced fixture -> Mathlib path" "$out"
has   "fenced import line past a nested comment survives" \
      "import Lean.DocString.Syntax" "$out"

# A role appearing after a nested block comment, in the same
# docstring, converts: the depth counter keeps the docstring open past
# the nested comment's `-/`.
mkdir -p fork17
cat > GebLang/Foo/NestedRole.lean <<'EOF'
module

/-- Text before.
/- inner comment -/
Role after nested comment: {name}`Nat`. -/
EOF
bash "$SCRIPT" GebLang/Foo/NestedRole.lean fork17 >/dev/null
out=fork17/Mathlib/Foo/NestedRole.lean
exists "nested-comment role fixture -> Mathlib path" "$out"
has   "role after a nested comment now converts" \
      "Role after nested comment: \`Nat\`." "$out"
lacks "no unconverted role remains after a nested comment" \
      "{name}\`Nat\`" "$out"

if [ "$failed" -ne 0 ]; then
  echo "test-extract-pr.sh: failures"
  exit 1
fi
echo "test-extract-pr.sh: all checks passed"
