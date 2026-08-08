/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax
public meta import Geb.Internal.ConcreteSyntax  -- shake: keep; #guard needs it

/-!
# Tests for the concrete-syntax prototype

`Geb.Csexp.parse_print` constrains the parser only on the printer's
output, so every rejection path is unexercised by it. The assertions
below exercise the parser on inputs the printer never emits; check the
printer's spelling and `Ast.size` at a concrete tree, which the
`@[simp]` lemmas pin but no theorem evaluates; evaluate the
retraction, the rose bijection and the formatter, which the theorems
state but do not run; and pin two properties of `Csexp.readVerbatim`
and of the fuel bound that `Csexp.parse` cannot see.

Three places where the parser deliberately admits more than the printer
emits are recorded here, since each is a divergence from [RFC9804]
canonical form: a label atom may be empty, a label atom may carry
leading zeros, and the length prefix of a verbatim atom may carry
leading zeros.

Inputs are `List Char`, built by `atomRaw` and `sexp` out of the same
two productions the canonical grammar has. Core's `String.toList` is
unavailable here: it depends on `Classical.choice`, which
[CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md) forbids.
`String.ofList` is choice-free, so the printer's output is still checked
against a string literal.

The assertions are `#guard`, which runs its argument in the interpreter.
`by decide` discharges every one of them too — `WType.beq` reduces in
the kernel, and the assertions that do not reach it compare `String`,
`Nat`, `Bool`, `Ann` or `Option` — but checks a different thing. A
parser and a printer are used by running them, so the interpreter is
the path worth exercising; that the kernel agrees is what the two forms
together would show.

## Main definitions

* `atomRaw`, `atom`, `sexp`, `leafBody`, `leafSexp`, `nodeTok` — input
  fixtures, built out of the canonical grammar's two productions.
* `sampleAst`, `sampleText` — the tree the assertions run on, and its
  printed spelling.

## References

* [RFC9804]

## Tags

concrete syntax, S-expression, parser, test
-/

@[expose] public section

open Geb

/-- A verbatim atom with an explicitly spelled length prefix, so that a
test may write a length the content does not have, or spell it
non-canonically. -/
def atomRaw (len content : List Char) : List Char := len ++ ':' :: content

/-- A verbatim atom of declared length `n`. At `n = content.length` this
is `Geb.Csexp.printVerbatim`. -/
def atom (n : Nat) (content : List Char) : List Char :=
  atomRaw (Csexp.decOf n) content

/-- Wrap a body in the parentheses of one s-expression. -/
def sexp (body : List Char) : List Char := '(' :: (body ++ [')'])

/-- The head atom of an s-expression that is neither `leaf` nor `fork`. -/
def nodeTok : List Char := ['n', 'o', 'd', 'e']

/-- The body of a well-formed leaf s-expression: its head atom and its
label atom, without the enclosing parentheses. -/
def leafBody (content : List Char) : List Char :=
  Csexp.printVerbatim Csexp.leafTok ++ atom content.length content

/-- A well-formed leaf s-expression whose label atom is `content`. -/
def leafSexp (content : List Char) : List Char := sexp (leafBody content)

/-- A five-node tree over a three-letter leaf alphabet. -/
def sampleAst : Ast 3 :=
  Ast.fork (Ast.leaf 0) (Ast.fork (Ast.leaf 1) (Ast.leaf 2))

/-- The canonical S-expression spelling of `sampleAst`. -/
def sampleText : String := String.ofList (Csexp.print sampleAst)

/-! ## The printer's spelling, which no theorem pins -/

#guard sampleText == "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"

/-! ## The proved round trips, evaluated

`Csexp.parse_print`, `Ast.ofRose_toRose`, `Ast.erase_trivialDoc` and
`Tree.extract_duplicate` already state four of these; the third
assertion below pins the rose orientation, which no theorem fixes. What
the assertions add is that the compiled evaluation agrees with the
kernel and terminates. `WType.beq`, which decides the equalities, folds
over a `FinEnum` enumeration; ten assertions in this file reach it, the
five below among them, while the twelve that compare `none` with `none`
are settled by `Option.decEq` without touching the payload.
`Tree.duplicate` is a `WType.para`, and only the last below runs
that. -/

#guard Csexp.parse 3 (Csexp.print sampleAst) == some sampleAst

#guard Ast.ofRose sampleAst.toRose == sampleAst

-- The orientation is normative, and the round trip above holds under
-- either choice, so it is pinned here: children are consumed as a
-- snoclist, so `sampleAst` is the curried application `0 1 2` and its
-- rose form nests one child deep at each level.
#guard Ast.toRose sampleAst
    == Rose.node 0 (fun _ : Fin 1 ↦
         Rose.node 1 (fun _ : Fin 1 ↦ Rose.node 2 Fin.elim0))

#guard Tree.erase (Ast.trivialDoc sampleAst) == sampleAst

#guard Tree.extract (Tree.duplicate (Ast.trivialDoc sampleAst))
    == Ast.trivialDoc sampleAst

/-! ## Relabelling

`Tree.map` is the only structure map no theorem here evaluates. The two
assertions are a pair: `Tree.erase` discards decorations whatever the
relabelling is, so the shape half passes under `id` too, and only the
`Tree.extract` half sees that the relabelling happened. -/

#guard Tree.extract (Tree.map (fun a : Ann ↦ { a with name := some "x" })
    (Ast.trivialDoc sampleAst)) == ({ name := some "x" } : Ann)

#guard Tree.erase (Tree.map (fun a : Ann ↦ { a with name := some "x" })
    (Ast.trivialDoc sampleAst)) == sampleAst

/-! ## The formatter

`Geb.format` is the law skeleton's one derived map, and no theorem
evaluates it. `Geb.format_idem` is trivially true on its `none` branch,
so only a worked `some` shows the branch that does something. -/

-- On a non-canonical spelling, so a `format` returning its input
-- unchanged on parse success fails this; and against a spelling built
-- from the fixtures rather than from `Csexp.print`, so a `print` that
-- emitted something else fails it too.
#guard format (Csexp.parse 3) Csexp.print (leafSexp ['0', '1'])
    == some (leafSexp ['1'])

/-! ## The reader, where `Csexp.parse` cannot see

Whether `Csexp.readVerbatim` rejects an over-long declared length or
truncates to it is invisible through `parse`: either way the atom is
rejected further along and `parse` answers `none`. It is asserted here
on the reader itself. That a `)` inside an atom's declared content is
content rather than a delimiter needs no assertion —
`Geb.Csexp.readVerbatim_append` states it for every atom. -/

-- An atom declaring more content than follows it is rejected, not
-- truncated. No theorem states this, and `parse` cannot see it.
#guard Csexp.readVerbatim (atomRaw ['9'] Csexp.leafTok) == none

/-! ## `Ast.size` and the fuel it bounds -/

#guard sampleAst.size == 5

-- `parseAst_printAst` asks for fuel at least `a.size`, which is 5 here.
-- The bound is not tight: fuel counts nesting depth, not nodes, so 3
-- suffices and 2 does not. `Csexp.parse` supplies the input length, far
-- above either.
#guard (Csexp.parseAst 3 3 (Csexp.print sampleAst)).isSome
#guard (Csexp.parseAst 3 2 (Csexp.print sampleAst)).isNone

/-! ## Inputs the parser accepts but the printer never emits -/

-- An empty label atom denotes leaf `0`: `Geb.Csexp.digitsVal [] = some 0`.
#guard Csexp.parse 3 (leafSexp []) == some (Ast.leaf 0)

-- A label atom may carry leading zeros; only the composite is
-- constrained by the retraction law.
#guard Csexp.parse 3 (leafSexp ['0', '1']) == some (Ast.leaf 1)

-- So may a length prefix, though [RFC9804]'s `decimal` production
-- forbids it: `Csexp.readNat` reads the digits and takes their value.
#guard Csexp.parse 3
  (sexp (atomRaw ['0', '4'] Csexp.leafTok ++ atom 1 ['0']))
    == some (Ast.leaf 0)

/-! ## Rejection paths -/

-- Empty input.
#guard Csexp.parse 3 [] == none

-- A leading character that is not `(`. The two assertions differ only
-- in the head character, and `Csexp.parseStep` uses that character for
-- nothing else, so the second fails if and only if the check is
-- dropped.
#guard Csexp.parse 3 ('(' :: (leafBody ['0'] ++ [')'])) == some (Ast.leaf 0)
#guard Csexp.parse 3 ('x' :: (leafBody ['0'] ++ [')'])) == none

-- A head atom whose declared length exceeds the input that follows it.
-- The length guard rejects it; were the guard removed, the truncated
-- atom would be rejected as a head atom, so this assertion does not
-- distinguish the two. The reader-level assertion above does.
#guard Csexp.parse 3 (sexp (atom 9 Csexp.leafTok ++ atom 1 ['0'])) == none

-- A label at the leaf alphabet's bound.
#guard Csexp.parse 3 (leafSexp ['3']) == none

-- Leaf `0` is out of range once the alphabet is empty.
#guard Csexp.parse 0 (leafSexp ['0']) == none

-- A missing closing parenthesis.
#guard Csexp.parse 3
  ('(' :: (Csexp.printVerbatim Csexp.leafTok ++ atom 1 ['0'])) == none

-- A fork whose children are missing entirely: the child parse meets the
-- empty input, which is `Csexp.parseStep`'s first rejection.
#guard Csexp.parse 3 ('(' :: Csexp.printVerbatim Csexp.forkTok) == none

-- A head atom that is neither `leaf` nor `fork`.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim nodeTok ++ atom 1 ['0'])) == none

-- A label atom whose content is not decimal.
#guard Csexp.parse 3 (leafSexp ['x']) == none

-- A fork with three children: `)` is required where the third begins.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim Csexp.forkTok ++ leafSexp ['0'] ++
    leafSexp ['1'] ++ leafSexp ['2'])) == none

-- Trailing input after a complete tree.
#guard Csexp.parse 3 (Csexp.print sampleAst ++ [')']) == none
