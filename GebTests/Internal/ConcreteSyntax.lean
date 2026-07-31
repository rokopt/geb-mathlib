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
printer's spelling, which no theorem pins; and evaluate the retraction,
the rose bijection and the formatter, which the theorems state but do
not run.

Three places where the parser deliberately admits more than the printer
emits are recorded here, since each is a divergence from [RFC9804]
canonical form: a label atom may be empty, a label atom may carry
leading zeros, and the length prefix of a verbatim atom may carry
leading zeros.

Inputs are `List Char`, built by `atomRaw` out of the same two
productions the grammar has. Core's `String.toList` is unavailable here:
it depends on `Classical.choice`, which
[CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md) forbids.
`String.ofList` is choice-free, so the printer's output is still checked
against a string literal.

The assertions are `#guard` rather than `by decide`: equality of `Ast k`
goes through `WType.beq`, which folds over a `FinEnum` enumeration and
does not reduce usefully in the kernel.

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

/-- A three-node tree over a three-letter leaf alphabet. -/
def sampleAst : Ast 3 :=
  Ast.fork (Ast.leaf 0) (Ast.fork (Ast.leaf 1) (Ast.leaf 2))

/-- The canonical S-expression spelling of `sampleAst`. -/
def sampleText : String := String.ofList (Csexp.print sampleAst)

/-! ## The printer's spelling, which no theorem pins -/

#guard sampleText == "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"

/-! ## The proved round trips, evaluated

`Csexp.parse_print` and `Ast.ofRose_toRose` already state these. What
the assertions add is that the compiled evaluation agrees with the
kernel and terminates — `WType.beq` and `WType.para` are folds over a
`FinEnum` enumeration, and nothing else here runs them. -/

#guard Csexp.parse 3 (Csexp.print sampleAst) == some sampleAst

#guard Ast.ofRose sampleAst.toRose == sampleAst

#guard Tree.erase (Ast.trivialDoc sampleAst) == sampleAst

#guard Tree.extract (Tree.duplicate (Ast.trivialDoc sampleAst))
    == Ast.trivialDoc sampleAst

/-! ## The formatter

`Geb.format` is the module's headline abstraction and no theorem
evaluates it. `Geb.format_idem` is trivially true on its `none` branch,
so only a worked `some` shows the branch that does something. -/

#guard format (Csexp.parse 3) Csexp.print (Csexp.print sampleAst)
    == some (Csexp.print sampleAst)

#guard format (Csexp.parse 3) Csexp.print (leafSexp ['x']) == none

/-! ## The reader, where `Csexp.parse` cannot see

Two properties of `Csexp.readVerbatim` are invisible through `parse`:
whichever way they go, the atom is rejected further along and `parse`
answers `none`. They are asserted here on the reader itself. -/

-- A length prefix is what delimits an atom, so `)` and `:` inside the
-- declared content are content. Asserting this through `parse` would
-- not distinguish a reader that stopped at the `)`.
#guard Csexp.readVerbatim (Csexp.printVerbatim ['f', 'o', ')', 'k'] ++ ['x'])
    == some (['f', 'o', ')', 'k'], ['x'])

-- An atom declaring more content than follows it is rejected, not
-- truncated.
#guard Csexp.readVerbatim (atomRaw ['9'] Csexp.leafTok) == none

/-! ## `Ast.size` and the fuel it bounds -/

#guard sampleAst.size == 5

-- `Csexp.parse` supplies the input length, far above what is needed;
-- these pin the bound that actually operates.
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

-- A head atom that is neither token, here one containing `)`. That the
-- `)` is read as content rather than as a delimiter is asserted on the
-- reader above; at this level either behaviour yields `none`.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim ['f', 'o', ')', 'k'] ++ atom 1 ['0'])) == none
