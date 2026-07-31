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
below exercise the parser on inputs the printer never emits, and record
the two places where the parser deliberately admits more than the printer
emits: a label atom may be empty, and it may carry leading zeros.

Inputs are `List Char`, built by `atom` out of the same two productions
the grammar has. Core's `String.toList` is unavailable here: it depends
on `Classical.choice`, which
[CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md) forbids.
`String.ofList` is choice-free, so the printer's output is still checked
against a string literal.

The assertions are `#guard` rather than `by decide`: equality of `Ast k`
goes through `WType.beq`, which folds over a `FinEnum` enumeration and
does not reduce usefully in the kernel.

## Tags

concrete syntax, S-expression, parser, test
-/

@[expose] public section

open Geb

/-- A verbatim atom with an explicitly chosen length prefix, so that a
test may declare a length its content does not have. At `n = content.length`
this is `Geb.Csexp.printVerbatim`. -/
def atom (n : Nat) (content : List Char) : List Char :=
  Csexp.decOf n ++ ':' :: content

/-- Wrap a body in the parentheses of one s-expression. -/
def sexp (body : List Char) : List Char := '(' :: (body ++ [')'])

/-- The head atom of an s-expression that is neither `leaf` nor `fork`. -/
def nodeTok : List Char := ['n', 'o', 'd', 'e']

/-- A three-node tree over a three-letter leaf alphabet. -/
def sampleAst : Ast 3 :=
  Ast.fork (Ast.leaf 0) (Ast.fork (Ast.leaf 1) (Ast.leaf 2))

/-- The canonical S-expression spelling of `sampleAst`. -/
def sampleText : String := String.ofList (Csexp.print sampleAst)

/-- A well-formed leaf s-expression whose label is `content`. -/
def leafSexp (content : List Char) : List Char :=
  sexp (Csexp.printVerbatim Csexp.leafTok ++ atom content.length content)

/-! ## The printer -/

#guard sampleText == "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"

#guard sampleAst.size == 5

/-! ## The retraction, and the rose bijection -/

#guard Csexp.parse 3 (Csexp.print sampleAst) == some sampleAst

#guard Ast.ofRose sampleAst.toRose == sampleAst

/-! ## Inputs the parser accepts but the printer never emits -/

-- An empty label atom denotes leaf `0`: `Geb.Csexp.digitsVal [] = some 0`.
#guard Csexp.parse 3 (leafSexp []) == some (Ast.leaf 0)

-- Leading zeros are accepted; only the composite is constrained.
#guard Csexp.parse 3 (leafSexp ['0', '1']) == some (Ast.leaf 1)

/-! ## Rejection paths -/

-- Empty input: the fuel is the input length, so there is none.
#guard Csexp.parse 3 [] == none

-- No opening parenthesis.
#guard Csexp.parse 3
  (Csexp.printVerbatim Csexp.leafTok ++ atom 1 ['0']) == none

-- A declared atom length exceeding the input that follows it.
#guard Csexp.parse 3 (sexp (atom 9 Csexp.leafTok ++ atom 1 ['0'])) == none

-- A label at the leaf alphabet's bound.
#guard Csexp.parse 3 (leafSexp ['3']) == none

-- The empty leaf alphabet admits no tree at all.
#guard Csexp.parse 0 (leafSexp ['0']) == none

-- A missing closing parenthesis.
#guard Csexp.parse 3
  ('(' :: (Csexp.printVerbatim Csexp.leafTok ++ atom 1 ['0'])) == none

-- A head atom that is neither `leaf` nor `fork`.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim nodeTok ++ atom 1 ['0'])) == none

-- A label atom whose content is not decimal.
#guard Csexp.parse 3 (leafSexp ['x']) == none

-- A fork with three children: the third is read where `)` is required.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim Csexp.forkTok ++ leafSexp ['0'] ++
    leafSexp ['1'] ++ leafSexp ['2'])) == none

-- Trailing input after a complete tree.
#guard Csexp.parse 3 (Csexp.print sampleAst ++ [')']) == none

-- Parentheses inside a verbatim atom are content, not delimiters: the
-- atom is read whole, and then rejected as a head atom.
#guard Csexp.parse 3
  (sexp (Csexp.printVerbatim ['f', 'o', ')', 'k'] ++ atom 1 ['0'])) == none
