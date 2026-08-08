/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.CanonicalSExpr  -- shake: keep; #guard needs it
public meta import Geb.Internal.CanonicalSExpr  -- shake: keep; #guard needs it
public import GebTests.Internal.ConcreteSyntax  -- shake: keep; #guard needs it
public meta import GebTests.Internal.ConcreteSyntax  -- shake: keep; #guard needs it

/-!
# Tests for the canonical S-expression data type

`Geb.Csexp.print_eq_render_toCSexp` states that the implemented printer
factors through `Geb.CSexp`; these assertions evaluate the factoring at
a tree, so the two sides are seen to agree rather than only proved to.

They also exhibit the point of carrying two maps into `Geb.CSexp`.
`Geb.Ast.toCSexp` spells a tree from `Ast`, tagging each node `leaf` or
`fork`; `Geb.Rose.toCSexp` spells it from `Rose`, as a label applied to
its arguments. The two disagree on the same tree, and the second is
shorter, carrying no constructor tags and no binary scaffolding. The
tree is `sampleAst` from `GebTests.Internal.ConcreteSyntax`, so the
spellings can be compared against the one that module pins.

The rest run the rose spelling as a concrete syntax in the sense
`Geb.Retraction` fixes — a `parse`/`print` pair satisfying the
retraction law, not a syntax over a second data model.
`Geb.Rose.parse_print` constrains the parser only on the printer's
output, so the assertions add the arity `sampleAst`'s rose form has
not, the fuel bound at which the child loop stops succeeding, the
spellings the parser accepts and the printer never emits, and the
rejection paths no theorem reaches.

## Main definitions

* `sampleWide`, `sampleLeaf` — a two-child rose node, which
  `sampleAst`'s rose form has not, and a childless one, which it has
  only below a node and not as the whole input.

## References

* [RFC9804]

## Tags

canonical S-expression, conformance, parser, test
-/

@[expose] public section

open Geb

/-! ## The factoring, evaluated -/

#guard Csexp.print sampleAst == CSexp.render sampleAst.toCSexp

#guard String.ofList (CSexp.render sampleAst.toCSexp)
    == "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"

/-! ## The two encodings differ

`Ast.printViaRose` composes the rose bijection with `Rose.toCSexp`, so
it encodes the same tree; it does not produce the same bytes. That it
encodes the same tree is `Ast.ofRose_toRose`, which inverts the
bijection the composite runs through and which
`GebTests.Internal.ConcreteSyntax` asserts. -/

#guard String.ofList (Ast.printViaRose sampleAst) == "(1:0(1:1(1:2)))"

#guard Ast.printViaRose sampleAst != Csexp.print sampleAst

/-! ## The rose spelling as a syntax

`Geb.Rose.parse_print` and `Geb.Ast.parseViaRose_printViaRose` state the
two retractions; the assertions below run them. `sampleAst`'s rose form
has one child at each of its two upper nodes and none at its lowest, so
it exercises the child loop at arity 1 and, below a node, at arity 0.
`sampleWide` supplies the arity it has not, and `sampleLeaf` the
position it has not: a childless node as the whole input, so that the
remainder `Geb.Rose.parse` requires to be empty is what the child loop
returns from its first step. -/

/-- A rose tree with a two-child node, which `sampleAst`'s rose form
has not. -/
def sampleWide : Rose 3 :=
  Rose.node 0 ![Rose.node 1 Fin.elim0, Rose.node 2 Fin.elim0]

/-- A childless rose node, whose spelling has an empty child list. -/
def sampleLeaf : Rose 3 := Rose.node 2 Fin.elim0

#guard Rose.parse 3 (Rose.print sampleAst.toRose) == some sampleAst.toRose

#guard Ast.parseViaRose 3 (Ast.printViaRose sampleAst) == some sampleAst

#guard String.ofList (Rose.print sampleWide) == "(1:0(1:1)(1:2))"

#guard Rose.parse 3 (Rose.print sampleWide) == some sampleWide

#guard String.ofList (Rose.print sampleLeaf) == "(1:2)"

#guard Rose.parse 3 (Rose.print sampleLeaf) == some sampleLeaf

/-! ## The child loop's bound

`Rose.parseAux` supplies its `Nat` in two roles at each layer,
undecremented as the child loop's bound and decremented as the child
parser's fuel, so at a node of `n` children it must be at least `n + 1`
and must exceed what each child needs. A node count satisfies both, and
here it is exact: `sampleWide` is three nodes and parses at three, not
at two. `Rose.parseAux_print` states the bound in terms of the printed
length instead, fifteen here, because `Rose.parse` supplies that number
in any case. -/

#guard (Rose.parseAux 3 3 (Rose.print sampleWide)).isSome
#guard (Rose.parseAux 3 2 (Rose.print sampleWide)).isNone

-- `Rose.parse` supplies the input length, so at empty input the fuel is
-- zero and `Rose.parseStep` is never reached. Given a unit of fuel it
-- is, and rejects: this is the only route to that branch.
#guard (Rose.parseAux 3 1 []).isNone

/-! ## Inputs the parser accepts but the printer never emits

Three, all inherited from the decimal layer this spelling shares with
the implemented one: `Geb.Csexp.digitsVal`, which `Rose.parseStep`
applies to a label atom's content, does not constrain that content's
spelling, and `Geb.Csexp.readNat` does not constrain the spelling of the
atom's length prefix.
`GebTests.Internal.ConcreteSyntax` records the same three for
`Geb.Csexp.parse`. The first runs `Geb.format`, whose idempotence
`Geb.Rose.format_idem` states without evaluating it. -/

-- A label atom carrying a leading zero, which `Geb.Csexp.decOf` never
-- writes.
#guard (format (Rose.parse 3) Rose.print (sexp (atom 2 ['0', '1']))).map
    String.ofList == some "(1:1)"

-- An empty label atom denotes label `0`, spelled `(1:0)` by the printer.
#guard Rose.parse 3 (sexp (atom 0 [])) == some (Rose.node 0 Fin.elim0)

-- A length prefix may carry leading zeros too, though [RFC9804]'s
-- `decimal` production forbids it: `Geb.Csexp.readNat` reads the digits
-- and takes their value.
#guard Rose.parse 3 (sexp (atomRaw ['0', '1'] ['0'])) == some (Rose.node 0 Fin.elim0)

/-! ## Rejection paths -/

-- Empty input.
#guard Rose.parse 3 [] == none

-- A leading character that is not `(`.
#guard Rose.parse 3 ('x' :: (Rose.print sampleLeaf).tail) == none

-- A missing closing parenthesis, so the child loop reaches the empty
-- input.
#guard Rose.parse 3 ('(' :: Csexp.printVerbatim ['2']) == none

-- A label atom whose content is not decimal.
#guard Rose.parse 3 (sexp (Csexp.printVerbatim ['x'])) == none

-- No label atom at all, which `Csexp.readVerbatim` rejects before
-- `Csexp.digitsVal` is reached.
#guard Rose.parse 3 (sexp []) == none

-- A child that is not an s-expression, which the child loop rejects
-- rather than reading as the end of the child list.
#guard Rose.parse 3 (sexp (Csexp.printVerbatim ['0'] ++ ['x'])) == none

-- A label at the alphabet's bound.
#guard Rose.parse 3 (sexp (Csexp.printVerbatim ['3'])) == none

-- Trailing input after a complete tree.
#guard Rose.parse 3 (Rose.print sampleWide ++ [')']) == none
