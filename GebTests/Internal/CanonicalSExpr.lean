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
its arguments. The two disagree on the same tree, and the second is much
the shorter, since it carries no constructor tags and no binary
scaffolding. The tree is `sampleAst` from
`GebTests.Internal.ConcreteSyntax`, so the spellings can be compared
against the one that module pins.

## References

* [RFC9804]

## Tags

canonical S-expression, conformance, test
-/

@[expose] public section

open Geb

/-! ## The factoring, evaluated -/

#guard Csexp.print sampleAst == CSexp.render sampleAst.toCSexp

#guard String.ofList (CSexp.render sampleAst.toCSexp)
    == "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"

/-! ## The two encodings differ

`Ast.printViaRose` composes the rose bijection with `Rose.toCSexp`, so
it encodes the same tree; it does not produce the same bytes. -/

#guard String.ofList (Ast.printViaRose sampleAst) == "(1:0(1:1(1:2)))"

#guard Ast.printViaRose sampleAst != Csexp.print sampleAst

-- Both spellings determine the same tree: the rose one because
-- `Ast.ofRose_toRose` inverts the bijection it is composed with.
#guard Ast.ofRose sampleAst.toRose == sampleAst
