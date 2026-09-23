/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Bootstrap -- shake: keep
public meta import Geb.Prototypes.Bootstrap -- shake: keep

set_option doc.verso true in
/-!
# Bootstrap certificate examples

Executable derivations compose two reductions and reverse their conclusion.
Malformed syntax, unsupported tags, wrong arities, invalid premises, incorrect
claims, and incompatible transitivity premises exercise rejection.

## Main definitions

* {lit}`first`, {lit}`middle`, and {lit}`last` form a two-step computation.
* {lit}`proof` composes its reduction certificates.

## Tags

bootstrap, proof certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Bootstrap.Tests

open Triage

/-- A pending application with a reducible function. -/
def first : Expr := .app (.app (.value Value.leaf) (.value Value.leaf)) (.value Value.leaf)

/-- The first absorption has produced a stem in function position. -/
def middle : Expr := .app (.value (.stem .leaf)) (.value .leaf)

/-- The second absorption has produced a fork. -/
def last : Expr := .value (.fork .leaf .leaf)

/-- A certificate for one reduction of a supplied expression. -/
def reduction (e : Expr) : Certificate := RoseTree.node (1, Oitavem.rank e.encode) []

/-- Transitivity composes the two computation steps. -/
def proof : Certificate := RoseTree.node (3, 0) [reduction first, reduction middle]

#guard check proof first.encode last.encode
#guard check (RoseTree.node (2, 0) [proof]) last.encode first.encode
#guard check (RoseTree.node (0, Oitavem.rank first.encode) []) first.encode first.encode
#guard !check proof first.encode middle.encode
#guard infer (RoseTree.node (0, Oitavem.rank []) []) = none
#guard infer (RoseTree.node (1, Oitavem.rank []) []) = none
#guard infer (reduction last) = none
#guard infer (RoseTree.node (255, 0) []) = none
#guard infer (RoseTree.node (2, 1) [proof]) = none
#guard infer (RoseTree.node (2, 0) []) = none
#guard infer (RoseTree.node (1, Oitavem.rank first.encode) [proof]) = none
#guard infer (RoseTree.node (3, 0) [reduction first, reduction first]) = none
#guard infer (RoseTree.node (3, 0) [proof, RoseTree.node (255, 0) []]) = none
#guard Oitavem.rank (Oitavem.unrank (2 ^ 200 + 17)) = 2 ^ 200 + 17

end Geb.Bootstrap.Tests

end
