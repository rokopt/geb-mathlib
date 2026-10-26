/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringGlue
public import Geb.Mathlib.Data.FinEnum
public meta import Geb.Prototypes.InteractionNet.WiringGlue -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Boundary gluing tests

These finite examples distinguish gluing that closes a single cycle, two independent
closed wires, and a chain that leaves an external wire. Both orders of the cuts are
executed. The tests inspect the resulting partners and closed-wire counts.

## Tags

interaction net, gluing, closed wire, regression test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests.Wiring

open scoped FinEnum

/-- A family of independent wires joining their false and true endpoints. -/
def strands (I : Type*) : Wiring (Bool × I) where
  partner p := (!p.1, p.2)
  involutive p := by cases p with | mk b i => cases b <;> rfl
  fixedPointFree p h := by
    rcases p with ⟨b, i⟩
    have hb : (!b) = b := congrArg Prod.fst h
    cases b <;> cases hb

/-- The two cuts across a square, which close its one wire cycle. -/
def squareCuts : Bool × Bool ↪ Bool × Bool :=
  .refl _

#guard (Wiring.glue squareCuts [false, true] (strands Bool, 0)).2 = 1
#guard (Wiring.glue squareCuts [true, false] (strands Bool, 0)).2 = 1
#guard (Wiring.glue squareCuts [false, true] (strands Bool, 0)).1.partner (false, false) =
  (false, true)

#guard (Wiring.glue (.refl _) [false, true] (strands Bool, 3)).2 = 4
#guard (Wiring.glue squareCuts [false, true] ((strands Bool).map (Equiv.prodComm _ _), 3)).2 =
  5
#guard (Wiring.glue squareCuts [true, false] ((strands Bool).map (Equiv.prodComm _ _), 3)).2 =
  5

/-- Join three consecutive strands by cutting their two adjoining endpoint pairs. -/
def chainCuts : Bool × Bool ↪ Bool × Fin 3 where
  toFun p := match p with
    | (false, false) => (true, 0)
    | (false, true) => (false, 1)
    | (true, false) => (true, 1)
    | (true, true) => (false, 2)
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

#guard (Wiring.glue chainCuts [false, true] (strands (Fin 3), 0)).2 = 0
#guard (Wiring.glue chainCuts [true, false] (strands (Fin 3), 0)).2 = 0
#guard (Wiring.glue chainCuts [false, true] (strands (Fin 3), 0)).1.partner (false, 0) =
  (true, 2)
#guard (Wiring.glue chainCuts [true, false] (strands (Fin 3), 0)).1.partner (true, 2) =
  (false, 0)

end Geb.InteractionNet.Tests.Wiring

end
