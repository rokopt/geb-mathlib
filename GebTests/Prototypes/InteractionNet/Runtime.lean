/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphRuntimeAdequacy
public import GebTests.Prototypes.InteractionNet.Graph
public meta import Geb.Prototypes.InteractionNet.GraphRuntimeAdequacy -- shake: keep
public meta import GebTests.Prototypes.InteractionNet.Graph -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Array graph runtime tests

Unary wire rules exercise loop creation and cell deletion. Two independent pairs are
executed in opposite orders. A zero-arity replacement allocates fresh inert cells and
checks their stored symbols and wires. Bounded runs distinguish exhausted fuel from a
reached normal form.

## Tags

interaction net, runtime, array, allocation, schedule, regression test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests.Runtime

open scoped FinEnum

/-- Unary control and data cells. -/
def unary (_ : Bool) : ℕ := 1

/-- A wire-only replacement with no internal cells. -/
def wire : PortNet unary (Fin.elim0 : Fin 0 → Bool) (Fin 1 ⊕ Fin 1) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl (.inl i) => .inl (.inr i)
        | .inl (.inr i) => .inl (.inl i)
        | .inr ⟨e, _⟩ => Fin.elim0 e
      involutive := by
        rintro ((i | i) | ⟨e, _⟩) <;> first | rfl | exact Fin.elim0 e
      fixedPointFree := by
        rintro ((i | i) | ⟨e, _⟩) h <;> first | cases h | exact Fin.elim0 e }
  loops := 0

/-- The unary rule joins the two auxiliary strands of a true/false active pair. -/
def wireSystem : PortSystem unary where
  rule a b := match a, b with
    | true, false => some ⟨0, Fin.elim0, wire⟩
    | _, _ => none
  oriented := by
    intro a b r h
    cases a <;> cases b <;> first | rfl | cases h

/-- A closed unary active pair with distinct control and data symbols. -/
def pair : FiniteNet unary 0 :=
  ⟨2, fun c ↦ c.val == 0, ⟨Graph.indexedPair.wiring, 0⟩⟩

/-- A closed pair in executable array form. -/
def start : GraphRuntime.State unary 0 := GraphRuntime.encode pair

#guard (GraphRuntime.run wireSystem 0 start).isNone
#guard (GraphRuntime.run wireSystem 1 start).map (fun n ↦ n.1) = some 0
#guard (GraphRuntime.run wireSystem 1 start).map (fun n ↦ n.2.2.loops) = some 1
#guard (GraphRuntime.run wireSystem 5 start).map (fun n ↦ n.2.2.loops) = some 1
#guard (GraphRuntime.stepAt wireSystem start (1 : Fin 2) (0 : Fin 2)).isNone

/-- Two disjoint unary active pairs, each also joined at its auxiliary ports. -/
def doublePair : PortNet unary (fun c : Fin 4 ↦ decide (c.val < 2)) (Fin 0) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl e => Fin.elim0 e
        | .inr ⟨c, p⟩ => .inr ⟨c.rev, p⟩
      involutive := by
        rintro (e | ⟨c, p⟩)
        · exact Fin.elim0 e
        · exact congrArg Sum.inr (congrArg
            (fun d ↦ (⟨d, p⟩ : CellPort unary (fun c : Fin 4 ↦ decide (c.val < 2))))
            (Fin.rev_rev c))
      fixedPointFree := by
        rintro (e | ⟨c, p⟩) h
        · exact Fin.elim0 e
        · have hc := congrArg
            (fun q : CellPort unary (fun c : Fin 4 ↦ decide (c.val < 2)) ↦ q.1.val)
            (Sum.inr.inj h)
          change 4 - (c.val + 1) = c.val at hc
          omega }
  loops := 2

/-- The two-pair graph's initial runtime state. -/
def doubleStart : GraphRuntime.State unary 0 :=
  GraphRuntime.encode ⟨4, _, doublePair⟩

/-- Finish a two-pair test after selecting its first pair explicitly. -/
def finish (first : Fin 4 × Fin 4) : Option (GraphRuntime.State unary 0) :=
  (GraphRuntime.stepAt wireSystem doubleStart first.1 first.2).bind
    (GraphRuntime.run wireSystem 1)

#guard (GraphRuntime.run wireSystem 1 doubleStart).isNone
#guard (GraphRuntime.run wireSystem 2 doubleStart).map (fun n ↦ n.1) = some 0
#guard (GraphRuntime.run wireSystem 2 doubleStart).map (fun n ↦ n.2.2.loops) = some 4
#guard (finish (0, 3)).map (fun n ↦ (n.1, n.2.2.loops)) = some (0, 4)
#guard (finish (1, 2)).map (fun n ↦ (n.1, n.2.2.loops)) = some (0, 4)

/-- A signature of zero-arity agents, including one inert replacement symbol. -/
def nullary (_ : Fin 3) : ℕ := 0

/-- A pair of zero-arity cells carrying any selected symbols. -/
def nullaryPair (label : Fin 2 → Fin 3) : PortNet nullary label (Fin 0) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl e => Fin.elim0 e
        | .inr ⟨c, p⟩ => .inr ⟨c.rev, p⟩
      involutive := by
        rintro (e | ⟨c, p⟩)
        · exact Fin.elim0 e
        · exact congrArg Sum.inr
            (congrArg (fun d ↦ (⟨d, p⟩ : CellPort nullary label)) (Fin.rev_rev c))
      fixedPointFree := by
        rintro (e | ⟨c, p⟩) h
        · exact Fin.elim0 e
        · have hc := congrArg (fun q : CellPort nullary label ↦ q.1.val) (Sum.inr.inj h)
          change 2 - (c.val + 1) = c.val at hc
          omega }
  loops := 0

/-- Identify the empty auxiliary boundary with the empty external boundary. -/
def emptyBoundary : Fin 0 ≃ Fin 0 ⊕ Fin 0 where
  toFun := Fin.elim0
  invFun p := p.elim Fin.elim0 Fin.elim0
  left_inv := fun p ↦ Fin.elim0 p
  right_inv p := by cases p with | inl p | inr p => exact Fin.elim0 p

/-- Replace the 0/1 pair by newly allocated cells bearing the inert symbol 2. -/
def allocateSystem : PortSystem nullary where
  rule a b := if a = 0 ∧ b = 1 then
      some ⟨2, fun _ ↦ 2, (nullaryPair (fun _ ↦ 2)).reboundary emptyBoundary⟩
    else none
  oriented := by
    intro a b r h
    split at h
    · rename_i ha
      rcases ha with ⟨rfl, rfl⟩
      simp
    · cases h

/-- The allocating rule's input pair. -/
def allocateStart : GraphRuntime.State nullary 0 :=
  GraphRuntime.encode ⟨2, fun c ↦ ⟨c.val, Nat.lt_trans c.isLt (by decide)⟩, nullaryPair _⟩

#guard (GraphRuntime.run allocateSystem 0 allocateStart).isNone
#guard (GraphRuntime.run allocateSystem 1 allocateStart).map (fun n ↦ n.1) = some 2
#guard (GraphRuntime.run allocateSystem 1 allocateStart).map (fun n ↦ n.2.2.loops) = some 0
#guard (GraphRuntime.run allocateSystem 1 allocateStart).map
  (fun n ↦ (List.finRange n.1).map n.2.1) = some [2, 2]
#guard (GraphRuntime.run allocateSystem 1 allocateStart).map
  (fun n ↦ n.2.2.wiring.links.toArray.map Fin.val) = some #[1, 0]

end Geb.InteractionNet.Tests.Runtime

end
