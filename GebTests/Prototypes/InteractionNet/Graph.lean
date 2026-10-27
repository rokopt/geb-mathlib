/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphConfluence
public meta import Geb.Prototypes.InteractionNet.GraphConfluence -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Graph contraction tests

Replacing a unary active pair by a wire either joins its two external strands or closes
a wire loop, depending on the context. The principal wire consumed by the interaction
does not itself count as a closed loop. The tests also inspect finite ordinal packing.

## Tags

interaction net, graph, contraction, boundary, closed wire, regression test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests.Graph

open scoped FinEnum

/-- A unary signature used to test both principal and auxiliary wires. -/
def arity (_ : Unit) : ℕ := 1

/-- Two unary cells joined at both their principal and auxiliary ports. -/
def closedPair : PortNet arity (fun _ : Bool ↦ ()) Empty where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl e => nomatch e
        | .inr ⟨c, p⟩ => .inr ⟨!c, p⟩
      involutive := by
        rintro (e | ⟨c, p⟩)
        · cases e
        · cases c <;> rfl
      fixedPointFree := by
        rintro (e | ⟨c, p⟩) h
        · cases e
        · have hc : (!c) = c := congrArg Sigma.fst (Sum.inr.inj h)
          cases c <;> cases hc }
  loops := 0

/-- The wire-only replacement of two unary cells. -/
def wire : PortNet arity (fun e : Empty ↦ nomatch e) (Fin 1 ⊕ Fin 1) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl (.inl i) => .inl (.inr i)
        | .inl (.inr i) => .inl (.inl i)
        | .inr ⟨e, _⟩ => nomatch e
      involutive := by
        rintro ((i | i) | ⟨e, _⟩) <;> first | rfl | cases e
      fixedPointFree := by
        rintro ((i | i) | ⟨e, _⟩) h <;> first | cases h | cases e }
  loops := 0

/-- The selected principal wire of the closed unary pair. -/
theorem closed_active : closedPair.Active false true := rfl

#guard (closedPair.contract closed_active wire).loops = 1

/-- A unary pair with its auxiliary ports connected to two external positions. -/
def openPartner : Endpoint arity (fun _ : Bool ↦ ()) Bool →
    Endpoint arity (fun _ : Bool ↦ ()) Bool
  | .inl c => .inr ⟨c, 1⟩
  | .inr ⟨c, p⟩ => Fin.cases (.inr ⟨!c, 0⟩) (fun _ ↦ .inl c) p

/-- The open pair's partner function pairs all external and cell endpoints. -/
theorem openPartner_involutive : Function.Involutive openPartner := by
  rintro (c | ⟨c, p⟩)
  · rfl
  · refine Fin.cases ?_ (fun q ↦ ?_) p
    · cases c <;> rfl
    · change Fin 1 at q
      have hq : q = 0 := Fin.eq_zero q
      subst q
      rfl

/-- None of the open pair's endpoints is wired to itself. -/
theorem openPartner_ne (p : Endpoint arity (fun _ : Bool ↦ ()) Bool) : openPartner p ≠ p := by
  rintro h
  rcases p with c | ⟨c, p⟩
  · cases h
  · revert h
    refine Fin.cases ?_ (fun q h ↦ ?_) p
    · intro h
      have hc : (!c) = c := congrArg Sigma.fst (Sum.inr.inj h)
      cases c <;> cases hc
    · cases h

/-- The open unary pair, together with pre-existing closed wire components. -/
def openPair : PortNet arity (fun _ : Bool ↦ ()) Bool :=
  ⟨⟨openPartner, openPartner_involutive, openPartner_ne⟩, 3⟩

/-- The open unary pair's principal ports form an active pair. -/
theorem open_active : openPair.Active false true := rfl

#guard (openPair.contract open_active wire).loops = 3
#guard (openPair.contract open_active wire).wiring.partner (.inl false) = .inl true
#guard (openPair.contract open_active wire).wiring.partner (.inl true) = .inl false

/-- A closed pair with finite ordinal cells and no external endpoints. -/
def indexedPair : PortNet arity (fun _ : Fin 2 ↦ ()) (Fin 0) where
  wiring :=
    { partner := fun p ↦ match p with
        | .inl e => Fin.elim0 e
        | .inr ⟨c, p⟩ => .inr ⟨Fin.rev c, p⟩
      involutive := by
        rintro (e | ⟨c, p⟩)
        · exact Fin.elim0 e
        · simp only [Fin.rev_rev]
      fixedPointFree := by
        rintro (e | ⟨c, p⟩) h
        · exact Fin.elim0 e
        · have hc := congrArg (fun q : CellPort arity (fun _ : Fin 2 ↦ ()) ↦ q.1.val)
            (Sum.inr.inj h)
          change 2 - (c.val + 1) = c.val at hc
          omega }
  loops := 0

/-- The finite ordinal pair has its principal ports connected. -/
theorem indexed_active : indexedPair.Active 0 1 := rfl

/-- Pack the closed pair's contraction after enumerating its surviving cells. -/
def packed : FiniteNet arity 0 :=
  letI := PortNet.subtypeEnum (fun c : Fin 2 ↦ c ≠ 0 ∧ c ≠ 1)
  letI : FinEnum Empty :=
    { card := 0
      equiv :=
        { toFun := Empty.elim
          invFun := Fin.elim0
          left_inv := fun e ↦ nomatch e
          right_inv := fun i ↦ Fin.elim0 i }
      decEq := inferInstance }
  FiniteNet.pack (indexedPair.contract indexed_active wire)

#guard packed.1 = 0
#guard packed.net.loops = 1

end Geb.InteractionNet.Tests.Graph

end
