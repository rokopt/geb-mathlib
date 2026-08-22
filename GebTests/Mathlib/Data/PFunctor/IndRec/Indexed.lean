/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Indexed

/-!
# Tests for codes for small indexed induction-recursion

`rfl` tests reading back the direct interpretation `IIR.interp` and the
reduction `IIR.toIR` at each code constructor.

## Tags

indexed induction-recursion, inductive-recursive
-/

@[expose] public section

open CategoryTheory IndRec

/-- A decoding family over `Bool`: both indices decode to natural
numbers. -/
@[reducible] def testIIRDec : Bool → Type := fun _ ↦ Nat

/-- A closed indexed code: one recursive field at the input index `true`,
landing at the output index `false` and decoding to that field's decoded
value incremented. -/
def testIIRCode : IIR.{0, 0, 0, 0, 0, 0} Bool testIIRDec Bool testIIRDec :=
  IIR.delta1 Bool testIIRDec Bool testIIRDec true fun n ↦
    IIR.iota Bool testIIRDec Bool testIIRDec false (n + 1)

-- The nodes of the interpretation at the output index the code lands at:
-- the single recursive field, then the proof that the index is the one
-- asked for.
example (G : IIR.FamSlice.{0, 0} Bool testIIRDec) (m : Bool) :
    (IIR.interp Bool testIIRDec Bool testIIRDec testIIRCode G m).1 =
      Σ _ : PUnit.{1} → (G true).1, ULift (PLift (false = m)) :=
  rfl

-- The node decodes to the recursive field's decoded value incremented.
example (G : IIR.FamSlice.{0, 0} Bool testIIRDec) (ig : PUnit.{1} → (G true).1) :
    (IIR.interp Bool testIIRDec Bool testIIRDec testIIRCode G false).2
        ⟨ig, ULift.up (PLift.up rfl)⟩ =
      (G true).2 (ig PUnit.unit) + 1 :=
  rfl

-- The reduction carries a constant code across unchanged, pairing the
-- output index with the decoding.
example (m : Bool) (ev : Nat) :
    IIR.toIR Bool testIIRDec Bool testIIRDec
        (IIR.iota Bool testIIRDec Bool testIIRDec m ev) =
      IR.iota (Σ i, testIIRDec i) (Σ j, testIIRDec j) ⟨m, ev⟩ :=
  rfl

-- The reduction carries a dependent sum across unchanged.
example (A : Type) (c : A → IIR.{0, 0, 0, 0, 0, 0} Bool testIIRDec Bool testIIRDec) :
    IIR.toIR Bool testIIRDec Bool testIIRDec
        (IIR.sigma Bool testIIRDec Bool testIIRDec A c) =
      IR.sigma (Σ i, testIIRDec i) (Σ j, testIIRDec j) A
        (fun a ↦ IIR.toIR Bool testIIRDec Bool testIIRDec (c a)) :=
  rfl

-- The reduction turns a dependent product's index assignment into a
-- dependent sum over the pointwise condition that the recursive fields
-- landed where the assignment demands.
example (P : Type) (ix : P → Bool)
    (c : ((p : P) → testIIRDec (ix p)) →
      IIR.{0, 0, 0, 0, 0, 0} Bool testIIRDec Bool testIIRDec) :
    IIR.toIR Bool testIIRDec Bool testIIRDec
        (IIR.delta Bool testIIRDec Bool testIIRDec P ix c) =
      IR.delta (Σ i, testIIRDec i) (Σ j, testIIRDec j) P (fun iD ↦
        IR.sigma (Σ i, testIIRDec i) (Σ j, testIIRDec j)
          (ULift (PLift (∀ p, (iD p).1 = ix p))) fun h ↦
            IIR.toIR Bool testIIRDec Bool testIIRDec
              (c fun p ↦ h.down.down p ▸ (iD p).2)) :=
  rfl
