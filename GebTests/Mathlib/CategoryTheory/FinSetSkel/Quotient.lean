/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient
public meta import Geb.Mathlib.CategoryTheory.FinSetSkel.Quotient  -- shake: keep

/-!
# Tests for the coequalizer of a parallel pair in `FinSetSkel`

A worked coequalizer, computed. With `X` of length 3 and `Y` of
length 4, the pair generates the edges `(0,1)`, `(1,2)` and the
reflexive `(3,3)`, so the classes are `{0,1,2}` and `{3}`. What is
asserted is the number of classes and the partition the projection
induces; which representative each class gets is fixed by union by
rank, an internal of Batteries' algorithm, and is not asserted.

The two facts about `desc` also follow from `comp_π` and `π_desc` as
proofs; asserting them by computation is what exercises the
algorithm. Assertions are `#guard` for the reason recorded in the
union-find test module: nothing built from `UnionFind.union` or
`rootD` reduces in the kernel.

The objects are `abbrev`s, not `def`s, so that `Y.len` reduces where a
numeral at `Fin Y.len` needs it to. Each assertion goes through a
locally declared wrapper.

## Tags

category, finite set, coequalizer, test
-/

@[expose] public section

open CategoryTheory

/-- The domain of the sample parallel pair. -/
abbrev coeqDom : FinSetSkel.{0} := ⟨3⟩

/-- The codomain of the sample parallel pair. -/
abbrev coeqCod : FinSetSkel.{0} := ⟨4⟩

/-- The first leg of the sample parallel pair. -/
def coeqF : coeqDom ⟶ coeqCod :=
  FinSetSkel.Hom.ofVec ⟨#[0, 1, 3], rfl⟩

/-- The second leg of the sample parallel pair. -/
def coeqG : coeqDom ⟶ coeqCod :=
  FinSetSkel.Hom.ofVec ⟨#[1, 2, 3], rfl⟩

/-- The union-find the sample pair induces. -/
def coeqV : Batteries.UnionFind.Sized coeqCod.len :=
  FinSetSkel.Quotient.unionFind coeqF coeqG

/-- The number of classes. -/
def coeqClasses : ℕ := FinSetSkel.Quotient.len coeqV

#guard coeqClasses == 2

/-- The projection of the sample pair. -/
def coeqPi : coeqCod ⟶ FinSetSkel.Quotient.obj coeqCod coeqV :=
  FinSetSkel.Quotient.π coeqCod coeqV

/-- The class of a sample index, as a `Nat`. -/
def coeqPiAt (j : Fin coeqCod.len) : ℕ := (coeqPi.toVec.get j).val

#guard coeqPiAt 0 == coeqPiAt 1
#guard coeqPiAt 1 == coeqPiAt 2
#guard coeqPiAt 0 != coeqPiAt 3

/-- A morphism coequalizing the sample pair. -/
def coeqH : coeqCod ⟶ (⟨2⟩ : FinSetSkel.{0}) :=
  FinSetSkel.Hom.ofVec ⟨#[0, 0, 0, 1], rfl⟩

/-- Whether the sample morphism coequalizes the pair. -/
def coeqCoequalizes : Bool := (coeqF ≫ coeqH) == (coeqG ≫ coeqH)

/-- Whether the factorisation through the projection recovers it. -/
def coeqFactors : Bool :=
  (coeqPi ≫ FinSetSkel.Quotient.desc coeqCod coeqV coeqH) == coeqH

#guard coeqCoequalizes
#guard coeqFactors
