/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Mono
public import Geb.Mathlib.Data.Vector.NodupEquivFin
public import Geb.Mathlib.Data.Vector.OfFn

/-!
# The subobject classifier of `FinSetSkel`, over vectors

The classifying object is the object of length 2 and the
characteristic morphism of a monomorphism sends the members of its
image to `1` and everything else to `0`. `truth` picks the index `1`
in `Classifier/Instance.lean`; the two modules fix the orientation
jointly and each states it.

The orientation follows mathlib's own: `finTwoEquiv` is
`fun i ↦ i == 1`, and `Presheaf.truth` and `Sheaf.truth`, the two
classifier instances mathlib builds, both pick the maximal sieve.
With `truth = 1` the characteristic morphism is the indicator of
membership and every bridge to `Bool`, `decide` or `Prop` is
`finTwoEquiv` composed with nothing; with `truth = 0` each such
bridge carries a negation and the normal forms on the two sides stop
matching.

The characteristic vector is scattered in one pass over a
`Vector.replicate`, not written index-by-index over a membership
test, which would rebuild and rescan the image per index.

## Main definitions

* `FinSetSkel.Classifier.chi` — the characteristic morphism.
* `FinSetSkel.Classifier.pullbackLift` — the factorisation through a
  monomorphism of a morphism whose image it contains.

## Main statements

* `FinSetSkel.Classifier.get_scatterOne_eq_one`,
  `FinSetSkel.Classifier.get_scatterOne_eq_one_of` — the pass writes
  `1` at the listed indices and nowhere else.
* `FinSetSkel.Classifier.chiVec_get_eq_one_iff` — the characteristic
  vector is the indicator of the image.
* `FinSetSkel.Classifier.chi_uniq` — a morphism with the same
  indicator is the characteristic morphism.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, subobject classifier, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel.Classifier

/-- One pass writing `1` at each listed index, generalised over the
starting vector. -/
def scatterOne {n : ℕ} (L : List (Fin n)) (v : Vector (Fin 2) n) :
    Vector (Fin 2) n :=
  L.foldl (fun w j ↦ w.set j.val 1 j.isLt) v

/-- The pass writes `1` only at listed indices. -/
theorem get_scatterOne_eq_one {n : ℕ} (L : List (Fin n)) (j : Fin n)
    (v : Vector (Fin 2) n) (h : (scatterOne L v).get j = 1) :
    j ∈ L ∨ v.get j = 1 :=
  L.rec (motive := fun L ↦ ∀ (v : Vector (Fin 2) n),
      (scatterOne L v).get j = 1 → j ∈ L ∨ v.get j = 1)
    (fun _ h ↦ Or.inr h)
    (fun a L ih v h ↦ by
      rcases ih (v.set a.val 1 a.isLt) h with hm | hs
      · exact Or.inl (List.mem_cons_of_mem a hm)
      · rcases Nat.decEq a.val j.val with hne | he
        · refine Or.inr ?_
          rw [Vector.get_eq_getElem] at hs
          rw [Vector.getElem_set_ne a.isLt j.isLt hne] at hs
          rwa [Vector.get_eq_getElem]
        · exact Or.inl (List.mem_cons.mpr (Or.inl (Fin.ext he).symm)))
    v h

/-- The pass writes `1` at every listed index, and preserves a `1`
already present. -/
theorem get_scatterOne_eq_one_of {n : ℕ} (L : List (Fin n))
    (j : Fin n) (v : Vector (Fin 2) n) (h : j ∈ L ∨ v.get j = 1) :
    (scatterOne L v).get j = 1 :=
  L.rec (motive := fun L ↦ ∀ (v : Vector (Fin 2) n),
      j ∈ L ∨ v.get j = 1 → (scatterOne L v).get j = 1)
    (fun _ h ↦ h.resolve_left List.not_mem_nil)
    (fun a L ih v h ↦ by
      refine ih (v.set a.val 1 a.isLt) ?_
      have hset : a = j → (v.set a.val 1 a.isLt).get j = 1 := by
        rintro rfl
        rw [Vector.get_eq_getElem]
        exact Vector.getElem_set_self _
      rcases h with hm | hv
      · rcases List.mem_cons.mp hm with hja | hjL
        · exact Or.inr (hset hja.symm)
        · exact Or.inl hjL
      · refine Or.inr ?_
        rcases Nat.decEq a.val j.val with hne | he
        · rw [Vector.get_eq_getElem] at hv
          rw [Vector.get_eq_getElem, Vector.getElem_set_ne a.isLt j.isLt hne]
          exact hv
        · exact hset (Fin.ext he))
    v h

/-- The pass writes `1` at every listed index. -/
theorem get_scatterOne_of_mem {n : ℕ} (L : List (Fin n)) (j : Fin n)
    (hj : j ∈ L) (v : Vector (Fin 2) n) : (scatterOne L v).get j = 1 :=
  get_scatterOne_eq_one_of L j v (Or.inl hj)

variable {U X : FinSetSkel.{u}}

/-- The characteristic vector of a monomorphism: `1` on its image,
`0` elsewhere. -/
def chiVec (m : U ⟶ X) : Vector (Fin 2) X.len :=
  scatterOne m.toVec.toList (Vector.replicate X.len 0)

/-- The characteristic morphism of a monomorphism. -/
def chi (m : U ⟶ X) : X ⟶ mk 2 := Hom.ofVec (chiVec m)

/-- The characteristic morphism looks up the characteristic
vector. -/
@[simp] theorem chi_get (m : U ⟶ X) (j : Fin X.len) :
    (chi m).toVec.get j = (chiVec m).get j := by
  rw [chi, Hom.toVec_ofVec]

/-- The characteristic vector is the indicator of the image. -/
theorem chiVec_get_eq_one_iff (m : U ⟶ X) (j : Fin X.len) :
    (chiVec m).get j = 1 ↔ j ∈ m.toVec.toList := by
  constructor
  · intro h
    refine (get_scatterOne_eq_one _ _ _ h).resolve_right ?_
    simp only [Vector.get_eq_getElem, Vector.getElem_replicate]
    decide
  · intro hj
    exact get_scatterOne_of_mem _ _ hj _

/-- The inversion of an injective vector recovers the vector's
lookup. -/
theorem invOfInjective_apply {n k : ℕ} (v : Vector (Fin n) k)
    (h : Function.Injective v.get) (i : Fin k) :
    ((Vector.invOfInjective v h) i).val = v.get i := rfl

/-- The factorisation through a monomorphism of a morphism whose
image it contains. -/
def pullbackLift (m : U ⟶ X) (hm : Function.Injective m.toVec.get)
    {Z : FinSetSkel.{u}} (z : Z ⟶ X)
    (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) : Z ⟶ U :=
  let e := Vector.invOfInjective m.toVec hm
  Hom.ofVec (Vector.ofFnC fun t ↦ e.symm ⟨z.toVec.get t, hz t⟩)

/-- The factorisation composes back to the original morphism. -/
theorem pullbackLift_comp (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList) :
    pullbackLift m hm z hz ≫ m = z :=
  hom_ext fun t ↦ by
    simp only [comp_get, pullbackLift, Hom.toVec_ofVec, Vector.get_ofFnC]
    rw [← invOfInjective_apply m.toVec hm, Equiv.apply_symm_apply]

/-- The factorisation through a monomorphism is unique. -/
theorem pullbackLift_uniq (m : U ⟶ X)
    (hm : Function.Injective m.toVec.get) {Z : FinSetSkel.{u}}
    (z : Z ⟶ X) (hz : ∀ t, z.toVec.get t ∈ m.toVec.toList)
    (n : Z ⟶ U) (hn : n ≫ m = z) : n = pullbackLift m hm z hz :=
  hom_ext fun t ↦ hm (by
    have h : (n ≫ m).toVec.get t = (pullbackLift m hm z hz ≫ m).toVec.get t := by
      rw [hn, pullbackLift_comp]
    simpa only [comp_get] using h)

/-- The characteristic morphism is `1` on the image. -/
theorem chi_comp_eq (m : U ⟶ X) (i : Fin U.len) :
    (chi m).toVec.get (m.toVec.get i) = 1 := by
  rw [chi_get]
  exact (chiVec_get_eq_one_iff m _).mpr (by simp [Vector.get_eq_getElem])

/-- A morphism whose fibre over `1` is the image is the
characteristic morphism. -/
theorem chi_uniq (m : U ⟶ X) (χ' : X ⟶ mk 2)
    (h : ∀ j, χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList) :
    χ' = chi m :=
  hom_ext fun j ↦ by
    rw [chi_get]
    by_cases hj : χ'.toVec.get j = 1
    · rw [hj]
      exact ((chiVec_get_eq_one_iff m j).mpr ((h j).mp hj)).symm
    · have h1 : (chiVec m).get j ≠ 1 :=
        fun hc ↦ hj ((h j).mpr ((chiVec_get_eq_one_iff m j).mp hc))
      -- neither is `1`, so in `Fin 2` both are `0`
      have h2 : (χ'.toVec.get j).val ≠ 1 := fun hc ↦ hj (Fin.val_injective hc)
      have h3 : ((chiVec m).get j).val ≠ 1 := fun hc ↦ h1 (Fin.val_injective hc)
      have h4 : (χ'.toVec.get j).val < 2 := (χ'.toVec.get j).isLt
      have h5 : ((chiVec m).get j).val < 2 := ((chiVec m).get j).isLt
      exact Fin.val_injective (by omega)

end FinSetSkel.Classifier
