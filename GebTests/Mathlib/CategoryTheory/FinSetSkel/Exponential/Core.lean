/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Core

/-!
# Tests for the exponential core of `FinSetSkel`

A sample function on a product carrier, the index its exponential
encoding takes at a sample parameter, naturality of that encoding
along a sample reindexing of the parameter, and a morphism-level
transpose at a fixed universe with its entries.

## Tags

category, finite set, skeleton, exponential, encoding, naturality
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- A sample function on a product carrier, of exponent length `2`
and parameter length `3`. -/
def sampleSkelExpFun : Fin (2 * 3) → Fin 2 :=
  fun i ↦ ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩

/-- A sample reindexing of the parameter object. -/
def sampleSkelExpReindex : Fin 2 → Fin 3 := Fin.succ

/-- The exponential encoding of the sample function at a sample
parameter index. -/
theorem sampleSkelExpFun_encode :
    expEquivIdx 2 3 2 sampleSkelExpFun ⟨1, by decide⟩ = ⟨2, by decide⟩ := by
  decide

/-- Naturality of the exponential encoding at the sample function and
the sample reindexing. -/
theorem sampleSkelExpFun_naturality :
    expEquivIdx 2 2 2
        (fun i ↦ sampleSkelExpFun
          (Fin.pairC (Fin.divNatC i) (sampleSkelExpReindex (Fin.modNatC i)))) =
      expEquivIdx 2 3 2 sampleSkelExpFun ∘ sampleSkelExpReindex :=
  expEquivIdx_naturality 2 2 3 2 sampleSkelExpReindex sampleSkelExpFun

/-- The morphism-level transpose of the sample function, at exponent
length `2`, parameter length `3` and target length `2`, at a fixed
universe. Naming it gives the `GebMeta` axiom linter a declaration to
inspect. -/
def sampleSkelExpEquivHom : (mk 3 : FinSetSkel.{0}) ⟶ mk (2 ^ 2) :=
  expEquivHom 2 3 2 (Hom.ofVec (Vector.ofFnC sampleSkelExpFun))

/-- At each parameter index `t` the transpose encodes the function
`fun a ↦ sampleSkelExpFun (Fin.pairC a t)`, the entry at `a = 1`
being the low digit; its entries are read as naturals, the target
object's length not being a literal. -/
theorem sampleSkelExpEquivHom_toList :
    sampleSkelExpEquivHom.toVec.toList.map Fin.val = [1, 2, 1] := by
  decide
