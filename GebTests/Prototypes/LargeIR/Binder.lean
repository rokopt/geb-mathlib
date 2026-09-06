/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.LargeIR.Basic
public import Geb.Prototypes.LargeIR.Binder -- shake: keep

/-!
# Tests for the binder obstruction

Exercises `Geb.Prototypes.LargeIR.Binder`: the presheaf with one code and `n`
terms computes, the dependent-product former's value at it is the functions
`Fin n → Fin n` and its two bijections compute on a function, and the
obstruction theorem applies to the transcription of a slice polynomial functor
once its values are compared with the former's.

## Tags

prototype, universe, dependent product, walking arrow, reduction test
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec GebProto.LargeIR

namespace LargeIRTest

-- The presheaf with one code and three terms.
example : (termsPsh 3).obj ⟨0⟩ = Unit := rfl
example : (termsPsh 3).obj ⟨1⟩ = Fin 3 := rfl
example : (termsPsh 3).map waHom.op (2 : Fin 3) = () := rfl

/-- The product former's element at two terms given by the swap. -/
def swapElem : PiFormerValue (termsPsh 2) := (piFormerEquiv 2).symm fun i ↦ i + 1

-- Its family of codes is the one code, and its terms are the swapped ones.
example : swapElem.2.1 ⟨(0 : Fin 2), rfl⟩ = () := rfl
example : (swapElem.2.2 ⟨(0 : Fin 2), rfl⟩).1 = (1 : Fin 2) := rfl
example : (swapElem.2.2 ⟨(1 : Fin 2), rfl⟩).1 = (0 : Fin 2) := rfl
example : piFormerEquiv 2 swapElem = fun i ↦ i + 1 := (piFormerEquiv 2).apply_symm_apply _

/-- No family of bijections identifies the transcription's level-`1` values
with the product former's. -/
theorem piBoolObstruction :
    (∀ n : ℕ, { x : (arrowPsh piBool).obj (termsPsh n) // (arrowPsh piBool).q x.shape = 1 } ≃
      PiFormerValue (termsPsh n)) → False :=
  not_piFormer (arrowPsh piBool)

end LargeIRTest
