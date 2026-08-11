/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases

/-!
# The fold at a carrier with a bit encoding

The catamorphism of a list of bits at a carrier admitting a `p`-bit encoding,
as an instance of the scan combinator. The carrier is arbitrary; its
finiteness enters only through the encoding.

## Main definitions

* `Cobham.foldStep` — the step, a dispatch on the encoded state.
* `Cobham.foldSem` — the scan's meaning at the step and the encoded base.
* `Cobham.fold`, `Cobham.foldOf` — the fold as an expression of `C`, and at
  its declared arity.

## Main statements

* `Cobham.stepWord_foldStep` — the word the step contributes.
* `Cobham.foldSem_nil`, `Cobham.foldSem_cons` — the scan on the empty word
  and on one bit.
* `Cobham.length_foldSem`, `Cobham.length_foldSem_le` — every state has the
  encoding's length.
* `Cobham.foldSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression carries.
* `Cobham.foldSem_eq` — the scan computes the carrier-level fold, encoded.

## Implementation notes

Neither the encoding-to-word nor the carrier-level fold is named: they are
`List.ofFn (enc a)` and `w.foldr step init`.

`length_foldSem` does not consume the retraction hypothesis, every state the
scan produces being a `List.ofFn` of an `enc` value whatever `dec` does.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, fold, catamorphism
-/

namespace Cobham

public section

universe u

variable {α : Type u} {p : ℕ} (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (init : α) (step : Bool → α → α)

/-- The fold's step at a bit: decode the state, apply the carrier-level step,
and spell the result. The dispatch is over the `p` bits of the state, which the
diagonal supplies in both the scrutinee and the argument position. -/
@[expose] def foldStep (b : Bool) : COf 1 :=
  diagOf (casesOf p fun v ↦ constAtOf 1 (List.ofFn (enc (step b (dec v)))))

/-- The step spells the carrier-level step of the state it decodes. -/
theorem stepWord_foldStep (b : Bool) (u : List Bool) :
    stepWord (foldStep enc dec step b) u =
      List.ofFn (enc (step b (dec (bits p u)))) := by
  change stepWord (diagOf (casesOf p fun v ↦
    constAtOf 1 (List.ofFn (enc (step b (dec v)))))) u = _
  rw [stepWord_diagOf]
  change casesSem p (fun v ↦ constAtOf 1 (List.ofFn (enc (step b (dec v)))))
    ![u, u] = _
  rw [casesSem_eq, stepWord_constAtOf]

/-- The fold's meaning: the scan at the encoded base and the two steps, with
the encoding's width as the growth bound. -/
@[expose] def foldSem : Sem 1 :=
  scanSem (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p

/-- The fold on the empty word is the encoded initial value. -/
theorem foldSem_nil : foldSem enc dec init step ![[]] = List.ofFn (enc init) :=
  (scanSem_nil (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p).trans (baseWord_constAtOf _)

/-- One step of the fold: the bit selects the step, which reads the value the
fold of the rest of the word returns. -/
theorem foldSem_cons (b : Bool) (w : List Bool) :
    foldSem enc dec init step ![b :: w] =
      stepWord (foldStep enc dec step b) (foldSem enc dec init step ![w]) :=
  (scanSem_cons (constAtOf 0 (List.ofFn (enc init)))
    (foldStep enc dec step false) (foldStep enc dec step true) p b w).trans
    (by cases b <;> rfl)

/-- Every state the fold produces has the encoding's width, whatever `dec`
does off the image of `enc`. -/
theorem length_foldSem : ∀ w : List Bool,
    (foldSem enc dec init step ![w]).length = p :=
  List.rec
    (by rw [foldSem_nil, List.length_ofFn])
    (fun b v _ ↦ by
      rw [foldSem_cons, stepWord_foldStep, List.length_ofFn])

/-- The growth bound the scan combinator asks for, tight at the empty word. -/
theorem length_foldSem_le (w : List Bool) :
    (scanSem (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
      (foldStep enc dec step true) p ![w]).length ≤ w.length + p :=
  (length_foldSem enc dec init step w).le.trans (Nat.le_add_left p w.length)

/-- The fold as an expression of `C`. -/
@[expose] def fold : C :=
  scan (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)

/-- `fold` at its declared arity. -/
@[expose] def foldOf : COf 1 :=
  scanOf (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)

/-- The meaning read at the raw tree is the meaning the expression carries. -/
theorem foldSem_eq_eval :
    transport (foldOf enc dec init step).2 (foldOf enc dec init step).1.eval =
      foldSem enc dec init step :=
  scanSem_eq_eval (constAtOf 0 (List.ofFn (enc init))) (foldStep enc dec step false)
    (foldStep enc dec step true) p (length_foldSem_le enc dec init step)

/-- The fold computes the carrier-level fold of the word, encoded. This is
where the retraction hypothesis enters: the state the scan carries is an
encoded carrier value, so decoding it returns that value. -/
theorem foldSem_eq (hdec : ∀ a, dec (enc a) = a) : ∀ w : List Bool,
    foldSem enc dec init step ![w] = List.ofFn (enc (w.foldr step init)) :=
  List.rec (foldSem_nil enc dec init step)
    (fun b v ih ↦ by
      rw [foldSem_cons, ih, stepWord_foldStep, bits_ofFn, hdec]
      rfl)

#print axioms foldStep
#print axioms stepWord_foldStep
#print axioms foldSem
#print axioms foldSem_nil
#print axioms foldSem_cons
#print axioms length_foldSem
#print axioms length_foldSem_le
#print axioms fold
#print axioms foldOf
#print axioms foldSem_eq_eval
#print axioms foldSem_eq

end

end Cobham
