/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.BitTree
meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# Bitstring output conventions

Mazzanti's constant cutoff permits singleton Boolean outputs even at the empty
input. Literal length non-increase is a different condition: the empty input
must return the empty output. Using empty for rejection and a zero bit for
acceptance satisfies that stricter condition exactly when the predicate rejects
the empty word.

## Main definitions

* {lit}`WordNonSizeIncreasing` is the unary bitstring version of the paper's size condition.
* {lit}`zeroOneWord` uses an empty word for rejection and a zero bit for acceptance.
* {lit}`BitTree.recognize` exposes the numerical algebra expression as a bitstring recognizer.

## Main statements

* {lit}`singleton_nonSizeIncreasing` applies to every Boolean predicate.
* {lit}`length_zeroOneWord_le_iff` characterizes the stricter convention at empty input.
* {lit}`BitTree.recognize_eq` identifies the algebra recognizer with the existing singleton output.

## References

* {cite}`Mazzanti2016`, Section 2, definition of non-size-increase.

## Tags

bitstring, non-size-increasing function, acceptance convention
-/

@[expose] public section

namespace Geb.Mazzanti

/-- Output length is bounded by input length or a fixed constant, whichever is larger. -/
def WordNonSizeIncreasing (f : List Bool → List Bool) : Prop :=
  ∃ k, ∀ w, (f w).length ≤ max w.length k

/-- Every singleton Boolean output satisfies the paper's size condition, with cutoff one. -/
theorem singleton_nonSizeIncreasing (p : List Bool → Bool) :
    WordNonSizeIncreasing (fun w ↦ [p w]) :=
  ⟨1, fun _ ↦ Nat.le_max_right _ _⟩

/-- A singleton output fails literal length non-increase at the empty word. -/
theorem not_singleton_length_le (p : List Bool → Bool) :
    ¬ ∀ w, ([p w] : List Bool).length ≤ w.length := by
  intro h
  have he := h []
  simp at he

/-- Empty output means rejection; a single zero bit means acceptance. -/
def zeroOneWord (p : List Bool → Bool) (w : List Bool) : List Bool :=
  if p w then [false] else []

/-- The zero-bit acceptance test recovers the original Boolean predicate. -/
@[simp] theorem zeroOneWord_eq_zero_iff (p : List Bool → Bool) (w : List Bool) :
    zeroOneWord p w = [false] ↔ p w = true := by
  cases h : p w <;> simp [zeroOneWord, h]

/-- The empty/singleton convention never needs a cutoff larger than one. -/
theorem zeroOneWord_nonSizeIncreasing (p : List Bool → Bool) :
    WordNonSizeIncreasing (zeroOneWord p) := by
  refine ⟨1, fun w ↦ ?_⟩
  have h : (zeroOneWord p w).length ≤ 1 := by cases h : p w <;> simp [zeroOneWord, h]
  exact h.trans (Nat.le_max_right _ _)

/-- Literal length non-increase holds exactly when the empty input is rejected. -/
theorem length_zeroOneWord_le_iff (p : List Bool → Bool) :
    (∀ w, (zeroOneWord p w).length ≤ w.length) ↔ p [] = false := by
  constructor
  · intro h
    have he := h []
    cases hp : p [] with
    | false => rfl
    | true =>
      simp only [zeroOneWord, hp, ↓reduceIte, List.length_singleton, List.length_nil] at he
      omega
  · intro h w
    cases w with
    | nil => simp only [zeroOneWord, h, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
    | cons b w =>
      unfold zeroOneWord
      split
      · change 1 ≤ w.length + 1
        omega
      · exact Nat.zero_le _

/-- The size condition is closed under composition, with the maximum of the cutoffs. -/
theorem WordNonSizeIncreasing.comp {f g : List Bool → List Bool}
    (hf : WordNonSizeIncreasing f) (hg : WordNonSizeIncreasing g) :
    WordNonSizeIncreasing (f ∘ g) := by
  obtain ⟨kf, hf⟩ := hf
  obtain ⟨kg, hg⟩ := hg
  refine ⟨max kf kg, fun w ↦ ?_⟩
  have h₁ := hf (g w)
  have h₂ := hg w
  change (f (g w)).length ≤ _
  omega

namespace BitTree

/-- The numerical algebra checker with the existing singleton-bit output convention. -/
def recognize (w : List Bool) : List Bool :=
  [decide (checker.eval ![Geb.BitTree.Elias.fromPayload w] = 1)]

/-- The algebra expression computes the existing bitstring function exactly. -/
theorem recognize_eq (w : List Bool) : recognize w = [Geb.BitTree.validBool w] := by
  rw [recognize, eval_checker]
  cases Geb.BitTree.validBool w <;> rfl

/-- The algebra checker's bitstring output is non-size-increasing, including at empty input. -/
theorem nonSizeIncreasing_recognize : WordNonSizeIncreasing recognize :=
  singleton_nonSizeIncreasing _

/-- Empty rejection and zero-bit acceptance give literal length non-increase for the checker. -/
theorem length_zeroOneWord_validBool_le (w : List Bool) :
    (zeroOneWord Geb.BitTree.validBool w).length ≤ w.length :=
  (length_zeroOneWord_le_iff _).mpr rfl w

end BitTree

end Geb.Mazzanti
