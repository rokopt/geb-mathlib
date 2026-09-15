/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Transforms
public import Geb.Prototypes.Computability.SizeBounded.Basic

set_option doc.verso true

/-!
# The loop computes simultaneous recursion

{name}`Geb.SizeBounded.Machine.loopF`, the transformer of the recursion loop,
runs a body once per bit of the recursion register's word, with the recursion
register holding the remaining tail. When the bodies extend a suffix register by
the bounded successor {name}`Geb.SizeBounded.sbsSem`, write each step's value
into its value register, and leave the argument and the parameters alone, the
invariant that the value registers hold
{name}`Geb.SizeBounded.evalSRN` at the processed suffix is preserved, so the
loop leaves them holding the recursion at the whole word. Independently of that
reading, the loop leaves every register below its recursion register unchanged
when its bodies do.

# Main statements

* {lit}`loopF_evalSRN` — the loop's transformer computes simultaneous
  recursion.
* {lit}`loopF_frame` — the loop leaves every register below its recursion
  register unchanged when its bodies do.

# Tags

Turing machine, loop, recursion, simultaneous recursion, register
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem)
open Geb.SizeBounded (sbsSem evalSRN)

public section

/-- The loop's transformer computes simultaneous recursion: with the recursion
register holding the reverse of the remaining word, the suffix register the
processed suffix, and the value registers the recursion at that suffix, the loop
leaves the value registers holding the recursion at the whole word. The bodies
are assumed to extend the suffix by the bounded successor, which conses while the
suffix is shorter than the argument, to write each step's value, and to leave
the argument and the parameters alone. -/
theorem loopF_evalSRN {k a b : ℕ} (R V X : Fin k) (vals : Fin b → Fin k)
    (params : Fin a → Fin k) (hRV : R ≠ V) (hRX : R ≠ X) (hRvals : ∀ l, R ≠ vals l)
    (hRparams : ∀ p, R ≠ params p)
    (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (hV : ∀ (i : Bool) σ, (if i then FT else FF) σ V = sbsSem i (σ V) (σ X))
    (hvals : ∀ (i : Bool) σ l, (if i then FT else FF) σ (vals l) =
      h i l (σ ∘ Fin.cons V (Fin.append vals params)))
    (hX : ∀ (i : Bool) σ, (if i then FT else FF) σ X = σ X)
    (hparams : ∀ (i : Bool) σ p, (if i then FT else FF) σ (params p) = σ (params p)) :
    ∀ (r u : List Bool) (σ : Fin k → List Bool), σ V = u →
      σ X = r.reverse ++ u → (∀ l, σ (vals l) = evalSRN g h u l (σ ∘ params)) →
      (∀ l, loopF R FF FT r σ (vals l) = evalSRN g h (r.reverse ++ u) l (σ ∘ params)) ∧
        loopF R FF FT r σ X = σ X ∧ (∀ p, loopF R FF FT r σ (params p) = σ (params p)) := by
  intro r
  refine List.rec ?_ ?_ r
  · intro u σ _ _ hv
    exact ⟨hv, rfl, fun _ ↦ rfl⟩
  · intro c r ih u σ hu hx hv
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hx
    have hσ₁V : Function.update σ R r V = σ V := Function.update_of_ne (Ne.symm hRV) _ _
    have hσ₁X : Function.update σ R r X = σ X := Function.update_of_ne (Ne.symm hRX) _ _
    have hσ₁vals : ∀ l, Function.update σ R r (vals l) = σ (vals l) :=
      fun l ↦ Function.update_of_ne (Ne.symm (hRvals l)) _ _
    have hσ₁params : ∀ p, Function.update σ R r (params p) = σ (params p) :=
      fun p ↦ Function.update_of_ne (Ne.symm (hRparams p)) _ _
    have hσ₂V : (if c then FT else FF) (Function.update σ R r) V = c :: u := by
      rw [hV c, hσ₁V, hσ₁X, hu, hx]
      unfold sbsSem
      split
      · rfl
      · exact absurd (show u.length + 1 ≤ (r.reverse ++ c :: u).length by
          rw [List.length_append, List.length_reverse, List.length_cons]; omega) ‹_›
    have hσ₂X : (if c then FT else FF) (Function.update σ R r) X = σ X := by
      rw [hX c, hσ₁X]
    have hσ₂params : ∀ p,
        (if c then FT else FF) (Function.update σ R r) (params p) = σ (params p) := by
      intro p
      rw [hparams c, hσ₁params]
    have hcomp : (if c then FT else FF) (Function.update σ R r) ∘ params = σ ∘ params :=
      funext hσ₂params
    have henv : Function.update σ R r ∘ (Fin.cons V (Fin.append vals params) :
          Fin (b + a + 1) → Fin k) =
        Fin.cons u (Fin.append (fun l ↦ evalSRN g h u l (σ ∘ params)) (σ ∘ params)) := by
      funext j
      simp only [Function.comp_apply]
      refine Fin.cases ?_ ?_ j
      · rw [Fin.cons_zero, hσ₁V, hu, Fin.cons_zero]
      · refine Fin.addCases (motive := fun s ↦
          Function.update σ R r ((Fin.cons V (Fin.append vals params) :
            Fin (b + a + 1) → Fin k) s.succ) =
            (Fin.cons u (Fin.append (fun l ↦ evalSRN g h u l (σ ∘ params)) (σ ∘ params)) :
              Fin (b + a + 1) → List Bool) s.succ) ?_ ?_
        · intro l
          rw [Fin.cons_succ, Fin.append_left, hσ₁vals, hv l, Fin.cons_succ, Fin.append_left]
        · intro p
          rw [Fin.cons_succ, Fin.append_right, hσ₁params, Fin.cons_succ, Fin.append_right]
          rfl
    have hσ₂vals : ∀ l, (if c then FT else FF) (Function.update σ R r) (vals l) =
        evalSRN g h (c :: u) l
          ((if c then FT else FF) (Function.update σ R r) ∘ params) := by
      intro l
      rw [hvals c, henv, hcomp]
      rfl
    obtain ⟨h₁, h₂, h₃⟩ := ih (c :: u) _ hσ₂V (by rw [hσ₂X, hx]) hσ₂vals
    rw [loopF_cons]
    refine ⟨fun l ↦ ?_, ?_, fun p ↦ ?_⟩
    · rw [h₁ l, hcomp, List.reverse_cons, List.append_assoc, List.singleton_append]
    · rw [h₂, hσ₂X]
    · rw [h₃ p, hσ₂params p]

/-- The loop leaves every register below a bound unchanged when its recursion
register is at or above it and its bodies leave such registers unchanged. -/
theorem loopF_frame {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (lo : ℕ) (hR : lo ≤ R.val)
    (hF : ∀ σ (i : Fin k), i.val < lo → FF σ i = σ i)
    (hT : ∀ σ (i : Fin k), i.val < lo → FT σ i = σ i) :
    ∀ (r : List Bool) (σ : Fin k → List Bool) (i : Fin k), i.val < lo →
      loopF R FF FT r σ i = σ i := by
  have hbody : ∀ (c : Bool) σ (i : Fin k), i.val < lo →
      (if c then FT else FF) σ i = σ i := by
    intro c
    cases c with
    | false => exact hF
    | true => exact hT
  refine List.rec ?_ ?_
  · intro _ _ _
    rfl
  · intro c r ih σ i hi
    rw [loopF_cons, ih _ i hi, hbody c _ i hi,
      Function.update_of_ne (Fin.ne_of_val_ne (by omega))]

end

end Geb.SizeBounded.Machine
