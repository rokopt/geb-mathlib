/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Correct
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family

set_option doc.verso true

/-!
# Correctness of a substitution node's compilation

The compiled program of a substitution node runs its arguments into the
consecutive registers above the first free one, in index order, and then its
head with those registers as its environment.
{lit}`correct_comp` derives the node's contract from its children's: every
argument program reads only the environment, which lies below the first free
register, so {name}`Geb.SizeBounded.Machine.composeFin_fresh` reads the head's
environment off the composite valuation, and
{name}`Geb.SizeBounded.Machine.composeFin_of_lt` leaves the registers below the
first free one to the head. The node's step bound is
{name}`Geb.SizeBounded.Machine.Transforms.seqFin`'s for the arguments, each
weakened to the maximum of their bounds, followed by the head's, which is the
bound {name}`Geb.SizeBounded.Machine.stepValue` assigns the node.

# Main statements

* {lit}`correct_comp` — a substitution node meets the contract when its
  children do.

# Tags

Turing machine, compilation, correctness, substitution, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem transport)
open Geb.SizeBounded (Direction rc evalValue nsiValue finMax le_finMax)

public section

/-- A substitution node is correct when its children are: the arguments run into
fresh registers in sequence, then the head reads them. -/
theorem correct_comp {k n m : ℕ} (c : Direction (.comp n m) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.comp n m) b) (s : Direction (.comp n m) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.comp n m) b) (K : Direction (.comp n m) → ℕ)
    (Tf : Direction (.comp n m) → ℕ → ℕ)
    (hk : ∀ b, CorrectSigma (c b) (s b) (K b) (Tf b)) :
    Correct (compileValue (.comp n m) c h) (evalValue (.comp n m) s hs)
      (nsiValue (.comp n m) K) (stepValue (.comp n m) Tf) := by
  intro env out free hfree hinj henv hout _ B hK
  have hregs : free + (m + max (c (.inl ())).2.regs
      (finMax m fun i ↦ (c (.inr i)).2.regs)) ≤ k := hfree
  -- every child is correct at the arity the signature prescribes
  have hchild : ∀ d, Correct (transportP (h d) (c d).2) (transport (hs d) (s d).2)
      (K d) (Tf d) := fun d ↦ (hk d).atArity (h d) (hs d)
  -- the fresh registers the arguments write
  have hrlt : ∀ i : Fin m, free + (i : ℕ) < k := fun i ↦ by have := i.isLt; omega
  set r : Fin m → Fin k := fun i ↦ ⟨free + i, hrlt i⟩
  have hrval : ∀ i : Fin m, (r i : ℕ) = free + i := fun _ ↦ rfl
  have harg : ∀ i : Fin m, free + m + (transportP (h (.inr i)) (c (.inr i)).2).regs ≤ k := by
    intro i
    rw [regs_transportP]
    have := le_finMax m (fun i ↦ (c (.inr i)).2.regs) i
    omega
  have hhead : free + m + (transportP (h (.inl ())) (c (.inl ())).2).regs ≤ k := by
    rw [regs_transportP]
    omega
  have hrinj : Function.Injective r := fun i j hij ↦ Fin.ext (by
    have hval := congrArg Fin.val hij
    rw [hrval, hrval] at hval
    omega)
  -- the arguments, each into its own fresh register
  have hargs := fun i : Fin m ↦ hchild (.inr i) env (r i) (free + m) (harg i) hinj
    (fun j ↦ by have := henv j; omega) (by have := i.isLt; rw [hrval]; omega)
    (fun j ↦ Fin.ne_of_val_ne (by have := henv j; rw [hrval]; omega)) B
    (Nat.le_trans (le_nsiValue _ K (.inr i)) hK)
  choose F hFT hFout hFframe hFB using hargs
  -- the head, reading the fresh registers
  obtain ⟨G, hGT, hGout, hGframe, hGB⟩ := hchild (.inl ()) r out (free + m) hhead hrinj
    (fun i ↦ by have : (i : ℕ) < m := i.isLt; rw [hrval]; omega) (by omega)
    (fun i ↦ Fin.ne_of_val_ne (by rw [hrval]; omega)) B
    (Nat.le_trans (le_nsiValue _ K (.inl ())) hK)
  have hseq : Transforms (seqFin m
      (fun i ↦ ((transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + m)
        (harg i)).State)
      (fun i ↦ ((transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + m)
        (harg i)).tm)).2 (composeFin m F) (m * finMax m (fun i ↦ Tf (.inr i) B) + 1) B :=
    Transforms.seqFin B (finMax m fun i ↦ Tf (.inr i) B) m _ _ F
      (fun i ↦ Transforms.mono_time (hFT i) (le_finMax m (fun i ↦ Tf (.inr i) B) i)) hFB
  -- the head's environment after the arguments have run
  have hg : ∀ (l : Fin m) (τ τ' : Fin k → List Bool),
      (∀ j : Fin k, (j : ℕ) < free → τ j = τ' j) →
      transport (hs (.inr l)) (s (.inr l)).2 (τ ∘ env) =
        transport (hs (.inr l)) (s (.inr l)).2 (τ' ∘ env) :=
    fun _ _ _ hτ ↦ congrArg _ (funext fun j ↦ hτ (env j) (henv j))
  have hfresh : ∀ (σ : Fin k → List Bool) (i : Fin m), composeFin m F σ (r i) =
      transport (hs (.inr i)) (s (.inr i)).2 (σ ∘ env) :=
    composeFin_fresh free m (by omega) F
      (fun l τ ↦ transport (hs (.inr l)) (s (.inr l)).2 (τ ∘ env)) hg hFout hFframe
  refine ⟨fun σ ↦ G (composeFin m F σ), Transforms.seq hseq hGT (composeFin_bounded B m F hFB),
    fun σ ↦ ?_, fun σ i hi hio ↦ ?_, fun σ hσ ↦ hGB _ (composeFin_bounded B m F hFB σ hσ)⟩
  · change G (composeFin m F σ) out = _
    rw [hGout]
    exact congrArg _ (funext fun i ↦ hfresh σ i)
  · change G (composeFin m F σ) i = σ i
    rw [hGframe (composeFin m F σ) i (by omega) hio]
    exact composeFin_of_lt free m F
      (fun l τ j hj ↦ hFframe l τ j (by omega)
        (Fin.ne_of_val_ne (by rw [hrval]; omega))) σ i hi

end

end Geb.SizeBounded.Machine
