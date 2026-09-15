/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Correct
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Body
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.LoopEval
import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.SrnInit

set_option doc.verso true

/-!
# Correctness of a recursion node's compilation

The compiled program of a recursion node reverses the recursion argument into
the recursion register, empties the processed suffix, runs the bases into the
value registers, loops over the reversed argument, and copies the selected value
register into the output register. {lit}`correct_srn` derives the node's
contract from its children's:
{name}`Geb.SizeBounded.Machine.srnInit_valuation` reads the valuation entering
the loop off the bases' contracts,
{name}`Geb.SizeBounded.Machine.srnBody_transforms` reads one turn of the loop
off the steps', and {name}`Geb.SizeBounded.Machine.loopF_evalSRN` turns the two
into {name}`Geb.SizeBounded.evalSRN` at the whole argument, the processed suffix
starting empty and the reversed argument consumed in full. The frame clause is
{name}`Geb.SizeBounded.Machine.loopF_frame` over the initial valuation's, and
the node's step bound is the sum of the parts', which is the bound
{name}`Geb.SizeBounded.Machine.stepValue` assigns the node.

The registers and the initial valuation are written out rather than abbreviated
by local definitions: the program the node's contract speaks of is the
compiler's, and matching it against the programs the parts' contracts speak of
is a definitional comparison of machines, which a local definition standing
between the two sides defeats.

# Main statements

* {lit}`correct_srn` — a recursion node meets the contract when its children
  do.

# Tags

Turing machine, compilation, correctness, recursion, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Cobham (Sem transport)
open Geb.SizeBounded (Direction rc evalValue nsiValue finMax le_finMax stepDir srnBases srnSteps
  evalSRN)

public section

/-- A recursion node is correct when its children are: the bases run into the
value registers, and the loop over the reversed argument runs the steps once per
bit, so the value registers hold the simultaneous recursion at the whole
argument. -/
theorem correct_srn {k a b : ℕ} (j : Fin b) (c : Direction (.srn a b j) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) (s : Direction (.srn a b j) → Σ i, Sem i)
    (hs : ∀ d, (s d).1 = rc (.srn a b j) d) (K : Direction (.srn a b j) → ℕ)
    (Tf : Direction (.srn a b j) → ℕ → ℕ)
    (hk : ∀ d, CorrectSigma (c d) (s d) (K d) (Tf d)) :
    Correct (compileValue (.srn a b j) c h) (evalValue (.srn a b j) s hs)
      (nsiValue (.srn a b j) K) (stepValue (.srn a b j) Tf) := by
  intro env out free hfree hinj henv hout _ B hK
  have hregs : free + (2 * b + 3 + max (finMax b fun l ↦ (c (.inl l)).2.regs)
      (max (finMax b fun l ↦ (c (.inr (.inl l))).2.regs)
        (finMax b fun l ↦ (c (.inr (.inr l))).2.regs))) ≤ k := hfree
  have hfk : free + (2 * b + 3) ≤ k := by omega
  have hXlt : (env 0).val < free := henv 0
  -- every child is correct at the arity the signature prescribes
  have hchild : ∀ d, Correct (transportP (h d) (c d).2) (transport (hs d) (s d).2)
      (K d) (Tf d) := fun d ↦ (hk d).atArity (h d) (hs d)
  -- the parameters lie below the first fresh register, and are distinct
  have hparams : ∀ p : Fin a, (Fin.tail env p).val < free := fun p ↦ henv p.succ
  have hpinj : Function.Injective (Fin.tail env) := by
    intro p p' hpp
    have hsucc : env p.succ = env p'.succ := hpp
    exact Fin.succ_injective a (hinj hsucc)
  -- the bases, each into its own value register
  have hbfree : ∀ l : Fin b,
      free + (2 * b + 3) + (transportP (h (.inl l)) (c (.inl l)).2).regs ≤ k := by
    intro l
    rw [regs_transportP]
    have := le_finMax b (fun l ↦ (c (.inl l)).2.regs) l
    omega
  have hbases := fun l : Fin b ↦ hchild (.inl l) (Fin.tail env)
    (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) (free + (2 * b + 3)) (hbfree l) hpinj
    (fun p ↦ by have := hparams p; omega)
    (by have := l.isLt; change free + 3 + (l : ℕ) < free + (2 * b + 3); omega)
    (fun p ↦ Fin.ne_of_val_ne (by
      have := hparams p
      change (Fin.tail env p).val ≠ free + 3 + (l : ℕ)
      omega))
    B (Nat.le_trans (le_nsiValue _ K (.inl l)) hK)
  choose Fb hFbT hFbout hFbframe hFbB using hbases
  -- the steps, each into its own scratch register, reading the step environment
  have hsfree : ∀ (i : Bool) (l : Fin b),
      free + (2 * b + 3) + (transportP (h (stepDir i l)) (c (stepDir i l)).2).regs ≤ k := by
    intro i l
    rw [regs_transportP]
    cases i
    · have h1 : (c (stepDir false l)).2.regs ≤ finMax b fun l ↦ (c (.inr (.inl l))).2.regs :=
        le_finMax b (fun l ↦ (c (.inr (.inl l))).2.regs) l
      omega
    · have h1 : (c (stepDir true l)).2.regs ≤ finMax b fun l ↦ (c (.inr (.inr l))).2.regs :=
        le_finMax b (fun l ↦ (c (.inr (.inr l))).2.regs) l
      omega
  have hsenv := srnEnv_lt free hfk (Fin.tail env) hparams
  have hsteps := fun (i : Bool) (l : Fin b) ↦ hchild (stepDir i l)
    (Fin.cons (⟨free + 1, by omega⟩ : Fin k)
      (Fin.append (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k))
        (Fin.tail env)))
    (⟨free + 3 + b + l, by have := l.isLt; omega⟩ : Fin k) (free + (2 * b + 3)) (hsfree i l)
    (srnEnv_injective free hfk (Fin.tail env) hparams hpinj)
    (fun p ↦ Nat.lt_of_lt_of_le (hsenv p) (by omega))
    (by have := l.isLt; change free + 3 + b + (l : ℕ) < free + (2 * b + 3); omega)
    (fun p ↦ Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hsenv p)
      (by change free + 3 + b ≤ free + 3 + b + (l : ℕ); omega))))
    B (Nat.le_trans (le_nsiValue _ K (stepDir i l)) hK)
  choose Fs hFsT hFsout hFsframe hFsB using hsteps
  have hTstep : ∀ (i : Bool) (l : Fin b), Tf (stepDir i l) B ≤
      max (finMax b fun l ↦ Tf (.inr (.inl l)) B) (finMax b fun l ↦ Tf (.inr (.inr l)) B) := by
    intro i l
    cases i
    · exact Nat.le_trans (le_finMax b (fun l ↦ Tf (.inr (.inl l)) B) l) (Nat.le_max_left _ _)
    · exact Nat.le_trans (le_finMax b (fun l ↦ Tf (.inr (.inr l)) B) l) (Nat.le_max_right _ _)
  -- one turn of the loop, for each bit
  have hbody := fun i : Bool ↦ srnBody_transforms i free hfk (Fin.tail env) (env 0) hparams hXlt
    (fun l ↦ (transportP (h (stepDir i l)) (c (stepDir i l)).2).prog
      (Fin.cons (⟨free + 1, by omega⟩ : Fin k)
        (Fin.append (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k))
          (Fin.tail env)))
      (⟨free + 3 + b + l, by have := l.isLt; omega⟩ : Fin k) (free + (2 * b + 3)) (hsfree i l))
    (srnSteps s hs i)
    (max (finMax b fun l ↦ Tf (.inr (.inl l)) B) (finMax b fun l ↦ Tf (.inr (.inr l)) B)) B
    (fun l ↦ ⟨Fs i l, Transforms.mono_time (hFsT i l) (hTstep i l), hFsout i l, hFsframe i l,
      hFsB i l⟩)
  obtain ⟨GF, hGFT, hGFV, hGFvals, hGFframe, hGFB⟩ := hbody false
  obtain ⟨GT, hGTT, hGTV, hGTvals, hGTframe, hGTB⟩ := hbody true
  -- the valuation entering the loop
  have hinitval := fun σ : Fin k → List Bool ↦ srnInit_valuation free hfk (Fin.tail env) (env 0)
    hparams Fb (srnBases s hs) hFbout hFbframe σ
  have hinitlow : ∀ (σ : Fin k → List Bool) (r : Fin k), r.val < free →
      composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
        (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) []) r = σ r :=
    fun σ ↦ (hinitval σ).2.2.2
  have hinitparams : ∀ σ : Fin k → List Bool,
      composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
        (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) []) ∘ Fin.tail env =
        σ ∘ Fin.tail env :=
    fun σ ↦ funext fun p ↦ hinitlow σ _ (hparams p)
  -- the reversed recursion argument is within the bound
  have hrev : ∀ σ : Fin k → List Bool, Bounded σ B → (σ (env 0)).reverse.length ≤ B :=
    fun σ hσ ↦ by
      rw [List.length_reverse]
      exact hσ (env 0)
  have hinitB : ∀ σ : Fin k → List Bool, Bounded σ B →
      Bounded (composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
        (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) [])) B := fun σ hσ ↦
    composeFin_bounded B b Fb hFbB _
      (Bounded.update (Bounded.update hσ (hrev σ hσ)) (Nat.zero_le B))
  -- the loop computes the simultaneous recursion
  have hloopeval := loopF_evalSRN (⟨free, by omega⟩ : Fin k) (⟨free + 1, by omega⟩ : Fin k)
    (env 0) (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k)) (Fin.tail env)
    (Fin.ne_of_val_ne (by change free ≠ free + 1; omega))
    (Fin.ne_of_val_ne (by change free ≠ (env 0).val; omega))
    (fun l ↦ Fin.ne_of_val_ne (by
      have := l.isLt
      change free ≠ free + 3 + (l : ℕ)
      omega))
    (fun p ↦ Fin.ne_of_val_ne (by
      have := hparams p
      change free ≠ (Fin.tail env p).val
      omega))
    (srnBases s hs) (srnSteps s hs) GF GT
    (fun i σ ↦ by cases i with | false => exact hGFV σ | true => exact hGTV σ)
    (fun i σ l ↦ by cases i with | false => exact hGFvals σ l | true => exact hGTvals σ l)
    (fun i σ ↦ by
      cases i with
      | false => exact hGFframe σ (env 0) (by omega)
      | true => exact hGTframe σ (env 0) (by omega))
    (fun i σ p ↦ by
      cases i with
      | false => exact hGFframe σ _ (by have := hparams p; omega)
      | true => exact hGTframe σ _ (by have := hparams p; omega))
  refine ⟨_, Transforms.mono_time (Transforms.seq
      (copyRev_transforms (env 0) (⟨free, by omega⟩ : Fin k)
        (Fin.ne_of_val_ne (by change (env 0).val ≠ free; omega)) B)
      (Transforms.seq (const_transforms [] (⟨free + 1, by omega⟩ : Fin k) B)
        (Transforms.seq
          (Transforms.seqFin B (finMax b fun l ↦ Tf (.inl l) B) b _ _ Fb
            (fun l ↦ Transforms.mono_time (hFbT l) (le_finMax b (fun l ↦ Tf (.inl l) B) l))
            hFbB)
          (Transforms.seq
            (Transforms.caseLoop (⟨free, by omega⟩ : Fin k) hGFT hGTT
              (fun σ ↦ hGFframe σ _ (by change free < free + 1; omega))
              (fun σ ↦ hGTframe σ _ (by change free < free + 1; omega)) hGFB hGTB)
            (copy_transforms (⟨free + 3 + j, by have := j.isLt; omega⟩ : Fin k) out
              (Fin.ne_of_val_ne (by
                have := j.isLt
                change free + 3 + (j : ℕ) ≠ out.val
                omega)) B)
            (fun σ hσ ↦ loopF_bounded _ GF GT B hGFB hGTB (σ _) σ (hσ _) hσ))
          (fun σ hσ ↦ composeFin_bounded B b Fb hFbB σ hσ))
        (fun _ hσ ↦ Bounded.update (w := []) hσ (Nat.zero_le B)))
      (fun σ hσ ↦ hσ.update (hrev σ hσ))) ?_,
    fun σ ↦ ?_, fun σ i hi hio ↦ ?_, fun σ hσ ↦ ?_⟩
  · dsimp only [stepValue]
    omega
  · have hXv : composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
        (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) []) (env 0) =
        (σ (env 0)).reverse.reverse ++ [] := by
      rw [List.reverse_reverse, List.append_nil]
      exact hinitlow σ (env 0) hXlt
    have hvalsv : ∀ l : Fin b,
        composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
            (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) [])
          (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k) =
          evalSRN (srnBases s hs) (srnSteps s hs) [] l
            (composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
              (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) []) ∘ Fin.tail env) := by
      intro l
      rw [hinitparams σ]
      exact (hinitval σ).2.2.1 l
    obtain ⟨h1, -, -⟩ := hloopeval (σ (env 0)).reverse [] _ (hinitval σ).2.1 hXv hvalsv
    have h1j := h1 j
    rw [hinitparams σ, List.reverse_reverse, List.append_nil] at h1j
    refine (Function.update_self ..).trans ?_
    rw [(hinitval σ).1]
    exact h1j
  · refine (Function.update_of_ne hio _ _).trans ?_
    exact (loopF_frame (⟨free, by omega⟩ : Fin k) GF GT free (Nat.le_refl free)
      (fun τ r hr ↦ hGFframe τ r (by omega)) (fun τ r hr ↦ hGTframe τ r (by omega))
      _ _ i hi).trans (hinitlow σ i hi)
  · have hb := loopF_bounded (⟨free, by omega⟩ : Fin k) GF GT B hGFB hGTB
      (composeFin b Fb (Function.update (Function.update σ (⟨free, by omega⟩ : Fin k)
        (σ (env 0)).reverse) (⟨free + 1, by omega⟩ : Fin k) []) (⟨free, by omega⟩ : Fin k))
      _ (hinitB σ hσ _) (hinitB σ hσ)
    exact hb.update (hb _)

end

end Geb.SizeBounded.Machine
