/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Body
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The loops compute simultaneous recursion on representations

The two loops of a compiled recursion node iterate their bodies' transformers,
and the iterates carry invariants that read
{name}`Geb.SizeBounded.Logspace.phaseSuffix` and
{name}`Geb.SizeBounded.Logspace.evalSRNRep` off the value registers. In the
first loop, after {lit}`j` iterations the cursor is {lit}`⟨[], j⟩`, the loop's
counter is the end segment length less {lit}`j`, and the value registers hold
the first phase at {lit}`j`; the loop runs as many times as the counter holds.
In the second loop, after {lit}`j` iterations the reversed word register holds
the reverse of a prefix of the word part, the cursor's word is the remaining
suffix, and the value registers hold the recursion at that suffix; the loop
runs as many times as the word is long. {lit}`srnLoop1_contract` and
{lit}`srnLoop2_contract` state each loop's contract under
{name}`Geb.SizeBounded.Logspace.Machine.TransformsIn.whileReg`, given the
clauses of its body's transformer, together with the clauses of the loop's
transformer the node's proof reads.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`readRep_srnEnv` — the representations of the step environment are the
  step environment of the cursor's, the value registers' and the parameters'.
* {lit}`phaseSuffix_congr_base` — the first phase depends on its bases only
  through their values at the parameters.
* {lit}`srnLoop1_contract`, {lit}`srnLoop2_contract` — the contracts of the two
  loops.

# Tags

Turing machine, loop, recursion on notation, invariant, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded.Machine (Prog Bounded)

public section

/-- The representations of the step environment are the step environment of
the cursor's, the value registers' and the parameters'. -/
theorem readRep_srnEnv {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k)
    (params : Fin a → Reg k) (τ : Fin k → List Bool) :
    (fun s ↦ readRep τ (srnEnv free hk params s)) =
      stepEnvRep (readRep τ (srnV free (by omega))) (fun l ↦ readRep τ (srnVals b free hk l))
        (fun p ↦ readRep τ (params p)) := by
  funext s
  unfold srnEnv stepEnvRep
  refine Fin.cases rfl (fun s ↦ ?_) s
  rw [Fin.cons_succ, Fin.cons_succ]
  refine Fin.addCases (motive := fun s ↦ readRep τ (Fin.append (srnVals b free hk) params s) =
    Fin.append (fun l ↦ readRep τ (srnVals b free hk l)) (fun p ↦ readRep τ (params p)) s)
    (fun l ↦ ?_) (fun p ↦ ?_) s
  · rw [Fin.append_left, Fin.append_left]
  · rw [Fin.append_right, Fin.append_right]

/-- The first phase depends on its bases only through their values at the
parameters. -/
theorem phaseSuffix_congr_base (w : List Bool) {a b : ℕ} {g g' : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} (x : Fin a → Rep) (hg : ∀ l, g l x = g' l x) :
    ∀ j l, phaseSuffix w g h j l x = phaseSuffix w g' h j l x :=
  Nat.rec hg fun j ih l ↦ by
    change h (bitAt w j) l (stepEnvRep ⟨[], j⟩ (fun l' ↦ phaseSuffix w g h j l' x) x) =
      h (bitAt w j) l (stepEnvRep ⟨[], j⟩ (fun l' ↦ phaseSuffix w g' h j l' x) x)
    rw [show (fun l' ↦ phaseSuffix w g h j l' x) = fun l' ↦ phaseSuffix w g' h j l' x from
      funext fun l' ↦ ih l']

/-- The contract of the first loop: from a valuation with an empty cursor, a
counter in the loop's register within the input, and well-formed value
registers and parameters, the loop iterates its body as many times as the
counter holds, leaving the tapes below the first free one alone, the cursor at
the empty word and that length, and the value registers holding the first
phase of the recursion at that length, well-formed. -/
theorem srnLoop1_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ) (body : Prog k)
    (B1 : List Bool → (Fin k → List Bool) → Fin k → List Bool) (T1 : ℕ → ℕ)
    (stepRep : Bool → Fin b → List Bool → RepSem (b + a + 1))
    (hT : TransformsIn body.tm
      (fun input σ ↦ (∃ j, σ (srnV free (by omega) 1) = counterWord j ∧ j < input.length) ∧
        EnvWF M input σ (srnEnv (b := b) free (by omega) params)) B1 T1 (bound M))
    (hfr : ∀ input σ (t : Fin k), t.val < free → B1 input σ t = σ t)
    (hV0 : ∀ input σ, B1 input σ (srnV free (by omega) 0) = σ (srnV free (by omega) 0))
    (hV1 : ∀ input σ j, σ (srnV free (by omega) 1) = counterWord j →
      B1 input σ (srnV free (by omega) 1) = counterWord (j + 1))
    (hCR : ∀ input σ, B1 input σ ⟨free + 2, by omega⟩ =
      (decL (σ ⟨free + 2, by omega⟩).reverse).reverse)
    (hvals : ∀ input σ j, σ (srnV free (by omega) 1) = counterWord j → j < input.length →
      EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      readRep (B1 input σ) (srnVals b free (by omega) l) =
        stepRep (bitAt input j) l input
          (fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
      WF M input.length (B1 input σ) (srnVals b free (by omega) l)) :
    TransformsIn (Prog.whileReg ⟨free + 2, by omega⟩ body).tm
      (fun input σ ↦ σ (srnV free (by omega) 0) = [] ∧
        σ (srnV free (by omega) 1) = counterWord 0 ∧
        (∃ l ≤ input.length, σ ⟨free + 2, by omega⟩ = counterWord l) ∧
        (∀ l, WF M input.length σ (srnVals b free (by omega) l)) ∧
        ∀ p, WF M input.length σ (params p))
      (fun input σ ↦ (B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ)
      (fun n ↦ n * (T1 n + 1) + 1) (bound M) ∧
    (∀ input σ, σ (srnV free (by omega) 0) = [] →
      σ (srnV free (by omega) 1) = counterWord 0 →
      (∃ l ≤ input.length, σ ⟨free + 2, by omega⟩ = counterWord l) →
      (∀ l, WF M input.length σ (srnVals b free (by omega) l)) →
      (∀ p, WF M input.length σ (params p)) →
      (∀ t : Fin k, t.val < free →
        (B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ t = σ t) ∧
      (B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ (srnV free (by omega) 0) = [] ∧
      (B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ (srnV free (by omega) 1) =
        counterWord (counterValue (σ ⟨free + 2, by omega⟩)) ∧
      ∀ l, readRep ((B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ)
          (srnVals b free (by omega) l) =
          phaseSuffix input (fun l _ ↦ readRep σ (srnVals b free (by omega) l))
            (fun i l ↦ stepRep i l input) (counterValue (σ ⟨free + 2, by omega⟩)) l
            (fun p ↦ readRep σ (params p)) ∧
        WF M input.length ((B1 input)^[counterValue (σ ⟨free + 2, by omega⟩)] σ)
          (srnVals b free (by omega) l)) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hkV : free + 2 ≤ k := by omega
  have hf2 : free + 2 < k := by omega
  -- The invariant of the iterates.
  have hinv : ∀ (input : List Bool) (σ : Fin k → List Bool),
      σ (srnV free hkV 0) = [] → σ (srnV free hkV 1) = counterWord 0 →
      (∃ l ≤ input.length, σ ⟨free + 2, hf2⟩ = counterWord l) →
      (∀ l, WF M input.length σ (srnVals b free hk2 l)) →
      (∀ p, WF M input.length σ (params p)) →
      ∀ j, j ≤ counterValue (σ ⟨free + 2, hf2⟩) →
        (B1 input)^[j] σ (srnV free hkV 0) = [] ∧
        (B1 input)^[j] σ (srnV free hkV 1) = counterWord j ∧
        (B1 input)^[j] σ ⟨free + 2, hf2⟩ = counterWord (counterValue (σ ⟨free + 2, hf2⟩) - j) ∧
        (∀ t : Fin k, t.val < free → (B1 input)^[j] σ t = σ t) ∧
        ∀ l, readRep ((B1 input)^[j] σ) (srnVals b free hk2 l) =
            phaseSuffix input (fun l _ ↦ readRep σ (srnVals b free hk2 l))
              (fun i l ↦ stepRep i l input) j l (fun p ↦ readRep σ (params p)) ∧
          WF M input.length ((B1 input)^[j] σ) (srnVals b free hk2 l) := by
    intro input σ h0 h1 ⟨l, hl, hC⟩ hwf hp
    have hlv : counterValue (σ ⟨free + 2, hf2⟩) = l := by rw [hC, counterValue_counterWord]
    refine Nat.rec (fun _ ↦ ⟨h0, h1, ?_, fun _ _ ↦ rfl, fun l' ↦ ⟨rfl, hwf l'⟩⟩) (fun j ih hj ↦ ?_)
    · rw [Function.iterate_zero_apply, hlv]
      change σ ⟨free + 2, hf2⟩ = counterWord (l - 0)
      rw [Nat.sub_zero, hC]
    obtain ⟨i0, i1, iC, ifr, ivals⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    -- the step environment of the iterate is well-formed
    have henv : EnvWF M input ((B1 input)^[j] σ) (srnEnv free hk2 params) := by
      intro s
      rcases srnEnv_cases free hk2 params s 0 with ⟨hs, _⟩ | ⟨l', hs, _⟩ | ⟨p, hs, _⟩
      · subst hs
        refine ⟨?_, j, by omega, ?_⟩
        · change ((B1 input)^[j] σ (srnV free hkV 0)).length ≤ M
          rw [i0]
          exact Nat.zero_le _
        · change (B1 input)^[j] σ (srnV free hkV 1) = _
          exact i1
      · subst hs
        rw [srnEnv_castAdd]
        exact (ivals l').2
      · subst hs
        rw [srnEnv_natAdd]
        obtain ⟨hw, l'', hl'', hc⟩ := hp p
        refine ⟨?_, l'', hl'', ?_⟩
        · rw [ifr _ (hparams p 0)]
          exact hw
        · rw [ifr _ (hparams p 1)]
          exact hc
    refine ⟨?_, ?_, ?_, ?_, fun l' ↦ ⟨?_, ?_⟩⟩
    · rw [hV0, i0]
    · exact hV1 input _ j i1
    · rw [hCR, iC, hlv, show l - j = (l - (j + 1)) + 1 from by omega, decL_counterWord_succ]
    · intro t ht
      rw [hfr input _ t ht, ifr t ht]
    · rw [(hvals input _ j i1 (by omega) henv l').1, readRep_srnEnv]
      change stepRep (bitAt input j) l' input (stepEnvRep (readRep _ (srnV free hkV))
        (fun l ↦ readRep _ (srnVals b free hk2 l)) fun p ↦ readRep _ (params p)) = _
      have hcur : readRep ((B1 input)^[j] σ) (srnV free hkV) = ⟨[], j⟩ := by
        unfold readRep
        rw [i0, i1, counterValue_counterWord]
      have hpar : (fun p ↦ readRep ((B1 input)^[j] σ) (params p)) =
          fun p ↦ readRep σ (params p) := funext fun p ↦ by
        unfold readRep
        rw [ifr _ (hparams p 0), ifr _ (hparams p 1)]
      have hv : (fun l ↦ readRep ((B1 input)^[j] σ) (srnVals b free hk2 l)) =
          fun l ↦ phaseSuffix input (fun l _ ↦ readRep σ (srnVals b free hk2 l))
            (fun i l ↦ stepRep i l input) j l (fun p ↦ readRep σ (params p)) :=
        funext fun l ↦ (ivals l).1
      rw [hcur, hpar, hv]
      rfl
    · exact (hvals input _ j i1 (by omega) henv l').2
  refine ⟨?_, ?_⟩
  · refine TransformsIn.whileReg ⟨free + 2, hf2⟩ hT _
      (fun input σ ↦ counterValue (σ ⟨free + 2, hf2⟩)) (fun n ↦ n) ?_ ?_ ?_
    · intro input σ ⟨_, _, ⟨l, hl, hC⟩, _, _⟩
      rw [hC, counterValue_counterWord]
      exact hl
    · intro input σ ⟨h0, h1, hC, hwf, hp⟩ j hj
      obtain ⟨i0, i1, iC, _, ivals⟩ := hinv input σ h0 h1 hC hwf hp j (by omega)
      obtain ⟨l, hl, hC'⟩ := hC
      have hlv : counterValue (σ ⟨free + 2, hf2⟩) = l := by rw [hC', counterValue_counterWord]
      refine ⟨?_, ⟨j, i1, by omega⟩, ?_⟩
      · rw [iC]
        intro h
        have := (counterWord_eq_nil_iff _).mp h
        omega
      · intro s
        rcases srnEnv_cases free hk2 params s 0 with ⟨hs, _⟩ | ⟨l', hs, _⟩ | ⟨p, hs, _⟩
        · subst hs
          refine ⟨?_, j, by omega, ?_⟩
          · change ((B1 input)^[j] σ (srnV free hkV 0)).length ≤ M
            rw [i0]
            exact Nat.zero_le _
          · change (B1 input)^[j] σ (srnV free hkV 1) = _
            exact i1
        · subst hs
          rw [srnEnv_castAdd]
          exact (ivals l').2
        · subst hs
          obtain ⟨_, _, _, ifr, _⟩ := hinv input σ h0 h1 ⟨l, hl, hC'⟩ hwf hp j (by omega)
          rw [srnEnv_natAdd]
          obtain ⟨hw, l'', hl'', hc⟩ := hp p
          refine ⟨?_, l'', hl'', ?_⟩
          · rw [ifr _ (hparams p 0)]
            exact hw
          · rw [ifr _ (hparams p 1)]
            exact hc
    · intro input σ ⟨h0, h1, hC, hwf, hp⟩
      obtain ⟨_, _, iC, _, _⟩ := hinv input σ h0 h1 hC hwf hp _ (le_refl _)
      rw [iC, Nat.sub_self]
      rfl
  · intro input σ h0 h1 hC hwf hp
    obtain ⟨i0, i1, _, ifr, ivals⟩ := hinv input σ h0 h1 hC hwf hp _ (le_refl _)
    exact ⟨ifr, i0, i1, ivals⟩

/-- The contract of the second loop: from a valuation whose cursor's word is
empty and whose cursor's length is a counter within the input, whose reversed
word register holds a word within the word bound, and whose value registers
hold the recursion at the empty word and that length, the loop iterates its
body as many times as the reversed word is long, leaving the tapes below the
first free one and the cursor's length alone, the cursor's word at the reverse
of the reversed word, and the value registers holding the recursion at that
word and length, well-formed. -/
theorem srnLoop2_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ) (body : Prog k)
    (B2 : List Bool → (Fin k → List Bool) → Fin k → List Bool) (T2 : ℕ → ℕ)
    (g : List Bool → Fin b → RepSem a) (stepRep : Bool → Fin b → List Bool → RepSem (b + a + 1))
    (hT : TransformsIn body.tm
      (fun input σ ↦ (σ (srnV free (by omega) 0)).length < M ∧
        EnvWF M input σ (srnEnv (b := b) free (by omega) params)) B2 T2 (bound M))
    (hfr : ∀ input σ (t : Fin k), t.val < free → B2 input σ t = σ t)
    (hV1 : ∀ input σ, B2 input σ (srnV free (by omega) 1) = σ (srnV free (by omega) 1))
    (hRV : ∀ input σ (c : Bool) (r : List Bool), σ ⟨free + 5, by omega⟩ = c :: r →
      B2 input σ ⟨free + 5, by omega⟩ = r ∧
      B2 input σ (srnV free (by omega) 0) = c :: σ (srnV free (by omega) 0))
    (hvals : ∀ input σ (c : Bool) (r : List Bool), σ ⟨free + 5, by omega⟩ = c :: r →
      EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      readRep (B2 input σ) (srnVals b free (by omega) l) =
        stepRep c l input (fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
      WF M input.length (B2 input σ) (srnVals b free (by omega) l)) :
    TransformsIn (Prog.whileReg ⟨free + 5, by omega⟩ body).tm
      (fun input σ ↦ σ (srnV free (by omega) 0) = [] ∧
        (∃ l ≤ input.length, σ (srnV free (by omega) 1) = counterWord l) ∧
        (σ ⟨free + 5, by omega⟩).length ≤ M ∧
        (∀ l, readRep σ (srnVals b free (by omega) l) =
          evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
            ⟨[], counterValue (σ (srnV free (by omega) 1))⟩ l (fun p ↦ readRep σ (params p))) ∧
        (∀ l, WF M input.length σ (srnVals b free (by omega) l)) ∧
        ∀ p, WF M input.length σ (params p))
      (fun input σ ↦ (B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ)
      (fun n ↦ M * (T2 n + 1) + 1) (bound M) ∧
    (∀ input σ, σ (srnV free (by omega) 0) = [] →
      (∃ l ≤ input.length, σ (srnV free (by omega) 1) = counterWord l) →
      (σ ⟨free + 5, by omega⟩).length ≤ M →
      (∀ l, readRep σ (srnVals b free (by omega) l) =
        evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
          ⟨[], counterValue (σ (srnV free (by omega) 1))⟩ l (fun p ↦ readRep σ (params p))) →
      (∀ l, WF M input.length σ (srnVals b free (by omega) l)) →
      (∀ p, WF M input.length σ (params p)) →
      (∀ t : Fin k, t.val < free → (B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ t = σ t) ∧
      (B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ (srnV free (by omega) 1) =
        σ (srnV free (by omega) 1) ∧
      (B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ (srnV free (by omega) 0) =
        (σ ⟨free + 5, by omega⟩).reverse ∧
      ∀ l, readRep ((B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ) (srnVals b free (by omega) l) =
          evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
            ⟨(σ ⟨free + 5, by omega⟩).reverse, counterValue (σ (srnV free (by omega) 1))⟩ l
            (fun p ↦ readRep σ (params p)) ∧
        WF M input.length ((B2 input)^[(σ ⟨free + 5, by omega⟩).length] σ)
          (srnVals b free (by omega) l)) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hkV : free + 2 ≤ k := by omega
  have hf5 : free + 5 < k := by omega
  -- The invariant of the iterates.
  have hinv : ∀ (input : List Bool) (σ : Fin k → List Bool),
      σ (srnV free hkV 0) = [] → (∃ l ≤ input.length, σ (srnV free hkV 1) = counterWord l) →
      (σ ⟨free + 5, hf5⟩).length ≤ M →
      (∀ l, readRep σ (srnVals b free hk2 l) =
        evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
          ⟨[], counterValue (σ (srnV free hkV 1))⟩ l (fun p ↦ readRep σ (params p))) →
      (∀ l, WF M input.length σ (srnVals b free hk2 l)) →
      (∀ p, WF M input.length σ (params p)) →
      ∀ j, j ≤ (σ ⟨free + 5, hf5⟩).length →
        ∃ w' c', (σ ⟨free + 5, hf5⟩).reverse = w' ++ c' ∧
          (B2 input)^[j] σ ⟨free + 5, hf5⟩ = w'.reverse ∧
          (B2 input)^[j] σ (srnV free hkV 0) = c' ∧ c'.length = j ∧
          (B2 input)^[j] σ (srnV free hkV 1) = σ (srnV free hkV 1) ∧
          (∀ t : Fin k, t.val < free → (B2 input)^[j] σ t = σ t) ∧
          ∀ l, readRep ((B2 input)^[j] σ) (srnVals b free hk2 l) =
              evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
                ⟨c', counterValue (σ (srnV free hkV 1))⟩ l (fun p ↦ readRep σ (params p)) ∧
            WF M input.length ((B2 input)^[j] σ) (srnVals b free hk2 l) := by
    intro input σ h0 ⟨l, hl, h1⟩ hR hvals0 hwf hp
    refine Nat.rec (fun _ ↦ ⟨(σ ⟨free + 5, hf5⟩).reverse, [], (List.append_nil _).symm,
      by rw [Function.iterate_zero_apply, List.reverse_reverse], h0, rfl, rfl, fun _ _ ↦ rfl,
      fun l' ↦ ⟨hvals0 l', hwf l'⟩⟩) (fun j ih hj ↦ ?_)
    obtain ⟨w', c', hu, iR, i0, ilen, i1, ifr, ivals⟩ := ih (by omega)
    -- the prefix is nonempty, so it ends in a bit
    have hlen : w'.length + c'.length = (σ ⟨free + 5, hf5⟩).length := by
      rw [← List.length_append, ← hu, List.length_reverse]
    obtain ⟨w'', x0, hw'⟩ : ∃ w'' x0, w' = w'' ++ [x0] := by
      rcases List.eq_nil_or_concat w' with h | ⟨w'', x0, h⟩
      · subst h
        rw [List.length_nil] at hlen
        omega
      · exact ⟨w'', x0, by rw [h, List.concat_eq_append]⟩
    subst hw'
    have hRj : (B2 input)^[j] σ ⟨free + 5, hf5⟩ = x0 :: w''.reverse := by
      rw [iR, List.reverse_concat]
    -- the step environment of the iterate is well-formed
    have henv : EnvWF M input ((B2 input)^[j] σ) (srnEnv free hk2 params) := by
      intro s
      rcases srnEnv_cases free hk2 params s 0 with ⟨hs, _⟩ | ⟨l', hs, _⟩ | ⟨p, hs, _⟩
      · subst hs
        refine ⟨?_, l, hl, ?_⟩
        · change ((B2 input)^[j] σ (srnV free hkV 0)).length ≤ M
          rw [i0]
          omega
        · change (B2 input)^[j] σ (srnV free hkV 1) = _
          rw [i1, h1]
      · subst hs
        rw [srnEnv_castAdd]
        exact (ivals l').2
      · subst hs
        rw [srnEnv_natAdd]
        obtain ⟨hw, l'', hl'', hc⟩ := hp p
        refine ⟨?_, l'', hl'', ?_⟩
        · rw [ifr _ (hparams p 0)]
          exact hw
        · rw [ifr _ (hparams p 1)]
          exact hc
    obtain ⟨hR', hV0'⟩ := hRV input _ x0 w''.reverse hRj
    refine ⟨w'', x0 :: c', ?_, ?_, ?_, ?_, ?_, ?_, fun l' ↦ ⟨?_, ?_⟩⟩
    · rw [hu, List.append_assoc, List.singleton_append]
    · rw [Function.iterate_succ_apply', hR']
    · rw [Function.iterate_succ_apply', hV0', i0]
    · rw [List.length_cons, ilen]
    · rw [Function.iterate_succ_apply', hV1, i1]
    · intro t ht
      rw [Function.iterate_succ_apply', hfr input _ t ht, ifr t ht]
    · rw [Function.iterate_succ_apply', (hvals input _ x0 _ hRj henv l').1, readRep_srnEnv]
      have hcur : readRep ((B2 input)^[j] σ) (srnV free hkV) =
          ⟨c', counterValue (σ (srnV free hkV 1))⟩ := by
        unfold readRep
        rw [i0, i1]
      have hpar : (fun p ↦ readRep ((B2 input)^[j] σ) (params p)) =
          fun p ↦ readRep σ (params p) := funext fun p ↦ by
        unfold readRep
        rw [ifr _ (hparams p 0), ifr _ (hparams p 1)]
      have hv : (fun l ↦ readRep ((B2 input)^[j] σ) (srnVals b free hk2 l)) =
          fun l ↦ evalSRNRep input (g input) (fun i l ↦ stepRep i l input)
            ⟨c', counterValue (σ (srnV free hkV 1))⟩ l (fun p ↦ readRep σ (params p)) :=
        funext fun l ↦ (ivals l).1
      rw [hcur, hpar, hv]
      rfl
    · rw [Function.iterate_succ_apply']
      exact (hvals input _ x0 _ hRj henv l').2
  refine ⟨?_, ?_⟩
  · refine TransformsIn.whileReg ⟨free + 5, hf5⟩ hT _
      (fun input σ ↦ (σ ⟨free + 5, hf5⟩).length) (fun _ ↦ M) ?_ ?_ ?_
    · intro input σ ⟨_, _, hR, _, _, _⟩
      exact hR
    · intro input σ ⟨h0, h1, hR, hvals0, hwf, hp⟩ j hj
      obtain ⟨w', c', hu, iR, i0, ilen, i1, ifr, ivals⟩ := hinv input σ h0 h1 hR hvals0 hwf hp j
        (by omega)
      obtain ⟨l, hl, h1'⟩ := h1
      have hlen : w'.length + c'.length = (σ ⟨free + 5, hf5⟩).length := by
        rw [← List.length_append, ← hu, List.length_reverse]
      refine ⟨?_, ?_, ?_⟩
      · rw [iR, ne_eq, List.reverse_eq_nil_iff]
        intro h
        subst h
        rw [List.length_nil] at hlen
        omega
      · rw [i0]
        omega
      · intro s
        rcases srnEnv_cases free hk2 params s 0 with ⟨hs, _⟩ | ⟨l', hs, _⟩ | ⟨p, hs, _⟩
        · subst hs
          refine ⟨?_, l, hl, ?_⟩
          · change ((B2 input)^[j] σ (srnV free hkV 0)).length ≤ M
            rw [i0]
            omega
          · change (B2 input)^[j] σ (srnV free hkV 1) = _
            rw [i1, h1']
        · subst hs
          rw [srnEnv_castAdd]
          exact (ivals l').2
        · subst hs
          rw [srnEnv_natAdd]
          obtain ⟨hw, l'', hl'', hc⟩ := hp p
          refine ⟨?_, l'', hl'', ?_⟩
          · rw [ifr _ (hparams p 0)]
            exact hw
          · rw [ifr _ (hparams p 1)]
            exact hc
    · intro input σ ⟨h0, h1, hR, hvals0, hwf, hp⟩
      obtain ⟨w', c', hu, iR, _, ilen, _, _, _⟩ := hinv input σ h0 h1 hR hvals0 hwf hp _
        (le_refl _)
      have hlen : w'.length + c'.length = (σ ⟨free + 5, hf5⟩).length := by
        rw [← List.length_append, ← hu, List.length_reverse]
      have hw' : w' = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [iR, hw']
      rfl
  · intro input σ h0 h1 hR hvals0 hwf hp
    obtain ⟨w', c', hu, _, i0, ilen, i1, ifr, ivals⟩ := hinv input σ h0 h1 hR hvals0 hwf hp _
      (le_refl _)
    have hlen : w'.length + c'.length = (σ ⟨free + 5, hf5⟩).length := by
      rw [← List.length_append, ← hu, List.length_reverse]
    have hw' : w' = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw'
    rw [List.nil_append] at hu
    subst hu
    exact ⟨ifr, i1, i0, ivals⟩

end

end Geb.SizeBounded.Logspace.Machine
