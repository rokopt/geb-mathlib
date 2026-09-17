/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.LoopEval
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Correctness of a recursion node's compilation

The compiled program of a recursion node runs its bases into the value
registers, empties the cursor, copies the argument's end segment length into
the loop counter, runs the first loop, reverses the argument's word into the
reversed word register, runs the second loop, and copies the selected value
register into the output. {lit}`correct_srn` derives the node's contract from
its children's: {name}`Geb.SizeBounded.Logspace.Machine.composeFin_fresh2`
reads the value registers off the bases' contracts, the two loop contracts
{name}`Geb.SizeBounded.Logspace.Machine.srnLoop1_contract` and
{name}`Geb.SizeBounded.Logspace.Machine.srnLoop2_contract` carry the two
phases of {name}`Geb.SizeBounded.Logspace.evalSRNRep`, and the copy reads the
result into the output register. The node's step bound is the sum of the
parts', which is the bound {name}`Geb.SizeBounded.Logspace.Machine.timeValue`
assigns the node.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`srnProg_tm` — the machine of a recursion node's program, part by
  part.
* {lit}`correct_srn` — a recursion node meets the contract when its children
  do.

# Tags

Turing machine, compilation, correctness, recursion on notation, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded (Direction rc nsiValue finMax le_finMax stepDir)
open Geb.SizeBounded.Machine (Prog composeFin composeFin_of_lt le_nsiValue seqFin seq copy const
  copyRev copy_transforms const_transforms copyRev_transforms Transforms Bounded)

public section

/-- The machine of a recursion node's program, part by part. -/
theorem srnProg_tm {k b : ℕ} (Y V : Reg k) (CR R : Fin k) (vals : Fin b → Reg k)
    (out : Reg k) (j : Fin b) (bases : Fin b → Prog k) (body1 body2 : Prog k) :
    (srnProg Y V CR R vals out j bases body1 body2).tm =
      seq (seqFin b (fun l ↦ (bases l).State) (fun l ↦ (bases l).tm)).2
        (seq (const [] (V 0)) (seq (const [] (V 1)) (seq (copy (Y 1) CR)
          (seq (whileNonblank (some CR) body1.tm) (seq (copyRev (Y 0) R)
            (seq (whileNonblank (some R) body2.tm)
              (seq (copy (vals j 0) (out 0)) (copy (vals j 1) (out 1))))))))) := by
  unfold srnProg
  simp only [Prog.tm_seq, Prog.tm_ofTM, Prog.tm_whileReg, Prog.tm_seqFin, copyReg_tm]
  rfl

/-- A recursion node is correct when its children are. -/
theorem correct_srn {k a b : ℕ} (j : Fin b) (c : Direction (.srn a b j) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) (s : Direction (.srn a b j) → List Bool → Σ i, RepSem i)
    (hs : ∀ d x, (s d x).1 = rc (.srn a b j) d) (K : Direction (.srn a b j) → ℕ)
    (hk : ∀ d, CorrectSigma (c d) (s d) (K d)) :
    Correct (compileValue (.srn a b j) c h)
      (fun x ↦ evalRepValue x (.srn a b j) (fun d ↦ s d x) (hs · x)) (nsiValue (.srn a b j) K) := by
  intro env out free hfree hadm M hK
  obtain ⟨hinj, henv, hout, hout01, houtenv⟩ := hadm
  have hkk : free + (4 * b + 6) ≤ k := by
    change free + regsValue (.srn a b j) (fun d ↦ (c d).2.regs) ≤ k at hfree
    rw [regsValue_srn] at hfree
    omega
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hk4 : free + 6 + 4 * b ≤ k := by omega
  have hkV : free + 2 ≤ k := by omega
  have hf2 : free + 2 < k := by omega
  have hf3 : free + 3 < k := by omega
  have hf4 : free + 4 < k := by omega
  have hf5 : free + 5 < k := by omega
  have hV0 : (srnV free hkV 0 : ℕ) = free := rfl
  have hV1 : (srnV free hkV 1 : ℕ) = free + 1 := rfl
  have hvals : ∀ (l : Fin b) (t : Fin 2), (srnVals b free hk2 l t : ℕ) = free + 6 + 2 * l + t :=
    fun _ _ ↦ rfl
  have hscr : ∀ (l : Fin b) (t : Fin 2),
      (srnScr b free hk4 l t : ℕ) = free + 6 + 2 * b + 2 * l + t := fun _ _ ↦ rfl
  -- the parameters and the argument
  set params : Fin a → Reg k := Fin.tail env with hparams_def
  have hparams : ∀ p t, (params p t).val < free := fun p t ↦ henv p.succ t
  have hpinj : Function.Injective fun x : Fin a × Fin 2 ↦ params x.1 x.2 := by
    intro x y hxy
    have := hinj (show (fun x : Fin (a + 1) × Fin 2 ↦ env x.1 x.2) (x.1.succ, x.2) =
      (fun x : Fin (a + 1) × Fin 2 ↦ env x.1 x.2) (y.1.succ, y.2) from hxy)
    have h1 := congrArg Prod.fst this
    have h2 := congrArg Prod.snd this
    exact Prod.ext (Fin.succ_injective a h1) h2
  have hY : ∀ t, (env 0 t).val < free := henv 0
  -- every child is correct at the arity the signature prescribes
  have hchild : ∀ d, Correct (transportP (h d) (c d).2)
      (fun x ↦ repTransport (hs d x) (s d x).2) (K d) := fun d ↦ (hk d).atArity (h d) (hs d)
  have hregsb : ∀ l, free + (4 * b + 6) + (transportP (h (.inl l)) (c (.inl l)).2).regs ≤ k := by
    intro l
    rw [regs_transportP]
    have := le_finMax b (fun l ↦ (c (.inl l)).2.regs) l
    change free + regsValue (.srn a b j) (fun d ↦ (c d).2.regs) ≤ k at hfree
    rw [regsValue_srn] at hfree
    omega
  have hregss : ∀ (i : Bool) (l : Fin b),
      free + (4 * b + 6) + (transportP (h (stepDir i l)) (c (stepDir i l)).2).regs ≤ k := by
    intro i l
    rw [regs_transportP]
    change free + regsValue (.srn a b j) (fun d ↦ (c d).2.regs) ≤ k at hfree
    rw [regsValue_srn] at hfree
    cases i
    · have h1 : (c (stepDir false l)).2.regs ≤ finMax b fun l ↦ (c (.inr (.inl l))).2.regs :=
        le_finMax b (fun l ↦ (c (.inr (.inl l))).2.regs) l
      omega
    · have h1 : (c (stepDir true l)).2.regs ≤ finMax b fun l ↦ (c (.inr (.inr l))).2.regs :=
        le_finMax b (fun l ↦ (c (.inr (.inr l))).2.regs) l
      omega
  -- the bases, each into its own value register
  have hbases := fun l : Fin b ↦ hchild (.inl l) params (srnVals b free hk2 l) (free + (4 * b + 6))
    (hregsb l)
    ⟨hpinj, fun p t ↦ by have := hparams p t; omega,
      fun t ↦ by rw [hvals]; have := l.isLt; have := t.isLt; omega,
      Fin.ne_of_val_ne (by rw [hvals, hvals]; change _ + 0 ≠ _ + 1; omega),
      fun p t t' ↦ Fin.ne_of_val_ne (by rw [hvals]; have := hparams p t; omega)⟩ M
    (Nat.le_trans (le_nsiValue _ K (.inl l)) hK)
  choose Gb hGbT hGbout hGbfr hGbwf using hbases
  -- the steps, each into its own scratch register
  have hsteps := fun (i : Bool) (l : Fin b) ↦ hchild (stepDir i l) (srnEnv free hk2 params)
    (srnScr b free hk4 l) (free + (4 * b + 6)) (hregss i l)
    ⟨srnEnv_injective free hk2 params hparams hpinj,
      fun st t ↦ by have := srnEnv_lt free hk2 params hparams st t; omega,
      fun t ↦ by rw [hscr]; have := l.isLt; have := t.isLt; omega,
      Fin.ne_of_val_ne (by rw [hscr, hscr]; change _ + 0 ≠ _ + 1; omega),
      fun st t t' ↦ Fin.ne_of_val_ne (by
        rw [hscr]; have := srnEnv_lt free hk2 params hparams st t; omega)⟩ M
    (Nat.le_trans (le_nsiValue _ K (stepDir i l)) hK)
  choose Gs hGsT hGsout hGsfr hGswf using hsteps
  set T : ℕ → ℕ := fun n ↦ max (finMax b fun l ↦ (c (.inr (.inl l))).2.time M n)
    (finMax b fun l ↦ (c (.inr (.inr l))).2.time M n) with hT_def
  have hsc : ∀ i, StepsCorrect free hkk params M
      (fun l ↦ (transportP (h (stepDir i l)) (c (stepDir i l)).2).prog (srnEnv free hk2 params)
        (srnScr b free hk4 l) (free + (4 * b + 6)) (hregss i l))
      (fun l input ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2) T (Gs i) := by
    intro i l
    refine ⟨TransformsIn.mono_time (hGsT i l) fun n ↦ ?_, hGsout i l, hGsfr i l, hGswf i l⟩
    rw [time_transportP]
    cases i
    · exact Nat.le_trans (le_finMax b (fun l ↦ (c (.inr (.inl l))).2.time M n) l)
        (Nat.le_max_left _ _)
    · exact Nat.le_trans (le_finMax b (fun l ↦ (c (.inr (.inr l))).2.time M n) l)
        (Nat.le_max_right _ _)
  -- the two loop bodies
  obtain ⟨hB1T, hB1fr, hB1V0, hB1V1, hB1CR, hB1vals⟩ :=
    srnBody1_contract free hkk params hparams M _ _ T (Gs) hsc
  obtain ⟨hB2T, hB2fr, hB2V1, hB2RV, hB2vals⟩ :=
    srnBody2_contract free hkk params hparams M _ _ T (Gs) hsc
  -- the two loops
  obtain ⟨hL1T, hL1⟩ := srnLoop1_contract free hkk params hparams M _ _ _
    (fun i l input ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2)
    hB1T hB1fr hB1V0 hB1V1 hB1CR hB1vals
  obtain ⟨hL2T, hL2⟩ := srnLoop2_contract free hkk params hparams M _ _ _
    (fun input l ↦ repTransport (hs (.inl l) input) (s (.inl l) input).2)
    (fun i l input ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2)
    hB2T hB2fr hB2V1 hB2RV hB2vals
  rw [Prog.tm_whileReg] at hL1T hL2T
  -- the tapes of the layout, by value
  have hCRne : ∀ t, (⟨free + 2, hf2⟩ : Fin k) ≠ srnV free hkV t := fun t ↦
    Fin.ne_of_val_ne (by change free + 2 ≠ free + (t : ℕ); have := t.isLt; omega)
  have hV01 : srnV free hkV 0 ≠ srnV free hkV 1 :=
    Fin.ne_of_val_ne (by rw [hV0, hV1]; omega)
  have hRV : ∀ t, (⟨free + 5, hf5⟩ : Fin k) ≠ srnV free hkV t := fun t ↦
    Fin.ne_of_val_ne (by change free + 5 ≠ free + (t : ℕ); have := t.isLt; omega)
  have hRCR : (⟨free + 5, hf5⟩ : Fin k) ≠ ⟨free + 2, hf2⟩ :=
    Fin.ne_of_val_ne (by change free + 5 ≠ free + 2; omega)
  have hvalsV : ∀ l t t', srnVals b free hk2 l t ≠ srnV free hkV t' := fun l t t' ↦
    Fin.ne_of_val_ne (by rw [hvals]; change _ ≠ free + (t' : ℕ); have := t'.isLt; omega)
  have hvalsCR : ∀ l t, srnVals b free hk2 l t ≠ ⟨free + 2, hf2⟩ := fun l t ↦
    Fin.ne_of_val_ne (by rw [hvals]; change _ ≠ free + 2; omega)
  have hvalsR : ∀ l t, srnVals b free hk2 l t ≠ ⟨free + 5, hf5⟩ := fun l t ↦
    Fin.ne_of_val_ne (by rw [hvals]; change _ ≠ free + 5; omega)
  have hlow : ∀ (t : Fin k), t.val < free → t ≠ srnV free hkV 0 ∧ t ≠ srnV free hkV 1 ∧
      t ≠ ⟨free + 2, hf2⟩ ∧ t ≠ ⟨free + 5, hf5⟩ := fun t ht ↦
    ⟨Fin.ne_of_val_ne (by rw [hV0]; omega), Fin.ne_of_val_ne (by rw [hV1]; omega),
      Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 2; omega),
      Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 5; omega)⟩
  have hY1CR : env 0 1 ≠ ⟨free + 2, hf2⟩ := (hlow _ (hY 1)).2.2.1
  have hY0R : env 0 0 ≠ ⟨free + 5, hf5⟩ := (hlow _ (hY 0)).2.2.2
  have houtvals : ∀ l t t', out t ≠ srnVals b free hk2 l t' := fun l t t' ↦
    Fin.ne_of_val_ne (by rw [hvals]; have := hout t; omega)
  -- the bases' contracts, sequenced
  have hbpres : ∀ l input σ, EnvWF M input σ params → EnvWF M input (Gb l input σ) params :=
    fun l input σ hwf ↦ envWF_of_frame hwf fun p t ↦ hGbfr l input σ _
      (by have := hparams p t; omega)
      (Fin.ne_of_val_ne (by rw [hvals]; have := hparams p t; omega))
      (Fin.ne_of_val_ne (by rw [hvals]; have := hparams p t; omega))
  have hbasesT := TransformsIn.mono_pre (TransformsIn.seqFin (bound M)
    (fun n ↦ finMax b fun l ↦ (c (.inl l)).2.time M n) b _ _
    (fun _ input σ ↦ EnvWF M input σ params) Gb
    (fun l ↦ TransformsIn.mono_time (hGbT l) fun n ↦ by
      rw [time_transportP]
      exact le_finMax b (fun l ↦ (c (.inl l)).2.time M n) l))
    (fun input σ _ hσ ↦ preFin_of_invariant _ b Gb hbpres input σ hσ)
  -- the value registers after the bases
  have hbfresh : ∀ input σ, EnvWF M input σ params → ∀ l,
      composeFin b (fun l ↦ Gb l input) σ (srnVals b free hk2 l 0) =
        (repTransport (hs (.inl l) input) (s (.inl l) input).2 fun p ↦ readRep σ (params p)).word ∧
      composeFin b (fun l ↦ Gb l input) σ (srnVals b free hk2 l 1) =
        counterWord (repTransport (hs (.inl l) input) (s (.inl l) input).2
          fun p ↦ readRep σ (params p)).suffix := by
    intro input σ hσ l
    exact composeFin_fresh2 (free + 6) (fun σ ↦ EnvWF M input σ params) b (by omega)
      (fun l ↦ Gb l input)
      (fun l σ ↦ (repTransport (hs (.inl l) input) (s (.inl l) input).2
        fun p ↦ readRep σ (params p)).word)
      (fun l σ ↦ counterWord (repTransport (hs (.inl l) input) (s (.inl l) input).2
        fun p ↦ readRep σ (params p)).suffix)
      (fun l σ ↦ hbpres l input σ)
      (fun l τ τ' hτ ↦ congrArg (fun x ↦ (repTransport (hs (.inl l) input) (s (.inl l) input).2
        x).word) (funext fun p ↦ by
          unfold readRep
          rw [hτ _ (by have := hparams p 0; omega), hτ _ (by have := hparams p 1; omega)]))
      (fun l τ τ' hτ ↦ congrArg (fun x ↦ counterWord (repTransport (hs (.inl l) input)
        (s (.inl l) input).2 x).suffix) (funext fun p ↦ by
          unfold readRep
          rw [hτ _ (by have := hparams p 0; omega), hτ _ (by have := hparams p 1; omega)]))
      (fun l τ hτ ↦ congrArg Rep.word (hGbout l input τ hτ))
      (fun l τ hτ ↦ by
        obtain ⟨_, l', _, hc⟩ := hGbwf l input τ hτ
        have hsuf := congrArg Rep.suffix (hGbout l input τ hτ)
        change counterValue (Gb l input τ (srnVals b free hk2 l 1)) = _ at hsuf
        rw [← hsuf, hc, counterValue_counterWord]
        exact hc)
      (fun l τ i hi h0 h1 ↦ hGbfr l input τ i (by omega) h0 h1) σ hσ l
  have hbfr : ∀ input σ (t : Fin k), t.val < free + 6 →
      composeFin b (fun l ↦ Gb l input) σ t = σ t := fun input σ t ht ↦
    composeFin_of_lt (free + 6) b (fun l ↦ Gb l input) (fun l τ i hi ↦ hGbfr l input τ i (by omega)
      (Fin.ne_of_val_ne (by rw [hvals]; omega)) (Fin.ne_of_val_ne (by rw [hvals]; omega))) σ t ht
  have hbwf : ∀ input σ, EnvWF M input σ params → ∀ l,
      WF M input.length (composeFin b (fun l ↦ Gb l input) σ) (srnVals b free hk2 l) := by
    intro input σ hσ l
    obtain ⟨h0, h1⟩ := hbfresh input σ hσ l
    obtain ⟨hw, l', hl', hc⟩ := hGbwf l input σ hσ
    have hsuf := congrArg Rep.suffix (hGbout l input σ hσ)
    change counterValue (Gb l input σ (srnVals b free hk2 l 1)) = _ at hsuf
    refine ⟨?_, l', hl', ?_⟩
    · rw [h0, ← congrArg Rep.word (hGbout l input σ hσ)]
      exact hw
    · rw [h1, ← hsuf, hc, counterValue_counterWord]
  -- the remaining components
  have hc0 := Transforms.toIn_of (fun n ↦ const_transforms [] (srnV free hkV 0) (bound M n))
    (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (Nat.zero_le _)
  have hc1 := Transforms.toIn_of (fun n ↦ const_transforms [] (srnV free hkV 1) (bound M n))
    (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (Nat.zero_le _)
  have hcp := Transforms.toIn_of (fun n ↦ copy_transforms (env 0 1) ⟨free + 2, hf2⟩ hY1CR
    (bound M n)) (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (hB _)
  have hrev := Transforms.toIn_of (fun n ↦ copyRev_transforms (env 0 0) ⟨free + 5, hf5⟩ hY0R
    (bound M n)) (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (by
      rw [List.length_reverse]
      exact hB _)
  have hco0 := Transforms.toIn_of (fun n ↦ copy_transforms (srnVals b free hk2 j 0) (out 0)
    (houtvals j 0 0).symm (bound M n)) (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (hB _)
  have hco1 := Transforms.toIn_of (fun n ↦ copy_transforms (srnVals b free hk2 j 1) (out 1)
    (houtvals j 1 1).symm (bound M n)) (fun _ _ ↦ True) fun _ _ hB _ ↦ hB.update (hB _)
  have hcopy : TransformsIn (seq (copy (srnVals b free hk2 j 0) (out 0))
      (copy (srnVals b free hk2 j 1) (out 1))) (fun _ _ ↦ True)
      (fun _ σ ↦ Function.update (Function.update σ (out 0) (σ (srnVals b free hk2 j 0))) (out 1)
        (σ (srnVals b free hk2 j 1)))
      (fun n ↦ (5 * bound M n + 12) + (5 * bound M n + 12)) (bound M) := by
    refine TransformsIn.congr ((hco0.seq hco1).mono_pre fun _ _ _ _ ↦ ⟨trivial, trivial⟩) ?_
    intro input σ _
    funext t
    change Function.update (Function.update σ (out 0) (σ (srnVals b free hk2 j 0))) (out 1)
      (Function.update σ (out 0) (σ (srnVals b free hk2 j 0)) (srnVals b free hk2 j 1)) t = _
    rw [Function.update_of_ne (houtvals j 0 1).symm]
  have hall := hbasesT.seq (hc0.seq (hc1.seq (hcp.seq (hL1T.seq (hrev.seq (hL2T.seq hcopy))))))
  -- the machine of the node is the sequence of the parts
  dsimp only [compileValue]
  rw [← hparams_def, srnProg_tm]
  have hparamsWF : ∀ input σ, EnvWF M input σ env → EnvWF M input σ params :=
    fun input σ hσ p ↦ hσ p.succ
  -- the frame of an iterate
  have hiter : ∀ (f : (Fin k → List Bool) → Fin k → List Bool) (t : Fin k),
      (∀ σ, f σ t = σ t) → ∀ m σ, f^[m] σ t = σ t := fun f t hf ↦
    Nat.rec (fun _ ↦ rfl) fun m ih σ ↦ by rw [Function.iterate_succ_apply', hf, ih]
  -- the valuation entering the first loop
  have hσ4 : ∀ input (σ : Fin k → List Bool) (t : Fin k), t ≠ srnV free hkV 0 →
      t ≠ srnV free hkV 1 → t ≠ ⟨free + 2, hf2⟩ →
      (Function.update (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) t =
        composeFin b (fun l ↦ Gb l input) σ t := by
    intro input σ t h0 h1 h2
    rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
  have hσ4low : ∀ input (σ : Fin k → List Bool) (t : Fin k), t.val < free →
      (Function.update (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) t = σ t := by
    intro input σ t ht
    obtain ⟨h0, h1, h2, _⟩ := hlow t ht
    rw [hσ4 input σ t h0 h1 h2, hbfr input σ t (by omega)]
  have hpre1 : ∀ input σ, EnvWF M input σ env →
      (Function.update (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) (srnV free hkV 0) = [] ∧
      (Function.update (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) (srnV free hkV 1) = counterWord 0 ∧
      (Function.update (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) ⟨free + 2, hf2⟩ = σ (env 0 1) ∧
      (∀ l, WF M input.length (Function.update (Function.update (Function.update
        (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) (srnVals b free hk2 l)) ∧
      (∀ p, WF M input.length (Function.update (Function.update (Function.update
        (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) (params p)) ∧
      ∀ l, readRep (Function.update (Function.update (Function.update
        (composeFin b (fun l ↦ Gb l input) σ)
        (srnV free hkV 0) []) (srnV free hkV 1) []) ⟨free + 2, hf2⟩
        (Function.update (Function.update (composeFin b (fun l ↦ Gb l input) σ)
          (srnV free hkV 0) []) (srnV free hkV 1) [] (env 0 1))) (srnVals b free hk2 l) =
        repTransport (hs (.inl l) input) (s (.inl l) input).2 fun p ↦ readRep σ (params p) := by
    intro input σ hσ
    refine ⟨?_, ?_, ?_, fun l ↦ ?_, fun p ↦ ?_, fun l ↦ ?_⟩
    · rw [Function.update_of_ne (hCRne 0).symm, Function.update_of_ne hV01,
        Function.update_self]
    · rw [Function.update_of_ne (hCRne 1).symm, Function.update_self]
      rfl
    · rw [Function.update_self, Function.update_of_ne (hlow _ (hY 1)).2.1,
        Function.update_of_ne (hlow _ (hY 1)).1, hbfr input σ _ (by have := hY 1; omega)]
    · obtain ⟨hw, l', hl', hc'⟩ := hbwf input σ (hparamsWF input σ hσ) l
      refine ⟨?_, l', hl', ?_⟩
      · rw [hσ4 input σ _ (hvalsV l 0 0) (hvalsV l 0 1) (hvalsCR l 0)]
        exact hw
      · rw [hσ4 input σ _ (hvalsV l 1 0) (hvalsV l 1 1) (hvalsCR l 1)]
        exact hc'
    · obtain ⟨hw, l', hl', hc'⟩ := hσ p.succ
      refine ⟨?_, l', hl', ?_⟩
      · rw [hσ4low input σ _ (hparams p 0)]
        exact hw
      · rw [hσ4low input σ _ (hparams p 1)]
        exact hc'
    · obtain ⟨h0, h1⟩ := hbfresh input σ (hparamsWF input σ hσ) l
      unfold readRep
      rw [hσ4 input σ _ (hvalsV l 0 0) (hvalsV l 0 1) (hvalsCR l 0), h0,
        hσ4 input σ _ (hvalsV l 1 0) (hvalsV l 1 1) (hvalsCR l 1), h1, counterValue_counterWord]
      exact rfl
  -- the run of the two loops from any valuation the initialisation produces
  have hrun : ∀ input (σ σ₄ : Fin k → List Bool), EnvWF M input σ env →
      (∀ t : Fin k, t.val < free → σ₄ t = σ t) →
      σ₄ (srnV free hkV 0) = [] → σ₄ (srnV free hkV 1) = counterWord 0 →
      σ₄ ⟨free + 2, hf2⟩ = σ (env 0 1) →
      (∀ l, WF M input.length σ₄ (srnVals b free hk2 l)) →
      (∀ p, WF M input.length σ₄ (params p)) →
      (∀ l, readRep σ₄ (srnVals b free hk2 l) =
        repTransport (hs (.inl l) input) (s (.inl l) input).2 fun p ↦ readRep σ (params p)) →
      ∀ σ₅, σ₅ = (body1F (srnV free hkV) ⟨free + 2, hf2⟩ ⟨free + 3, hf3⟩ ⟨free + 4, hf4⟩
        (srnVals b free hk2) (srnScr b free hk4) Gs input)^[counterValue (σ₄ ⟨free + 2, hf2⟩)]
          σ₄ →
      ∀ σ₆, σ₆ = Function.update σ₅ ⟨free + 5, hf5⟩ (σ₅ (env 0 0)).reverse →
      ∀ σ₇, σ₇ = (body2F (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩ (srnVals b free hk2)
        (srnScr b free hk4) Gs input)^[(σ₆ ⟨free + 5, hf5⟩).length] σ₆ →
      (σ₆ (srnV free hkV 0) = [] ∧
        (∃ l ≤ input.length, σ₆ (srnV free hkV 1) = counterWord l) ∧
        (σ₆ ⟨free + 5, hf5⟩).length ≤ M ∧
        (∀ l, readRep σ₆ (srnVals b free hk2 l) =
          evalSRNRep input (fun l ↦ repTransport (hs (.inl l) input) (s (.inl l) input).2)
            (fun i l ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2)
            ⟨[], counterValue (σ₆ (srnV free hkV 1))⟩ l fun p ↦ readRep σ₆ (params p)) ∧
        (∀ l, WF M input.length σ₆ (srnVals b free hk2 l)) ∧
        ∀ p, WF M input.length σ₆ (params p)) ∧
      readRep σ₇ (srnVals b free hk2 j) =
        evalSRNRep input (fun l ↦ repTransport (hs (.inl l) input) (s (.inl l) input).2)
          (fun i l ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2)
          ⟨σ (env 0 0), counterValue (σ (env 0 1))⟩ j (fun p ↦ readRep σ (params p)) ∧
      WF M input.length σ₇ (srnVals b free hk2 j) := by
    intro input σ σ₄ hσ hlow4 hp0 hp1 hC hpvals hpp hbase σ₅ hσ₅ σ₆ hσ₆ σ₇ hσ₇
    obtain ⟨_, l, hl, hc⟩ := hσ 0
    have hpC : σ₄ ⟨free + 2, hf2⟩ = counterWord l := hC.trans hc
    obtain ⟨hfr1, hv0, hv1, hvals1⟩ := hL1 input σ₄ hp0 hp1 ⟨l, hl, hpC⟩ hpvals hpp
    rw [← hσ₅] at hfr1 hv0 hv1 hvals1
    have hcv : counterValue (σ₄ ⟨free + 2, hf2⟩) = l := by rw [hpC, counterValue_counterWord]
    rw [hcv] at hv1 hvals1
    have hσ4params : (fun p ↦ readRep σ₄ (params p)) = fun p ↦ readRep σ (params p) := by
      funext p
      unfold readRep
      rw [hlow4 _ (hparams p 0), hlow4 _ (hparams p 1)]
    have hσ6low : ∀ t : Fin k, t.val < free → σ₆ t = σ t := fun t ht ↦ by
      rw [hσ₆, Function.update_of_ne (hlow t ht).2.2.2, hfr1 t ht, hlow4 t ht]
    have hσ6params : (fun p ↦ readRep σ₆ (params p)) = fun p ↦ readRep σ (params p) := by
      funext p
      unfold readRep
      rw [hσ6low _ (hparams p 0), hσ6low _ (hparams p 1)]
    have hσ6V1 : σ₆ (srnV free hkV 1) = counterWord l := by
      rw [hσ₆, Function.update_of_ne (hRV 1).symm, hv1]
    have hσ6V0 : σ₆ (srnV free hkV 0) = [] := by
      rw [hσ₆, Function.update_of_ne (hRV 0).symm, hv0]
    have hσ6R : σ₆ ⟨free + 5, hf5⟩ = (σ (env 0 0)).reverse := by
      rw [hσ₆, Function.update_self, hfr1 _ (hY 0), hlow4 _ (hY 0)]
    have hσ6vals : ∀ l', readRep σ₆ (srnVals b free hk2 l') =
        evalSRNRep input (fun l ↦ repTransport (hs (.inl l) input) (s (.inl l) input).2)
          (fun i l ↦ repTransport (hs (stepDir i l) input) (s (stepDir i l) input).2)
          ⟨[], counterValue (σ₆ (srnV free hkV 1))⟩ l' fun p ↦ readRep σ₆ (params p) := by
      intro l'
      rw [hσ6V1, counterValue_counterWord, hσ6params]
      have hr := (hvals1 l').1
      rw [hσ4params] at hr
      unfold readRep
      rw [hσ₆, Function.update_of_ne (hvalsR l' 0), Function.update_of_ne (hvalsR l' 1)]
      change readRep σ₅ (srnVals b free hk2 l') = _
      rw [hr]
      exact phaseSuffix_congr_base input _ (fun l'' ↦ hbase l'') l l'
    have hσ6valsWF : ∀ l', WF M input.length σ₆ (srnVals b free hk2 l') := fun l' ↦ by
      obtain ⟨hw, l'', hl'', hc'⟩ := (hvals1 l').2
      refine ⟨?_, l'', hl'', ?_⟩
      · rw [hσ₆, Function.update_of_ne (hvalsR l' 0)]
        exact hw
      · rw [hσ₆, Function.update_of_ne (hvalsR l' 1)]
        exact hc'
    have hσ6pp : ∀ p, WF M input.length σ₆ (params p) := fun p ↦ by
      obtain ⟨hw, l'', hl'', hc'⟩ := hσ p.succ
      refine ⟨?_, l'', hl'', ?_⟩
      · rw [hσ6low _ (hparams p 0)]
        exact hw
      · rw [hσ6low _ (hparams p 1)]
        exact hc'
    have hσ6Rlen : (σ₆ ⟨free + 5, hf5⟩).length ≤ M := by
      rw [hσ6R, List.length_reverse]
      exact (hσ 0).1
    obtain ⟨hfr2, -, -, hvals2⟩ :=
      hL2 input σ₆ hσ6V0 ⟨l, hl, hσ6V1⟩ hσ6Rlen hσ6vals hσ6valsWF hσ6pp
    rw [← hσ₇] at hfr2 hvals2
    refine ⟨⟨hσ6V0, ⟨l, hl, hσ6V1⟩, hσ6Rlen, hσ6vals, hσ6valsWF, hσ6pp⟩, ?_, (hvals2 j).2⟩
    rw [(hvals2 j).1, hσ6R, List.reverse_reverse, hσ6V1, counterValue_counterWord, hσ6params, hc,
      counterValue_counterWord]
  refine ⟨_, TransformsIn.mono_time (TransformsIn.mono_pre hall ?_) ?_, ?_, ?_, ?_⟩
  · -- the precondition of the chain
    intro input σ _ hσ
    obtain ⟨hp0, hp1, hC, hpvals, hpp, hbase⟩ := hpre1 input σ hσ
    obtain ⟨_, l, hl, hc⟩ := hσ 0
    obtain ⟨hpre2, -, -⟩ := hrun input σ _ hσ (hσ4low input σ) hp0 hp1 hC hpvals hpp hbase
      _ rfl _ rfl _ rfl
    exact ⟨hparamsWF input σ hσ, trivial, trivial, trivial,
      ⟨hp0, hp1, ⟨l, hl, hC.trans hc⟩, hpvals, hpp⟩, trivial, hpre2, trivial⟩
  · -- the step bound
    intro n
    dsimp only [timeValue, copyRegTime]
    simp only [hT_def]
    omega
  · -- the output register
    intro input σ hσ
    obtain ⟨hp0, hp1, hC, hpvals, hpp, hbase⟩ := hpre1 input σ hσ
    obtain ⟨-, hval, -⟩ := hrun input σ _ hσ (hσ4low input σ) hp0 hp1 hC hpvals hpp hbase
      _ rfl _ rfl _ rfl
    have hcp : ∀ τ : Fin k → List Bool, readRep (Function.update (Function.update τ (out 0)
        (τ (srnVals b free hk2 j 0))) (out 1) (τ (srnVals b free hk2 j 1))) out =
        readRep τ (srnVals b free hk2 j) := fun τ ↦ by
      unfold readRep
      rw [Function.update_of_ne hout01, Function.update_self, Function.update_self]
    change readRep (Function.update (Function.update (_ : Fin k → List Bool) (out 0) _) (out 1) _)
      out = _
    rw [hcp, hval, hparams_def]
    rfl
  · -- the frame
    intro input σ t ht hto0 hto1
    change Function.update (Function.update (_ : Fin k → List Bool) (out 0) _) (out 1) _ t = σ t
    rw [Function.update_of_ne hto1, Function.update_of_ne hto0,
      hiter _ t (fun σ ↦ hB2fr input σ t ht), Function.update_of_ne (hlow t ht).2.2.2,
      hiter _ t (fun σ ↦ hB1fr input σ t ht), hσ4low input σ t ht]
  · -- the output register is well-formed
    intro input σ hσ
    obtain ⟨hp0, hp1, hC, hpvals, hpp, hbase⟩ := hpre1 input σ hσ
    obtain ⟨-, -, hwf⟩ := hrun input σ _ hσ (hσ4low input σ) hp0 hp1 hC hpvals hpp hbase
      _ rfl _ rfl _ rfl
    obtain ⟨hw, l, hl, hc⟩ := hwf
    refine ⟨?_, l, hl, ?_⟩
    · change (Function.update (Function.update (_ : Fin k → List Bool) (out 0) _) (out 1) _
        (out 0)).length ≤ M
      rw [Function.update_of_ne hout01, Function.update_self]
      exact hw
    · change Function.update (Function.update (_ : Fin k → List Bool) (out 0) _) (out 1) _
        (out 1) = _
      rw [Function.update_self]
      exact hc

end

end Geb.SizeBounded.Logspace.Machine
