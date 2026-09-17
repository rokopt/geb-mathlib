/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Comp
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The transformers of a recursion node's loop bodies

The two loops of a compiled recursion node share a middle: the dispatch on the
flag register to the step programs for that bit, each writing its scratch
register, followed by the copies of the scratch registers into the value
registers. The first loop's body reads the input bit at the cursor's length
into the flag before the middle and counts the cursor's length up and the
loop's counter down after it; the second loop's body pops the next bit of the
reversed word into the flag before the middle and pushes that bit onto the
cursor's word after it. {lit}`srnBody1_contract` and {lit}`srnBody2_contract`
state each body's contract under
{name}`Geb.SizeBounded.Logspace.Machine.TransformsIn` together with the
clauses of its transformer the loop invariants read: the tapes below the
first free one and the registers the body does not write are unchanged, the
counters and the cursor move as described, and the value registers hold the
steps' meanings at the environment the body received.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`StepsCorrect` — the steps of a bit are correct at the node's
  allocation, with their transformers named.
* {lit}`middleF`, {lit}`body1F`, {lit}`body2F` — the transformers of the
  middle and of the two loop bodies.

# Main statements

* {lit}`srnEnv_lt`, {lit}`srnEnv_cases`, {lit}`srnEnv_zero`,
  {lit}`srnEnv_castAdd`, {lit}`srnEnv_natAdd`, {lit}`srnEnv_injective` — the
  step environment lies below the scratch registers, its slots, and its
  injectivity.
* {lit}`srnSteps_contract` — the sequenced steps of a bit write the scratch
  registers.
* {lit}`srnMiddle_contract` — the dispatch and the copies write the value
  registers.
* {lit}`srnBody1_contract`, {lit}`srnBody2_contract` — the contracts of the
  two loop bodies.

# Tags

Turing machine, compilation, recursion, register allocation, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Geb.SizeBounded (finMax le_finMax)
open Geb.SizeBounded.Machine (Prog composeFin composeFin_of_lt Bounded copy const
  copy_transforms Transforms)

public section

/-- Every tape of the step environment lies below the scratch registers. -/
theorem srnEnv_lt {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k) (params : Fin a → Reg k)
    (hparams : ∀ p t, (params p t).val < free) :
    ∀ s t, (srnEnv free hk params s t).val < free + 6 + 2 * b := by
  intro s t
  unfold srnEnv
  refine Fin.cases ?_ (fun s ↦ ?_) s
  · rw [Fin.cons_zero]
    change free + (t : ℕ) < _
    have := t.isLt
    omega
  · rw [Fin.cons_succ]
    refine Fin.addCases (motive := fun s ↦ (Fin.append (srnVals b free hk) params s t).val <
      free + 6 + 2 * b) (fun l ↦ ?_) (fun p ↦ ?_) s
    · rw [Fin.append_left]
      change free + 6 + 2 * (l : ℕ) + (t : ℕ) < _
      have := l.isLt
      have := t.isLt
      omega
    · rw [Fin.append_right]
      have := hparams p t
      omega

/-- The value of every tape of the step environment, by the slot: the cursor at
slot zero, value register {lit}`l` at slot {lit}`l + 1`, and parameter {lit}`p`
at slot {lit}`b + p + 1`. -/
theorem srnEnv_cases {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k) (params : Fin a → Reg k)
    (s : Fin (b + a + 1)) (t : Fin 2) :
    (s = 0 ∧ (srnEnv free hk params s t).val = free + t) ∨
    (∃ l : Fin b, s = (Fin.castAdd a l).succ ∧
      (srnEnv free hk params s t).val = free + 6 + 2 * l + t) ∨
    (∃ p : Fin a, s = (Fin.natAdd b p).succ ∧ srnEnv free hk params s t = params p t) := by
  unfold srnEnv
  refine Fin.cases (Or.inl ⟨rfl, rfl⟩) (fun s ↦ ?_) s
  rw [Fin.cons_succ]
  refine Fin.addCases (motive := fun s ↦ (s.succ = 0 ∧ _) ∨
    (∃ l : Fin b, s.succ = (Fin.castAdd a l).succ ∧
      (Fin.append (srnVals b free hk) params s t).val = free + 6 + 2 * l + t) ∨
    (∃ p : Fin a, s.succ = (Fin.natAdd b p).succ ∧
      Fin.append (srnVals b free hk) params s t = params p t)) (fun l ↦ ?_) (fun p ↦ ?_) s
  · refine Or.inr (Or.inl ⟨l, rfl, ?_⟩)
    rw [Fin.append_left]
    rfl
  · refine Or.inr (Or.inr ⟨p, rfl, ?_⟩)
    rw [Fin.append_right]

/-- The step environment at slot zero is the cursor. -/
theorem srnEnv_zero {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k) (params : Fin a → Reg k) :
    srnEnv free hk params 0 = srnV free (by omega) := rfl

/-- The step environment at the slot of a value register is that register. -/
theorem srnEnv_castAdd {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k)
    (params : Fin a → Reg k) (l : Fin b) :
    srnEnv free hk params (Fin.castAdd a l).succ = srnVals b free hk l := by
  unfold srnEnv
  rw [Fin.cons_succ, Fin.append_left]

/-- The step environment at the slot of a parameter is that parameter. -/
theorem srnEnv_natAdd {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k)
    (params : Fin a → Reg k) (p : Fin a) :
    srnEnv free hk params (Fin.natAdd b p).succ = params p := by
  unfold srnEnv
  rw [Fin.cons_succ, Fin.append_right]

/-- The step environment is injective when the parameters are and lie below the
first free tape. -/
theorem srnEnv_injective {k a b : ℕ} (free : ℕ) (hk : free + 6 + 2 * b ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free)
    (hinj : Function.Injective fun x : Fin a × Fin 2 ↦ params x.1 x.2) :
    Function.Injective fun x : Fin (b + a + 1) × Fin 2 ↦ srnEnv free hk params x.1 x.2 := by
  intro x y hxy
  have hv := congrArg Fin.val hxy
  change (srnEnv free hk params x.1 x.2).val = (srnEnv free hk params y.1 y.2).val at hv
  have hx2 := x.2.isLt
  have hy2 := y.2.isLt
  rcases srnEnv_cases free hk params x.1 x.2 with ⟨hx, hxv⟩ | ⟨l, hx, hxv⟩ | ⟨p, hx, hxv⟩ <;>
    rcases srnEnv_cases free hk params y.1 y.2 with ⟨hy, hyv⟩ | ⟨l', hy, hyv⟩ | ⟨p', hy, hyv⟩
  · exact Prod.ext (hx.trans hy.symm) (Fin.ext (by omega))
  · exact absurd (hxv ▸ hyv ▸ hv) (by have := l'.isLt; omega)
  · exact absurd (hxv ▸ (congrArg Fin.val hyv) ▸ hv) (by have := hparams p' y.2; omega)
  · exact absurd (hxv ▸ hyv ▸ hv) (by have := l.isLt; omega)
  · have hl : l = l' := Fin.ext (by have := l.isLt; have := l'.isLt; omega)
    subst hl
    exact Prod.ext (hx.trans hy.symm) (Fin.ext (by omega))
  · exact absurd (hxv ▸ (congrArg Fin.val hyv) ▸ hv) (by have := hparams p' y.2; omega)
  · exact absurd ((congrArg Fin.val hxv) ▸ hyv ▸ hv) (by have := hparams p x.2; omega)
  · exact absurd ((congrArg Fin.val hxv) ▸ hyv ▸ hv) (by have := hparams p x.2; omega)
  · have hpp := hinj (show (fun x : Fin a × Fin 2 ↦ params x.1 x.2) (p, x.2) =
      (fun x : Fin a × Fin 2 ↦ params x.1 x.2) (p', y.2) from hxv.symm.trans (hxy.trans hyv))
    have h1 := congrArg Prod.fst hpp
    have h2 := congrArg Prod.snd hpp
    exact Prod.ext (hx.trans ((congrArg (fun p ↦ (Fin.natAdd b p).succ) h1).trans hy.symm)) h2

/-- The steps of a bit are correct at the node's allocation: each step's program
has a transformer under contract at the step environment, writing the step's
meaning into its scratch register, leaving the other tapes below the node's
scratch need alone, and leaving its scratch register well-formed. -/
@[expose] def StepsCorrect {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (M : ℕ) (steps : Fin b → Prog k)
    (stepRep : Fin b → List Bool → RepSem (b + a + 1)) (T : ℕ → ℕ)
    (G : Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool) : Prop :=
  ∀ l, TransformsIn (steps l).tm
      (fun input σ ↦ EnvWF M input σ (srnEnv (b := b) free (by omega) params)) (G l) T (bound M) ∧
    (∀ input σ, EnvWF M input σ (srnEnv (b := b) free (by omega) params) →
      readRep (G l input σ) (srnScr b free (by omega) l) =
        stepRep l input fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
    (∀ input σ (t : Fin k), t.val < free + (4 * b + 6) → t ≠ srnScr b free (by omega) l 0 →
      t ≠ srnScr b free (by omega) l 1 → G l input σ t = σ t) ∧
    (∀ input σ, EnvWF M input σ (srnEnv (b := b) free (by omega) params) →
      WF M input.length (G l input σ) (srnScr b free (by omega) l))

/-- The meaning of a correct step is within the word bound and the input's
length at every well-formed environment. -/
theorem stepRep_bounds {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (M : ℕ) (steps : Fin b → Prog k)
    (stepRep : Fin b → List Bool → RepSem (b + a + 1)) (T : ℕ → ℕ)
    (G : Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (hG : StepsCorrect free hk params M steps stepRep T G) (l : Fin b) (input : List Bool)
    (σ : Fin k → List Bool) (hσ : EnvWF M input σ (srnEnv (b := b) free (by omega) params)) :
    (stepRep l input fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)).word.length ≤ M ∧
    (stepRep l input fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)).suffix ≤
      input.length := by
  obtain ⟨hw, l', hl', hc⟩ := (hG l).2.2.2 input σ hσ
  rw [← (hG l).2.1 input σ hσ]
  refine ⟨hw, ?_⟩
  change counterValue (G l input σ (srnScr b free (by omega) l 1)) ≤ _
  rw [hc, counterValue_counterWord]
  exact hl'

/-- The sequenced steps of a bit write the scratch registers: the composite of
their transformers leaves every tape below the scratch registers alone and
leaves scratch register {lit}`l` holding the meaning of step {lit}`l` at the
environment received, well-formed. -/
theorem srnSteps_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ)
    (steps : Fin b → Prog k) (stepRep : Fin b → List Bool → RepSem (b + a + 1)) (T : ℕ → ℕ)
    (G : Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (hG : StepsCorrect free hk params M steps stepRep T G) :
    TransformsIn (Prog.seqFin b steps).tm
      (fun input σ ↦ EnvWF M input σ (srnEnv (b := b) free (by omega) params))
      (fun input σ ↦ composeFin b (fun l ↦ G l input) σ) (fun n ↦ b * T n + 1) (bound M) ∧
    (∀ input σ (t : Fin k), t.val < free + 6 + 2 * b →
      composeFin b (fun l ↦ G l input) σ t = σ t) ∧
    (∀ input σ, EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      composeFin b (fun l ↦ G l input) σ (srnScr b free (by omega) l 0) =
        (stepRep l input fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)).word ∧
      composeFin b (fun l ↦ G l input) σ (srnScr b free (by omega) l 1) =
        counterWord (stepRep l input
          fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)).suffix) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hk4 : free + 6 + 4 * b ≤ k := by omega
  have hscr0 : ∀ l : Fin b, (srnScr b free hk4 l 0 : ℕ) = free + 6 + 2 * b + 2 * l :=
    fun l ↦ by change free + 6 + 2 * b + 2 * (l : ℕ) + 0 = _; omega
  have hscr1 : ∀ l : Fin b, (srnScr b free hk4 l 1 : ℕ) = free + 6 + 2 * b + 2 * l + 1 :=
    fun l ↦ rfl
  have henvlt := srnEnv_lt free hk2 params hparams
  -- the environment survives every step
  have hpres : ∀ (l : Fin b) input σ, EnvWF M input σ (srnEnv free hk2 params) →
      EnvWF M input (G l input σ) (srnEnv free hk2 params) :=
    fun l input σ hwf ↦ envWF_of_frame hwf fun s t ↦ (hG l).2.2.1 input σ _
      (by have := henvlt s t; omega)
      (Fin.ne_of_val_ne (by rw [hscr0]; have := henvlt s t; omega))
      (Fin.ne_of_val_ne (by rw [hscr1]; have := henvlt s t; omega))
  have hframe : ∀ (l : Fin b) input σ (t : Fin k), t.val < free + 6 + 2 * b →
      G l input σ t = σ t := fun l input σ t ht ↦
    (hG l).2.2.1 input σ t (by omega)
      (Fin.ne_of_val_ne (by rw [hscr0]; omega)) (Fin.ne_of_val_ne (by rw [hscr1]; omega))
  refine ⟨?_, ?_, ?_⟩
  · exact TransformsIn.mono_pre (TransformsIn.seqFin (bound M) T b _ _
      (fun _ input σ ↦ EnvWF M input σ (srnEnv free hk2 params)) G fun l ↦ (hG l).1)
      fun input σ _ hσ ↦ preFin_of_invariant _ b G hpres input σ hσ
  · intro input σ t ht
    exact composeFin_of_lt (free + 6 + 2 * b) b (fun l ↦ G l input)
      (fun l τ j hj ↦ hframe l input τ j hj) σ t ht
  · intro input σ hσ l
    exact composeFin_fresh2 (free + 6 + 2 * b)
      (fun σ ↦ EnvWF M input σ (srnEnv free hk2 params)) b (by omega)
      (fun l ↦ G l input)
      (fun l σ ↦ (stepRep l input fun s ↦ readRep σ (srnEnv free hk2 params s)).word)
      (fun l σ ↦ counterWord
        (stepRep l input fun s ↦ readRep σ (srnEnv free hk2 params s)).suffix)
      (fun l σ ↦ hpres l input σ)
      (fun l τ τ' hτ ↦ congrArg (fun x ↦ (stepRep l input x).word) (funext fun s ↦ by
        unfold readRep
        rw [hτ _ (henvlt s 0), hτ _ (henvlt s 1)]))
      (fun l τ τ' hτ ↦ congrArg (fun x ↦ counterWord (stepRep l input x).suffix)
        (funext fun s ↦ by
          unfold readRep
          rw [hτ _ (henvlt s 0), hτ _ (henvlt s 1)]))
      (fun l τ hτ ↦ congrArg Rep.word ((hG l).2.1 input τ hτ))
      (fun l τ hτ ↦ by
        obtain ⟨_, l', _, hc⟩ := (hG l).2.2.2 input τ hτ
        have hsuf := congrArg Rep.suffix ((hG l).2.1 input τ hτ)
        change counterValue (G l input τ (srnScr b free hk4 l 1)) = _ at hsuf
        rw [← hsuf, hc, counterValue_counterWord]
        exact hc)
      (fun l τ i hi h0 h1 ↦ (hG l).2.2.1 input τ i (by omega) h0 h1) σ hσ l

/-- The transformer of the middle of a loop body: the steps for the flag's bit
into the scratch registers, then the copies into the value registers. -/
@[expose] def middleF {k b : ℕ} (F : Fin k) (vals scr : Fin b → Reg k)
    (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (input : List Bool) (σ : Fin k → List Bool) : Fin k → List Bool :=
  composeFin b (fun l σ ↦ Function.update (Function.update σ (vals l 0) (σ (scr l 0)))
    (vals l 1) (σ (scr l 1)))
    (if (σ F).getLast? = some true then composeFin b (fun l ↦ G true l input) σ
      else composeFin b (fun l ↦ G false l input) σ)

/-- The middle of a loop body, the dispatch on the flag to the steps for that
bit and the copies into the value registers, transforms by
{name}`middleF`: on a valuation whose flag holds one bit and whose step
environment is well-formed, every tape below the value registers is
unchanged, and value register {lit}`l` holds the meaning of step {lit}`l` for
that bit at the environment received, well-formed. -/
theorem srnMiddle_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ)
    (steps : Bool → Fin b → Prog k) (stepRep : Bool → Fin b → List Bool → RepSem (b + a + 1))
    (T : ℕ → ℕ) (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (hG : ∀ i, StepsCorrect free hk params M (steps i) (stepRep i) T (G i)) :
    TransformsIn (srnMiddle ⟨free + 4, by omega⟩ (srnVals b free (by omega))
        (srnScr b free (by omega)) (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm
      (fun input σ ↦ EnvWF M input σ (srnEnv (b := b) free (by omega) params))
      (middleF ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G)
      (fun n ↦ (1 + max (b * T n + 1) (b * T n + 1)) + (b * copyRegTime (bound M n) + 1))
      (bound M) ∧
    (∀ input σ (t : Fin k), t.val < free + 6 →
      middleF ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G
        input σ t = σ t) ∧
    (∀ input σ (c : Bool), σ ⟨free + 4, by omega⟩ = [c] →
      EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      readRep (middleF ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega))
        G input σ) (srnVals b free (by omega) l) =
        stepRep c l input (fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
      WF M input.length (middleF ⟨free + 4, by omega⟩ (srnVals b free (by omega))
        (srnScr b free (by omega)) G input σ) (srnVals b free (by omega) l)) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hk4 : free + 6 + 4 * b ≤ k := by omega
  have hvals : ∀ (l : Fin b) (t : Fin 2), (srnVals b free hk2 l t : ℕ) = free + 6 + 2 * l + t :=
    fun _ _ ↦ rfl
  have hscr : ∀ (l : Fin b) (t : Fin 2),
      (srnScr b free hk4 l t : ℕ) = free + 6 + 2 * b + 2 * l + t := fun _ _ ↦ rfl
  have hF : ∀ (l : Fin b) (t : Fin 2), (⟨free + 4, by omega⟩ : Fin k) ≠ srnVals b free hk2 l t :=
    fun l t ↦ Fin.ne_of_val_ne (by
      rw [hvals]
      change free + 4 ≠ free + 6 + 2 * (l : ℕ) + (t : ℕ)
      omega)
  have hvinj : Function.Injective fun x : Fin b × Fin 2 ↦ srnVals b free hk2 x.1 x.2 := by
    intro x y hxy
    have := congrArg Fin.val hxy
    rw [hvals, hvals] at this
    have := x.2.isLt
    have := y.2.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hvs : ∀ l t l' t', srnVals b free hk2 l t ≠ srnScr b free hk4 l' t' :=
    fun l t l' t' ↦ Fin.ne_of_val_ne (by rw [hvals, hscr]; have := l.isLt; have := t.isLt; omega)
  obtain ⟨hT0, hfr0, hout0⟩ := srnSteps_contract free hk params hparams M (steps false)
    (stepRep false) T (G false) (hG false)
  obtain ⟨hT1, hfr1, hout1⟩ := srnSteps_contract free hk params hparams M (steps true)
    (stepRep true) T (G true) (hG true)
  -- the copies
  have hcopy : ∀ l : Fin b, TransformsIn (copyReg (srnScr b free hk4 l) (srnVals b free hk2 l)).tm
      (fun _ _ ↦ True)
      (fun _ σ ↦ Function.update (Function.update σ (srnVals b free hk2 l 0)
        (σ (srnScr b free hk4 l 0))) (srnVals b free hk2 l 1) (σ (srnScr b free hk4 l 1)))
      (fun n ↦ copyRegTime (bound M n)) (bound M) := by
    intro l
    have h1 := Transforms.toIn_of (fun n ↦ copy_transforms (srnScr b free hk4 l 0)
      (srnVals b free hk2 l 0) (hvs l 0 l 0).symm (bound M n)) (fun _ _ ↦ True)
      fun input σ hB _ ↦ hB.update (hB _)
    have h2 := Transforms.toIn_of (fun n ↦ copy_transforms (srnScr b free hk4 l 1)
      (srnVals b free hk2 l 1) (hvs l 1 l 1).symm (bound M n)) (fun _ _ ↦ True)
      fun input σ hB _ ↦ hB.update (hB _)
    refine TransformsIn.congr (TransformsIn.mono_time
      ((h1.seq h2).mono_pre fun _ _ _ _ ↦ ⟨trivial, trivial⟩) fun n ↦ by
        unfold copyRegTime
        omega) ?_
    intro input σ _
    funext t
    change Function.update (Function.update σ (srnVals b free hk2 l 0) (σ (srnScr b free hk4 l 0)))
      (srnVals b free hk2 l 1) (Function.update σ (srnVals b free hk2 l 0)
        (σ (srnScr b free hk4 l 0)) (srnScr b free hk4 l 1)) t = _
    rw [Function.update_of_ne (hvs l 0 l 1).symm]
  have hcopies := TransformsIn.seqFin (bound M) (fun n ↦ copyRegTime (bound M n)) b _ _
    (fun _ _ _ ↦ True) _ hcopy
  have hcopy2 := composeFin_copy2 (srnVals b free hk2) (srnScr b free hk4) hvinj hvs
  have hmid := TransformsIn.seq (TransformsIn.caseReg (⟨free + 4, by omega⟩ : Fin k) hT0 hT1)
    hcopies
  refine ⟨?_, ?_, ?_⟩
  · refine TransformsIn.mono_pre (TransformsIn.congr hmid fun input σ _ ↦ rfl) ?_
    intro input σ _ hσ
    refine ⟨?_, preFin_of_invariant (fun _ _ ↦ True) b _ (fun _ _ _ _ ↦ trivial) input _ trivial⟩
    by_cases h : (σ ⟨free + 4, by omega⟩).getLast? = some true
    · rw [ite_eq_left h]
      exact hσ
    · rw [ite_eq_right h]
      exact hσ
  · intro input σ t ht
    unfold middleF
    rw [(hcopy2 _).2 t (fun l b ↦ Fin.ne_of_val_ne (by rw [hvals]; omega))]
    by_cases h : (σ ⟨free + 4, by omega⟩).getLast? = some true
    · rw [ite_eq_left h]
      exact hfr1 input σ t (by omega)
    · rw [ite_eq_right h]
      exact hfr0 input σ t (by omega)
  · intro input σ c hc hσ l
    have hbits := fun (c : Bool) ↦ stepRep_bounds free hk params M (steps c) (stepRep c) T (G c)
      (hG c) l input σ hσ
    unfold middleF
    rw [hc]
    cases c with
    | false =>
      rw [List.getLast?_singleton, ite_eq_right (by decide)]
      obtain ⟨h0, h1⟩ := hout0 input σ hσ l
      refine ⟨?_, ?_, ?_⟩
      · unfold readRep
        rw [(hcopy2 _).1 l 0, (hcopy2 _).1 l 1, h0, h1, counterValue_counterWord]
        rfl
      · rw [(hcopy2 _).1 l 0, h0]
        exact (hbits false).1
      · refine ⟨_, (hbits false).2, ?_⟩
        rw [(hcopy2 _).1 l 1, h1]
    | true =>
      rw [List.getLast?_singleton, ite_eq_left rfl]
      obtain ⟨h0, h1⟩ := hout1 input σ hσ l
      refine ⟨?_, ?_, ?_⟩
      · unfold readRep
        rw [(hcopy2 _).1 l 0, (hcopy2 _).1 l 1, h0, h1, counterValue_counterWord]
        rfl
      · rw [(hcopy2 _).1 l 0, h0]
        exact (hbits true).1
      · refine ⟨_, (hbits true).2, ?_⟩
        rw [(hcopy2 _).1 l 1, h1]

/-- The tapes of a recursion node's layout, by value. -/
theorem srnV_val {k : ℕ} (free : ℕ) (hk : free + 2 ≤ k) (t : Fin 2) :
    (srnV free hk t : ℕ) = free + t := rfl

/-- The transformer of {name}`readInput`. -/
@[expose] def readF {k : ℕ} (C S F : Fin k) (input : List Bool) (σ : Fin k → List Bool) :
    Fin k → List Bool :=
  Function.update (Function.update σ S []) F [bitAt input (counterValue (σ C))]

/-- The transformer of {name}`inc`. -/
@[expose] def incF {k : ℕ} (C : Fin k) (_ : List Bool) (σ : Fin k → List Bool) :
    Fin k → List Bool :=
  Function.update σ C (incL (σ C).reverse).reverse

/-- The transformer of {name}`dec`. -/
@[expose] def decF {k : ℕ} (C : Fin k) (_ : List Bool) (σ : Fin k → List Bool) :
    Fin k → List Bool :=
  Function.update σ C (decL (σ C).reverse).reverse

/-- The transformer of {name}`pop`. -/
@[expose] def popF {k : ℕ} (R F : Fin k) (_ : List Bool) (σ : Fin k → List Bool) :
    Fin k → List Bool :=
  Function.update (Function.update σ F (σ R).head?.toList) R (σ R).tail

/-- The transformer of {name}`push`. -/
@[expose] def pushF {k : ℕ} (c : Bool) (U : Fin k) (_ : List Bool) (σ : Fin k → List Bool) :
    Fin k → List Bool :=
  Function.update σ U (c :: σ U)

/-- The transformer of the branch on a register's last bit. -/
@[expose] def caseF {k : ℕ} (R : Fin k) (P Q : List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (input : List Bool) (σ : Fin k → List Bool) : Fin k → List Bool :=
  if (σ R).getLast? = some true then Q input σ else P input σ

/-- The transformer of the first loop's body: the read of the input bit into
the flag, the middle, the increment of the cursor's length and the decrement of
the loop's counter. -/
@[expose] def body1F {k b : ℕ} (V : Reg k) (CR S F : Fin k) (vals scr : Fin b → Reg k)
    (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (input : List Bool) (σ : Fin k → List Bool) : Fin k → List Bool :=
  decF CR input (incF (V 1) input (middleF F vals scr G input (readF (V 1) S F input σ)))

/-- The transformer of the second loop's body: the pop of the reversed word's
head bit into the flag, the middle, and the push of the flag's bit onto the
cursor's word. -/
@[expose] def body2F {k b : ℕ} (V : Reg k) (R F : Fin k) (vals scr : Fin b → Reg k)
    (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (input : List Bool) (σ : Fin k → List Bool) : Fin k → List Bool :=
  caseF F (pushF false (V 0)) (pushF true (V 0)) input
    (middleF F vals scr G input (popF R F input σ))

/-- The contract of the first loop's body: from a valuation whose cursor holds
a counter below the input's length and whose step environment is well-formed,
the body leaves the tapes below the first free one and the cursor's word
alone, counts the cursor's length up and the loop's counter down, and leaves
each value register holding its step's meaning for the input bit at the
cursor's length, well-formed. -/
theorem srnBody1_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ)
    (steps : Bool → Fin b → Prog k) (stepRep : Bool → Fin b → List Bool → RepSem (b + a + 1))
    (T : ℕ → ℕ) (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (hG : ∀ i, StepsCorrect free hk params M (steps i) (stepRep i) T (G i)) :
    TransformsIn (srnBody1 (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega))
        (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm
      (fun input σ ↦ (∃ j, σ (srnV free (by omega) 1) = counterWord j ∧ j < input.length) ∧
        EnvWF M input σ (srnEnv (b := b) free (by omega) params))
      (body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G)
      (fun n ↦ b * T n + 1 + body1Time b (bound M n) n) (bound M) ∧
    (∀ input σ (t : Fin k), t.val < free →
      body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ t =
        σ t) ∧
    (∀ input σ, body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        (srnV free (by omega) 0) = σ (srnV free (by omega) 0)) ∧
    (∀ input σ j, σ (srnV free (by omega) 1) = counterWord j →
      body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        (srnV free (by omega) 1) = counterWord (j + 1)) ∧
    (∀ input σ, body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        ⟨free + 2, by omega⟩ = (decL (σ ⟨free + 2, by omega⟩).reverse).reverse) ∧
    (∀ input σ j, σ (srnV free (by omega) 1) = counterWord j → j < input.length →
      EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      readRep (body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ)
        (srnVals b free (by omega) l) =
        stepRep (bitAt input j) l input
          (fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
      WF M input.length (body1F (srnV free (by omega)) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ)
        (srnVals b free (by omega) l)) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hk4 : free + 6 + 4 * b ≤ k := by omega
  have hkV : free + 2 ≤ k := by omega
  have hf2 : free + 2 < k := by omega
  have hf3 : free + 3 < k := by omega
  have hf4 : free + 4 < k := by omega
  have hV1 : (srnV free hkV 1 : ℕ) = free + 1 := rfl
  have hV0 : (srnV free hkV 0 : ℕ) = free := rfl
  have hvals : ∀ (l : Fin b) (t : Fin 2), (srnVals b free hk2 l t : ℕ) = free + 6 + 2 * l + t :=
    fun _ _ ↦ rfl
  -- tape inequalities
  have hV1S : srnV free hkV 1 ≠ ⟨free + 3, by omega⟩ :=
    Fin.ne_of_val_ne (by rw [hV1]; change free + 1 ≠ free + 3; omega)
  have hV1F : srnV free hkV 1 ≠ ⟨free + 4, by omega⟩ :=
    Fin.ne_of_val_ne (by rw [hV1]; change free + 1 ≠ free + 4; omega)
  have hSF : (⟨free + 3, by omega⟩ : Fin k) ≠ ⟨free + 4, by omega⟩ :=
    Fin.ne_of_val_ne (by change free + 3 ≠ free + 4; omega)
  have hCRV1 : (⟨free + 2, by omega⟩ : Fin k) ≠ srnV free hkV 1 :=
    Fin.ne_of_val_ne (by rw [hV1]; change free + 2 ≠ free + 1; omega)
  have henvS : ∀ s t, srnEnv free hk2 params s t ≠ ⟨free + 3, by omega⟩ := fun s t ↦ by
    rcases srnEnv_cases free hk2 params s t with ⟨_, hv⟩ | ⟨l, _, hv⟩ | ⟨p, _, hv⟩
    · exact Fin.ne_of_val_ne (by rw [hv]; change free + (t : ℕ) ≠ free + 3; have := t.isLt; omega)
    · exact Fin.ne_of_val_ne (by rw [hv]; change _ ≠ free + 3; omega)
    · rw [hv]
      exact Fin.ne_of_val_ne (by change _ ≠ free + 3; have := hparams p t; omega)
  have henvF : ∀ s t, srnEnv free hk2 params s t ≠ ⟨free + 4, by omega⟩ := fun s t ↦ by
    rcases srnEnv_cases free hk2 params s t with ⟨_, hv⟩ | ⟨l, _, hv⟩ | ⟨p, _, hv⟩
    · exact Fin.ne_of_val_ne (by rw [hv]; change free + (t : ℕ) ≠ free + 4; have := t.isLt; omega)
    · exact Fin.ne_of_val_ne (by rw [hv]; change _ ≠ free + 4; omega)
    · rw [hv]
      exact Fin.ne_of_val_ne (by change _ ≠ free + 4; have := hparams p t; omega)
  -- the components
  have hread := TransformsIn.congr (readInput_transformsIn (srnV free hkV 1) ⟨free + 3, by omega⟩
    ⟨free + 4, by omega⟩ hV1S hV1F hSF (bound M) (fun n ↦ by unfold bound; omega))
    (fun _ _ _ ↦ rfl : ∀ input σ, _ → _ = readF (srnV free hkV 1) ⟨free + 3, by omega⟩
      ⟨free + 4, by omega⟩ input σ)
  obtain ⟨hmidT, hmidfr, hmidout⟩ :=
    srnMiddle_contract free hk params hparams M steps stepRep T G hG
  have hinc := TransformsIn.congr (Transforms.toIn_of (fun n ↦ inc_transforms (srnV free hkV 1)
    (bound M n))
    (fun input σ ↦ ∃ j, σ (srnV free hkV 1) = counterWord j ∧ j + 1 ≤ input.length)
    (fun input σ hB ⟨j, hj, hjn⟩ ↦ hB.update (by
      rw [hj, incL_counterWord]
      exact length_counterWord_le_bound hjn)))
    (fun _ _ _ ↦ rfl : ∀ input σ, _ → _ = incF (srnV free hkV 1) input σ)
  have hdec := TransformsIn.congr (Transforms.toIn_of (fun n ↦ dec_transforms
    (⟨free + 2, by omega⟩ : Fin k) (bound M n)) (fun _ _ ↦ True) (fun input σ hB _ ↦ hB.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by rw [List.length_reverse]; exact hB _))))
    (fun _ _ _ ↦ rfl : ∀ input σ, _ → _ = decF (⟨free + 2, by omega⟩ : Fin k) input σ)
  have h := hread.seq (hmidT.seq (hinc.seq hdec))
  -- the valuations along the body, on a valuation satisfying the precondition
  have hfr1 : ∀ (input : List Bool) (σ : Fin k → List Bool) (t : Fin k),
      t ≠ ⟨free + 3, by omega⟩ → t ≠ ⟨free + 4, by omega⟩ →
      readF (srnV free hkV 1) ⟨free + 3, by omega⟩ ⟨free + 4, by omega⟩ input σ t = σ t :=
    fun input σ t h3 h4 ↦ by
      unfold readF
      rw [Function.update_of_ne h4, Function.update_of_ne h3]
  have henv1 : ∀ input σ, EnvWF M input σ (srnEnv free hk2 params) →
      EnvWF M input (readF (srnV free hkV 1) ⟨free + 3, by omega⟩ ⟨free + 4, by omega⟩ input σ)
        (srnEnv free hk2 params) :=
    fun input σ hσ ↦ envWF_of_frame hσ fun s t ↦ hfr1 input σ _ (henvS s t) (henvF s t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : (srnBody1 (srnV free hkV) ⟨free + 2, hf2⟩ ⟨free + 3, hf3⟩ ⟨free + 4, hf4⟩
        (srnVals b free hk2) (srnScr b free hk4) (Prog.seqFin b (steps false))
        (Prog.seqFin b (steps true))).tm =
        Geb.SizeBounded.Machine.seq (readInput (srnV free hkV 1) ⟨free + 3, hf3⟩ ⟨free + 4, hf4⟩)
          (Geb.SizeBounded.Machine.seq (srnMiddle ⟨free + 4, hf4⟩ (srnVals b free hk2)
            (srnScr b free hk4) (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm
            (Geb.SizeBounded.Machine.seq (inc (srnV free hkV 1)) (dec ⟨free + 2, hf2⟩))) := rfl
    rw [hm]
    refine TransformsIn.mono_time (TransformsIn.mono_pre (TransformsIn.congr h
      fun input σ _ ↦ (rfl : _ = body1F (srnV free hkV) ⟨free + 2, hf2⟩ ⟨free + 3, hf3⟩
        ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input σ)) ?_) ?_
    · intro input σ _ ⟨⟨j, hj, hjn⟩, hσ⟩
      refine ⟨⟨j, hj, hjn⟩, henv1 input σ hσ, ⟨j, ?_, hjn⟩, trivial⟩
      rw [hmidfr input _ _ (by rw [hV1]; omega), hfr1 input σ _ hV1S hV1F, hj]
    · intro n
      unfold body1Time
      rw [Nat.max_self]
      omega
  · intro input σ t ht
    unfold body1F decF incF
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 2; omega)),
      Function.update_of_ne (Fin.ne_of_val_ne (by rw [hV1]; omega)),
      hmidfr input _ t (by omega), hfr1 input σ t
        (Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 3; omega))
        (Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 4; omega))]
  · intro input σ
    unfold body1F decF incF
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by rw [hV0]; change free ≠ free + 2; omega)),
      Function.update_of_ne (Fin.ne_of_val_ne (by rw [hV0, hV1]; omega)),
      hmidfr input _ _ (by rw [hV0]; omega), hfr1 input σ _
        (Fin.ne_of_val_ne (by rw [hV0]; change free ≠ free + 3; omega))
        (Fin.ne_of_val_ne (by rw [hV0]; change free ≠ free + 4; omega))]
  · intro input σ j hj
    unfold body1F decF incF
    rw [Function.update_of_ne hCRV1.symm, Function.update_self,
      hmidfr input _ _ (by rw [hV1]; omega), hfr1 input σ _ hV1S hV1F, hj, incL_counterWord]
  · intro input σ
    unfold body1F decF incF
    rw [Function.update_self, Function.update_of_ne hCRV1,
      hmidfr input _ _ (by change free + 2 < _; omega), hfr1 input σ _
        (Fin.ne_of_val_ne (by change free + 2 ≠ free + 3; omega))
        (Fin.ne_of_val_ne (by change free + 2 ≠ free + 4; omega))]
  · intro input σ j hj hjn hσ l
    have hflag : readF (srnV free hkV 1) ⟨free + 3, by omega⟩ ⟨free + 4, by omega⟩ input σ
        ⟨free + 4, by omega⟩ = [bitAt input j] := by
      unfold readF
      rw [Function.update_self, hj, counterValue_counterWord]
    obtain ⟨hout, hwf⟩ := hmidout input _ (bitAt input j) hflag (henv1 input σ hσ) l
    have hvt : ∀ t, body1F (srnV free hkV) ⟨free + 2, by omega⟩ ⟨free + 3, by omega⟩
        ⟨free + 4, by omega⟩ (srnVals b free hk2) (srnScr b free hk4) G input σ
        (srnVals b free hk2 l t) =
        middleF ⟨free + 4, by omega⟩ (srnVals b free hk2) (srnScr b free hk4) G input
          (readF (srnV free hkV 1) ⟨free + 3, by omega⟩ ⟨free + 4, by omega⟩ input σ)
          (srnVals b free hk2 l t) :=
      fun t ↦ by
        unfold body1F decF incF
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by rw [hvals]; change _ ≠ free + 2; omega)),
          Function.update_of_ne (Fin.ne_of_val_ne (by rw [hvals, hV1]; omega))]
    have hread : ∀ τ (r : Reg k), readRep τ r = ⟨τ (r 0), counterValue (τ (r 1))⟩ := fun _ _ ↦ rfl
    refine ⟨?_, ?_⟩
    · rw [hread, hvt 0, hvt 1, ← hread, hout]
      refine congrArg _ (funext fun s ↦ ?_)
      rw [hread, hread, hfr1 input σ _ (henvS s 0) (henvF s 0),
        hfr1 input σ _ (henvS s 1) (henvF s 1)]
    · obtain ⟨hw, l', hl', hc⟩ := hwf
      refine ⟨?_, l', hl', ?_⟩
      · rw [hvt 0]
        exact hw
      · rw [hvt 1]
        exact hc

/-- The contract of the second loop's body: from a valuation whose reversed
word register holds {lit}`c :: r`, whose cursor's word is below the word bound
and whose step environment is well-formed, the body leaves the tapes below the
first free one and the cursor's length alone, leaves the reversed word register
holding {lit}`r`, pushes {lit}`c` onto the cursor's word, and leaves each value
register holding its step's meaning for {lit}`c`, well-formed. -/
theorem srnBody2_contract {k a b : ℕ} (free : ℕ) (hk : free + (4 * b + 6) ≤ k)
    (params : Fin a → Reg k) (hparams : ∀ p t, (params p t).val < free) (M : ℕ)
    (steps : Bool → Fin b → Prog k) (stepRep : Bool → Fin b → List Bool → RepSem (b + a + 1))
    (T : ℕ → ℕ) (G : Bool → Fin b → List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (hG : ∀ i, StepsCorrect free hk params M (steps i) (stepRep i) T (G i)) :
    TransformsIn (srnBody2 (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega))
        (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm
      (fun input σ ↦ (σ (srnV free (by omega) 0)).length < M ∧
        EnvWF M input σ (srnEnv (b := b) free (by omega) params))
      (body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G)
      (fun n ↦ b * T n + 1 + body2Time b (bound M n)) (bound M) ∧
    (∀ input σ (t : Fin k), t.val < free →
      body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ t = σ t) ∧
    (∀ input σ, body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        (srnV free (by omega) 1) = σ (srnV free (by omega) 1)) ∧
    (∀ input σ (c : Bool) (r : List Bool), σ ⟨free + 5, by omega⟩ = c :: r →
      body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        ⟨free + 5, by omega⟩ = r ∧
      body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ
        (srnV free (by omega) 0) = c :: σ (srnV free (by omega) 0)) ∧
    (∀ input σ (c : Bool) (r : List Bool), σ ⟨free + 5, by omega⟩ = c :: r →
      EnvWF M input σ (srnEnv (b := b) free (by omega) params) → ∀ l,
      readRep (body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ)
        (srnVals b free (by omega) l) =
        stepRep c l input (fun s ↦ readRep σ (srnEnv (b := b) free (by omega) params s)) ∧
      WF M input.length (body2F (srnV free (by omega)) ⟨free + 5, by omega⟩ ⟨free + 4, by omega⟩
        (srnVals b free (by omega)) (srnScr b free (by omega)) G input σ)
        (srnVals b free (by omega) l)) := by
  have hk2 : free + 6 + 2 * b ≤ k := by omega
  have hk4 : free + 6 + 4 * b ≤ k := by omega
  have hkV : free + 2 ≤ k := by omega
  have hf4 : free + 4 < k := by omega
  have hf5 : free + 5 < k := by omega
  have hV1 : (srnV free hkV 1 : ℕ) = free + 1 := rfl
  have hV0 : (srnV free hkV 0 : ℕ) = free := rfl
  have hvals : ∀ (l : Fin b) (t : Fin 2), (srnVals b free hk2 l t : ℕ) = free + 6 + 2 * l + t :=
    fun _ _ ↦ rfl
  -- tape inequalities
  have hRF : (⟨free + 5, hf5⟩ : Fin k) ≠ ⟨free + 4, hf4⟩ :=
    Fin.ne_of_val_ne (by change free + 5 ≠ free + 4; omega)
  have henvR : ∀ s t, srnEnv free hk2 params s t ≠ ⟨free + 5, hf5⟩ := fun s t ↦ by
    rcases srnEnv_cases free hk2 params s t with ⟨_, hv⟩ | ⟨l, _, hv⟩ | ⟨p, _, hv⟩
    · exact Fin.ne_of_val_ne (by rw [hv]; change free + (t : ℕ) ≠ free + 5; have := t.isLt; omega)
    · exact Fin.ne_of_val_ne (by rw [hv]; change _ ≠ free + 5; omega)
    · rw [hv]
      exact Fin.ne_of_val_ne (by change _ ≠ free + 5; have := hparams p t; omega)
  have henvF : ∀ s t, srnEnv free hk2 params s t ≠ ⟨free + 4, hf4⟩ := fun s t ↦ by
    rcases srnEnv_cases free hk2 params s t with ⟨_, hv⟩ | ⟨l, _, hv⟩ | ⟨p, _, hv⟩
    · exact Fin.ne_of_val_ne (by rw [hv]; change free + (t : ℕ) ≠ free + 4; have := t.isLt; omega)
    · exact Fin.ne_of_val_ne (by rw [hv]; change _ ≠ free + 4; omega)
    · rw [hv]
      exact Fin.ne_of_val_ne (by change _ ≠ free + 4; have := hparams p t; omega)
  have hV0ne : srnV free hkV 0 ≠ ⟨free + 4, hf4⟩ :=
    Fin.ne_of_val_ne (by rw [hV0]; change free ≠ free + 4; omega)
  have hV0ne' : srnV free hkV 0 ≠ ⟨free + 5, hf5⟩ :=
    Fin.ne_of_val_ne (by rw [hV0]; change free ≠ free + 5; omega)
  -- the components
  have hpop := TransformsIn.congr (Transforms.toIn_of (fun n ↦ pop_transforms
    (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ hRF (bound M n)) (fun _ _ ↦ True)
    (fun input σ hB _ ↦ (hB.update (by
        cases h : σ ⟨free + 5, hf5⟩
        · exact Nat.zero_le _
        · change 1 ≤ bound M input.length
          unfold bound
          omega)).update (by
        rw [List.length_tail]
        exact (Nat.sub_le _ _).trans (hB _))))
    (fun _ _ _ ↦ rfl : ∀ input σ, _ → _ = popF (⟨free + 5, hf5⟩ : Fin k)
      ⟨free + 4, hf4⟩ input σ)
  obtain ⟨hmidT, hmidfr, hmidout⟩ :=
    srnMiddle_contract free hk params hparams M steps stepRep T G hG
  have hpush : ∀ c : Bool, TransformsIn (push c (srnV free hkV 0)) (fun input σ ↦
      (σ (srnV free hkV 0)).length < M) (pushF c (srnV free hkV 0)) (fun n ↦ 2 * bound M n + 6)
      (bound M) :=
    fun c ↦ TransformsIn.congr (Transforms.toIn_of (fun n ↦ push_transforms c (srnV free hkV 0)
      (bound M n)) _ (fun input σ hB hl ↦ hB.update (by
        rw [List.length_cons]
        exact le_bound_of_le hl))) (fun _ _ _ ↦ rfl)
  have hcase := TransformsIn.congr (TransformsIn.caseReg (⟨free + 4, hf4⟩ : Fin k)
    (hpush false) (hpush true))
    (fun _ _ _ ↦ rfl : ∀ input σ, _ → _ = caseF (⟨free + 4, hf4⟩ : Fin k)
      (pushF false (srnV free hkV 0)) (pushF true (srnV free hkV 0)) input σ)
  have h := hpop.seq (hmidT.seq hcase)
  -- the valuations along the body
  have hfr1 : ∀ (input : List Bool) (σ : Fin k → List Bool) (t : Fin k),
      t ≠ ⟨free + 4, hf4⟩ → t ≠ ⟨free + 5, hf5⟩ →
      popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ t = σ t := by
    intro input σ t h4 h5
    unfold popF
    rw [Function.update_of_ne h5, Function.update_of_ne h4]
  have henv1 : ∀ input σ, EnvWF M input σ (srnEnv free hk2 params) →
      EnvWF M input (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ)
        (srnEnv free hk2 params) :=
    fun input σ hσ ↦ envWF_of_frame hσ fun s t ↦ hfr1 input σ _ (henvF s t) (henvR s t)
  -- the flag after the middle is the flag after the pop
  have hflag : ∀ input σ, middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G
      input (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) ⟨free + 4, hf4⟩ =
      (σ ⟨free + 5, hf5⟩).head?.toList := fun input σ ↦ by
    rw [hmidfr input _ _ (by change free + 4 < _; omega)]
    unfold popF
    rw [Function.update_of_ne hRF.symm, Function.update_self]
  -- the body's transformer, on a valuation whose reversed word is nonempty
  have hpushF : ∀ input σ (c : Bool) (r : List Bool), σ ⟨free + 5, hf5⟩ = c :: r →
      body2F (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩ (srnVals b free hk2)
        (srnScr b free hk4) G input σ =
      Function.update (middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
        (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ)) (srnV free hkV 0)
        (c :: middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
          (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) (srnV free hkV 0)) := by
    intro input σ c r hcr
    unfold body2F caseF pushF
    rw [hflag, hcr, List.head?_cons, Option.toList_some, List.getLast?_singleton]
    cases c
    · rw [ite_eq_right (by decide)]
    · rw [ite_eq_left rfl]
  -- the body's transformer changes nothing but the cursor's word below the value registers
  have hfrb : ∀ input σ (t : Fin k), t.val < free + 6 → t ≠ srnV free hkV 0 →
      body2F (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩ (srnVals b free hk2)
        (srnScr b free hk4) G input σ t =
      popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ t := by
    intro input σ t ht hne
    unfold body2F caseF pushF
    by_cases hc : (middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
        (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) ⟨free + 4, hf4⟩).getLast? =
        some true
    · rw [ite_eq_left hc, Function.update_of_ne hne, hmidfr input _ t ht]
    · rw [ite_eq_right hc, Function.update_of_ne hne, hmidfr input _ t ht]
  have hm : (srnBody2 (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩ (srnVals b free hk2)
      (srnScr b free hk4) (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm =
      Geb.SizeBounded.Machine.seq (pop (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩)
        (Geb.SizeBounded.Machine.seq (srnMiddle ⟨free + 4, hf4⟩ (srnVals b free hk2)
          (srnScr b free hk4) (Prog.seqFin b (steps false)) (Prog.seqFin b (steps true))).tm
          (caseProbe (some ⟨free + 4, hf4⟩) (push false (srnV free hkV 0))
            (push true (srnV free hkV 0)))) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    refine TransformsIn.mono_time (TransformsIn.mono_pre (TransformsIn.congr h
      fun input σ _ ↦ (rfl : _ = body2F (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩
        (srnVals b free hk2) (srnScr b free hk4) G input σ)) ?_) ?_
    · intro input σ _ ⟨hl, hσ⟩
      refine ⟨trivial, henv1 input σ hσ, ?_⟩
      have hV : middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
          (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) (srnV free hkV 0) =
          σ (srnV free hkV 0) := by
        rw [hmidfr input _ _ (by rw [hV0]; omega), hfr1 input σ _ hV0ne hV0ne']
      by_cases hc : (middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
          (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) ⟨free + 4, hf4⟩).getLast? =
          some true
      · rw [ite_eq_left hc, hV]
        exact hl
      · rw [ite_eq_right hc, hV]
        exact hl
    · intro n
      unfold body2Time
      rw [Nat.max_self, Nat.max_self]
      omega
  · intro input σ t ht
    rw [hfrb input σ t (by omega) (Fin.ne_of_val_ne (by rw [hV0]; omega)),
      hfr1 input σ t (Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 4; omega))
        (Fin.ne_of_val_ne (by change (t : ℕ) ≠ free + 5; omega))]
  · intro input σ
    rw [hfrb input σ _ (by rw [hV1]; omega) (Fin.ne_of_val_ne (by rw [hV0, hV1]; omega)),
      hfr1 input σ _ (Fin.ne_of_val_ne (by rw [hV1]; change free + 1 ≠ free + 4; omega))
        (Fin.ne_of_val_ne (by rw [hV1]; change free + 1 ≠ free + 5; omega))]
  · intro input σ c r hcr
    rw [hpushF input σ c r hcr, Function.update_of_ne hV0ne'.symm, Function.update_self,
      hmidfr input _ _ (by change free + 5 < _; omega), hmidfr input _ _ (by rw [hV0]; omega),
      hfr1 input σ _ hV0ne hV0ne']
    unfold popF
    rw [Function.update_self, hcr, List.tail_cons]
    exact ⟨rfl, rfl⟩
  · intro input σ c r hcr hσ l
    have hF : popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ ⟨free + 4, hf4⟩ = [c] := by
      unfold popF
      rw [Function.update_of_ne hRF.symm, Function.update_self, hcr, List.head?_cons,
        Option.toList_some]
    obtain ⟨hout, hwf⟩ := hmidout input _ c hF (henv1 input σ hσ) l
    have hvt : ∀ t, body2F (srnV free hkV) ⟨free + 5, hf5⟩ ⟨free + 4, hf4⟩ (srnVals b free hk2)
        (srnScr b free hk4) G input σ (srnVals b free hk2 l t) =
        middleF ⟨free + 4, hf4⟩ (srnVals b free hk2) (srnScr b free hk4) G input
          (popF (⟨free + 5, hf5⟩ : Fin k) ⟨free + 4, hf4⟩ input σ) (srnVals b free hk2 l t) :=
      fun t ↦ by
        rw [hpushF input σ c r hcr,
          Function.update_of_ne (Fin.ne_of_val_ne (by rw [hvals, hV0]; omega))]
    have hread : ∀ τ (r : Reg k), readRep τ r = ⟨τ (r 0), counterValue (τ (r 1))⟩ := fun _ _ ↦ rfl
    refine ⟨?_, ?_⟩
    · rw [hread, hvt 0, hvt 1, ← hread, hout]
      refine congrArg _ (funext fun s ↦ ?_)
      rw [hread, hread, hfr1 input σ _ (henvF s 0) (henvR s 0),
        hfr1 input σ _ (henvF s 1) (henvR s 1)]
    · obtain ⟨hw, l', hl', hc⟩ := hwf
      refine ⟨?_, l', hl', ?_⟩
      · rw [hvt 0]
        exact hw
      · rw [hvt 1]
        exact hc

end

end Geb.SizeBounded.Logspace.Machine
