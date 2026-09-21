/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Repeat

set_option doc.verso true in
/-!
# Word constructors on generated arguments

Constructor programs invoke their argument generators as subroutines. Generated
arguments are read by recomputation, and their output is never stored on a work tape.
Each argument generator restores its initialized valuation, so the same tapes can
be reused across calls and shared by several argument programs.

## Main definitions

* {lit}`lengthGenerator` emits the numerical length of its generated argument.
* {lit}`productGenerator` counts its second argument and repeats its first argument.
* {lit}`emitNumberClean` emits a binary counter in shortlex form, then clears it.
* {lit}`condGenerator` selects a branch by the length of its generated selector.

## Main statements

* {lit}`lengthGenerator_emitsIn` proves numerical length with one extra tape.
* {lit}`succGenerator_emitsIn` prefixes a fixed digit to a generated argument.
* {lit}`productGenerator_emitsIn` proves the string-product constructor for arbitrary
  argument generators, with one extra binary counter and preserved caller registers.
* {lit}`condGenerator_emitsIn` preserves the selected branch's contract and clears the test tape.

## Implementation notes

The counter is initialized by the length reader and consumed by the repetition loop.
The argument programs have fixed finite control and share the same physical input.
The contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, composition, word reader, string product
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Emit a shortlex number, then park and clear its binary counter. -/
@[expose] def emitNumberClean {k : ℕ} (C : Fin k) :=
  seq (seq (emitNumber C) (returnTape C)) (const [] C)

/-- A binary counter can be emitted as a numerical word with all heads parked on return. -/
theorem emitNumberClean_emitsIn {k : ℕ} (C : Fin k) (B : ℕ → ℕ) :
    EmitsIn (emitNumberClean C)
      (fun input σ ↦ ∃ n, σ C = counterWord n ∧ (n + 1).size ≤ B input.length)
      (fun _ σ ↦ Function.update σ C [])
      (fun _ σ ↦ unrank (counterValue (σ C)))
      (fun n ↦ (4 * B n + 7) + (4 * B n + 9)) B := by
  have hp : EmitsIn (seq (emitNumber C) (returnTape C))
      (fun input σ ↦ ∃ n, σ C = counterWord n ∧ (n + 1).size ≤ B input.length)
      (fun _ σ ↦ Function.update σ C (counterWord (counterValue (σ C) + 1)))
      (fun _ σ ↦ unrank (counterValue (σ C))) (fun n ↦ 4 * B n + 7) B := by
    intro input cfg σ hq hpark hpos hσ hpre hB
    obtain ⟨n, hn, hnB⟩ := hpre
    have hheads (i : Fin k) :
        -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
      rw [hpark i]
      constructor <;> omega
    obtain ⟨t, ht, he⟩ := emitNumber_emits C { cfg with state := some (emitNumber C).q₀ }
      rfl n (B input.length) ((hσ C).trans (congrArg tapeOf hn)) (hpark C) hnB hheads
    have hr := returnTape_runsTo C
      { cfg with state := some (returnTape C).q₀
                 workTapes := Function.update cfg.workTapes C (tapeOf (counterWord (n + 1)))
                 workTapePos := Function.update cfg.workTapePos C ((n + 1).size : ℤ)
                 output := cfg.output ++ unrank n }
      rfl (counterWord (n + 1)) (Function.update_self ..) ((n + 1).size : ℤ)
      (Function.update_self ..) (by omega) (by rw [length_counterWord]) (B input.length)
      (update_workTapePos_bounds C hheads _ (by omega) (by omega))
    have h := he.seqEmits hr.toEmits
    rw [← liftL_start (emitNumber C) (returnTape C) cfg hq, List.append_nil] at h
    have hreturn : Function.update cfg.workTapePos C 0 = cfg.workTapePos := by
      rw [← hpark C, Function.update_eq_self]
    dsimp only
    rw [hn, counterValue_counterWord]
    refine ⟨hB.update (by rw [length_counterWord]; exact hnB),
      t + (((n + 1).size : ℤ) + 2).toNat, by omega, h.congr_target ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      change Function.update cfg.workTapes C (tapeOf (counterWord (n + 1))) i = _
      by_cases hi : i = C
      · subst i
        simp
      · simp only [Function.update_of_ne hi, after, hσ i]
    · simp only [liftR, Function.update_idem, hreturn, after]
    · rfl
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] C (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  simpa only [emitNumberClean, Function.update_idem] using
    (hp.seqTransformsIn hc).mono_pre (fun _ _ _ h ↦ ⟨h, trivial⟩)

/-- Numerical length of a generated word, returning the additional counter tape blank. -/
@[expose] def lengthGenerator {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  seq (generatedLength P) (emitNumberClean 0)

/-- Numerical length substitutes any generator without storing its output.
The generator's exact final valuation is retained on its original tapes. -/
theorem lengthGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B)
    (hsize : ∀ input σ, Pre input σ → Bounded σ (B input.length) →
      ((W input σ).length + 1).size ≤ B input.length) :
    EmitsIn (lengthGenerator P) (fun input σ ↦ Pre input (fun i ↦ σ i.succ))
      (fun input σ ↦ Fin.cons [] (F input (fun i ↦ σ i.succ)))
      (fun input σ ↦ unrank (W input (fun i ↦ σ i.succ)).length)
      (fun n ↦ (4 * B n + 9 + T n * (2 * B n + 5)) +
        ((4 * B n + 7) + (4 * B n + 9))) B := by
  have h := ((generatedLength_transformsIn hP hsize).seqEmitsIn
    (emitNumberClean_emitsIn 0 B)).mono_pre
      (Pre' := fun input σ ↦ Pre input (fun i ↦ σ i.succ)) (by
        intro input σ hB hp
        exact ⟨hp, (W input (fun i ↦ σ i.succ)).length, rfl,
          hsize input (fun i ↦ σ i.succ) hp (fun i ↦ hB i.succ)⟩)
  have hf (input : List Bool) (σ : Fin (k + 1) → List Bool) :
      Function.update (Fin.cons (counterWord (W input (fun i ↦ σ i.succ)).length)
        (F input (fun i ↦ σ i.succ))) 0 [] =
        (Fin.cons [] (F input (fun i ↦ σ i.succ)) : Fin (k + 1) → List Bool) := by
    funext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i
  simpa only [lengthGenerator, Fin.cons_zero, counterValue_counterWord, hf] using h

/-- Emit an optional fixed digit in one step, leaving every tape and head unchanged. -/
@[expose] def emitSymbol {k : ℕ} (b : Option Bool) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := b, state := none }

/-- A fixed optional digit has an emitter contract with no scratch registers. -/
theorem emitSymbol_emitsIn {k : ℕ} (b : Option Bool) (B : ℕ → ℕ) :
    EmitsIn (emitSymbol (k := k) b) (fun _ _ ↦ True) (fun _ σ ↦ σ)
      (fun _ _ ↦ b.toList) (fun _ ↦ 1) B := by
  intro input cfg σ hq hpark _ hσ _ hB
  have hs : (emitSymbol b).step cfg =
      { cfg with state := none, output := cfg.output ++ b.toList } := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      exact add_zero _
    · rfl
  refine ⟨hB, 1, le_rfl, ⟨⟨?_, ?_, ?_⟩, ?_, rfl⟩⟩
  · intro s hs'
    have : s = 0 := by omega
    simpa only [this, runFrom_zero, hq] using Option.some_ne_none ()
  · rw [runFrom_succ_eq_step', runFrom_zero, hs]
    apply Cfg.ext <;> try rfl
    exact funext hσ
  · intro s hs' i
    have hp : -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
      rw [hpark i]
      constructor <;> omega
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · exact hp
    · simpa only [runFrom_succ_eq_step', runFrom_zero, hs] using hp
  · simp [outputString_succ, outputSymbol, hq, emitSymbol]
    rfl

/-- String successor emits its fixed first digit before running the argument generator. -/
theorem succGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) (b : Bool) :
    EmitsIn (seq (emitSymbol (some b)) P) Pre F
      (fun input σ ↦ b :: W input σ) (fun n ↦ 1 + T n) B := by
  simpa only [Option.toList_some, List.singleton_append] using
    ((emitSymbol_emitsIn (some b) B).seqEmitsIn hP).mono_pre
      (fun _ _ _ h ↦ ⟨trivial, h⟩)

/-- String product of two generated words, using one additional repetition counter. -/
@[expose] def productGenerator {k : ℕ} {S₁ S₂ : Type}
    (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂) :=
  seq (generatedLength Q) (repeatGenerator (onTapes P (reserveTape k)) 0)

/-- String product substitutes arbitrary restoring generators into both argument slots.
The second word need only have a bounded binary length; the first is regenerated. -/
theorem productGenerator_emitsIn {k : ℕ} {S₁ S₂ : Type}
    {P : MultiTapeTM k Bool S₁} {Q : MultiTapeTM k Bool S₂}
    {Pre₁ Pre₂ : List Bool → (Fin k → List Bool) → Prop}
    {W V : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B N : ℕ → ℕ}
    (hP : EmitsIn P Pre₁ (fun _ σ ↦ σ) W T₁ B)
    (hQ : EmitsIn Q Pre₂ (fun _ σ ↦ σ) V T₂ B)
    (hlen : ∀ input σ, Pre₂ input σ → (V input σ).length ≤ N input.length)
    (hsize : ∀ input σ, Pre₂ input σ → Bounded σ (B input.length) →
      ((V input σ).length + 1).size ≤ B input.length) :
    EmitsIn (productGenerator P Q)
      (fun input σ ↦ Pre₁ input (fun i ↦ σ i.succ) ∧ Pre₂ input (fun i ↦ σ i.succ))
      (fun _ σ ↦ Function.update σ 0 [])
      (fun input σ ↦ (List.replicate (V input (fun i ↦ σ i.succ)).length
        (W input (fun i ↦ σ i.succ))).flatten)
      (fun n ↦ (4 * B n + 9 + T₂ n * (2 * B n + 5)) +
        (N n * (T₁ n + 2 * B n + 7) + 1)) B := by
  have hp : EmitsIn (onTapes P (reserveTape k))
      (fun input σ ↦ Pre₁ input (fun i ↦ σ i.succ)) (fun _ σ ↦ σ)
      (fun input σ ↦ W input (fun i ↦ σ i.succ)) T₁ B := by
    simpa only [reserveTape_symm_inl] using
      (hP.onTapes (reserveTape k)).congr (F' := fun _ σ ↦ σ)
        (fun _ σ _ ↦ onTapesVal_self _ σ)
  have hr := repeatGenerator_emitsIn hp (0 : Fin (k + 1)) N
    (fun input σ n h ↦ by simpa using h)
    (fun input σ n ↦ by simp)
  have hl := generatedLength_readsLength hQ hsize
  have hs := (hl.seqEmitsIn hr).mono_pre (Pre' := fun input σ ↦
      Pre₁ input (fun i ↦ σ i.succ) ∧ Pre₂ input (fun i ↦ σ i.succ)) (by
    intro input σ _ h
    refine ⟨h.2, ?_, (V input (fun i ↦ σ i.succ)).length, Function.update_self .., ?_⟩
    · simpa using h.1
    · simpa using hlen input (fun i ↦ σ i.succ) h.2)
  simpa only [productGenerator, Function.update_self, counterValue_counterWord,
    Function.update_idem, Function.update_of_ne (Fin.succ_ne_zero _)] using hs

/-- Select one of two programs by a test of the symbol under a work head.
The Boolean tag is retained in finite control throughout the chosen subcall. -/
@[expose] def chooseSymbol {k : ℕ} {S : Bool → Type} (R : Fin k) (test : Option Bool → Bool)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) :
    MultiTapeTM k Bool (Option ((b : Bool) × S b)) where
  q₀ := none
  tr q input work := match q with
    | none =>
      let b := test (work R)
      { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none,
        state := some (some ⟨b, (P b).q₀⟩) }
    | some ⟨b, q⟩ =>
      let a := (P b).tr q input work
      { a with state := a.state.map (fun q ↦ some ⟨b, q⟩) }

/-- Embed a branch's configuration in the conditional's finite control. -/
@[expose] def chooseCfg {k : ℕ} {S : Bool → Type} {input : List Bool} (b : Bool)
    (cfg : Cfg k Bool (S b) input) : Cfg k Bool (Option ((b : Bool) × S b)) input :=
  { cfg with state := cfg.state.map (fun q ↦ some ⟨b, q⟩) }

/-- The chosen branch is simulated exactly, including its halting transition. -/
theorem chooseSymbol_step {k : ℕ} {S : Bool → Type} {input : List Bool}
    (R : Fin k) (test : Option Bool → Bool)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) (b : Bool) (cfg : Cfg k Bool (S b) input) :
    (chooseSymbol R test P).step (chooseCfg b cfg) = chooseCfg b ((P b).step cfg) := by
  cases hq : cfg.state with
  | none => simp [chooseCfg, step_of_halt, hq]
  | some q => unfold step chooseCfg; simp only [hq]; rfl

/-- Every time in the chosen branch corresponds to the same time in the conditional. -/
theorem chooseSymbol_runFrom {k : ℕ} {S : Bool → Type} {input : List Bool}
    (R : Fin k) (test : Option Bool → Bool)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) (b : Bool) (cfg : Cfg k Bool (S b) input)
    (t : ℕ) :
    (chooseSymbol R test P).runFrom (chooseCfg b cfg) t = chooseCfg b ((P b).runFrom cfg t) := by
  revert t
  refine Nat.rec ?_ ?_
  · rfl
  · intro t ih
    rw [runFrom_succ_eq_step', ih, chooseSymbol_step, runFrom_succ_eq_step']

/-- A conditional emits exactly the chosen branch's output. -/
theorem chooseSymbol_outputString {k : ℕ} {S : Bool → Type} {input : List Bool}
    (R : Fin k) (test : Option Bool → Bool)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) (b : Bool) (cfg : Cfg k Bool (S b) input)
    (t : ℕ) :
    (chooseSymbol R test P).outputString (chooseCfg b cfg) t = (P b).outputString cfg t := by
  have ho (c : Cfg k Bool (S b) input) :
      (chooseSymbol R test P).outputSymbol (chooseCfg b c) = (P b).outputSymbol c := by
    unfold outputSymbol chooseCfg
    cases c.state <;> rfl
  revert t
  refine Nat.rec ?_ ?_
  · rfl
  · intro t ih
    rw [outputString_succ, outputString_succ, ih, chooseSymbol_runFrom, ho]

/-- A work-symbol test costs one step and preserves the chosen branch's resource contract. -/
theorem chooseSymbol_emitsIn {k : ℕ} {S : Bool → Type} (R : Fin k) (test : Option Bool → Bool)
    {P : (b : Bool) → MultiTapeTM k Bool (S b)}
    {Pre : Bool → List Bool → (Fin k → List Bool) → Prop}
    {F : Bool → List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : Bool → List Bool → (Fin k → List Bool) → List Bool} {T : Bool → ℕ → ℕ} {B : ℕ → ℕ}
    (hP : ∀ b, EmitsIn (P b) (Pre b) (F b) (W b) (T b) B) :
    EmitsIn (chooseSymbol R test P) (fun input σ ↦ Pre (test (tapeOf (σ R) 0)) input σ)
      (fun input σ ↦ F (test (tapeOf (σ R) 0)) input σ)
      (fun input σ ↦ W (test (tapeOf (σ R) 0)) input σ)
      (fun n ↦ 1 + max (T false n) (T true n)) B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  let b := (test (tapeOf (σ R) 0))
  let start := { cfg with state := some (P b).q₀ }
  obtain ⟨hFB, t, ht, he⟩ := hP b input start σ rfl hpark hpos hσ hp hB
  have hbit : test (cfg.workTapeSymbols R) = b := by
    change test (cfg.workTapes R (cfg.workTapePos R)) = b
    rw [hpark R, hσ R]
  have hstep : (chooseSymbol R test P).step cfg = chooseCfg b start := by
    rw [step_of_state _ _ none hq]
    simp only [chooseSymbol, moveInputPos_zero, Option.toList_none, List.append_nil]
    apply Cfg.ext
    · change some (some (⟨test (cfg.workTapeSymbols R),
          (P (test (cfg.workTapeSymbols R))).q₀⟩ : Sigma S)) =
        some (some (⟨b, (P b).q₀⟩ : Sigma S))
      rw [hbit]
    · rfl
    · rfl
    · funext i
      simp [chooseCfg, start]
    · rfl
  have hrun (s : ℕ) : (chooseSymbol R test P).runFrom cfg (s + 1) =
      chooseCfg b ((P b).runFrom start s) := by
    rw [Nat.add_comm s 1, runFrom_add]
    change (chooseSymbol R test P).runFrom ((chooseSymbol R test P).step cfg) s = _
    rw [hstep, chooseSymbol_runFrom]
  refine ⟨hFB, t + 1, ?_, ?_⟩
  · have hm : T b input.length ≤ max (T false input.length) (T true input.length) := by
      cases b
      · exact le_max_left ..
      · exact le_max_right ..
    dsimp only
    omega
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, rfl⟩
    · intro s hs
      cases s with
      | zero => simp [runFrom_zero, hq]
      | succ s =>
        rw [hrun]
        simpa [chooseCfg] using he.live s (by omega)
    · rw [hrun, he.runFrom_eq]
      rfl
    · intro s hs i
      cases s with
      | zero => rw [runFrom_zero, hpark i]; constructor <;> omega
      | succ s => rw [hrun]; exact he.pos s (by omega) i
    · rw [Nat.add_comm t 1, outputString_add_eq_append]
      have ho : (chooseSymbol R test P).outputString cfg 1 = [] := by
        rw [outputString_succ]
        simp only [runFrom_zero, outputSymbol, hq]
        rfl
      rw [ho, List.nil_append]
      change (chooseSymbol R test P).outputString ((chooseSymbol R test P).step cfg) t = _
      rw [hstep, chooseSymbol_outputString, he.output]

/-- Select a branch according to whether a parked register is empty. -/
@[expose] def chooseEmpty {k : ℕ} {S : Bool → Type} (R : Fin k)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) :=
  chooseSymbol R Option.isNone P

/-- An empty-register test preserves the selected branch's emitting contract. -/
theorem chooseEmpty_emitsIn {k : ℕ} {S : Bool → Type} (R : Fin k)
    {P : (b : Bool) → MultiTapeTM k Bool (S b)}
    {Pre : Bool → List Bool → (Fin k → List Bool) → Prop}
    {F : Bool → List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : Bool → List Bool → (Fin k → List Bool) → List Bool} {T : Bool → ℕ → ℕ} {B : ℕ → ℕ}
    (hP : ∀ b, EmitsIn (P b) (Pre b) (F b) (W b) (T b) B) :
    EmitsIn (chooseEmpty R P) (fun input σ ↦ Pre (σ R).isEmpty input σ)
      (fun input σ ↦ F (σ R).isEmpty input σ) (fun input σ ↦ W (σ R).isEmpty input σ)
      (fun n ↦ 1 + max (T false n) (T true n)) B := by
  have he (w : List Bool) : (tapeOf w 0).isNone = w.isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp [tapeOf_zero_eq_none_iff]
  simpa only [chooseEmpty, he] using chooseSymbol_emitsIn R Option.isNone hP

/-- A length counter is empty precisely when the represented word is empty. -/
@[simp] theorem counterWord_length_isEmpty (w : List Bool) :
    (counterWord w.length).isEmpty = w.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  simp [counterWord_eq_nil_iff]

/-- Test a generated word's emptiness, call the selected generator, and clear the length tape. -/
@[expose] def condGenerator {k : ℕ} {S : Bool → Type} {A : Type}
    (Q : MultiTapeTM k Bool A) (P : (b : Bool) → MultiTapeTM k Bool (S b)) :=
  seq (generatedLength Q)
    (seq (chooseEmpty 0 (fun b ↦ onTapes (P b) (reserveTape k))) (const [] 0))

/-- A conditional has finite control when its selector and both branches do. -/
theorem condGenerator_finite {k : ℕ} {S : Bool → Type} {A : Type}
    [Finite A] [∀ b, Finite (S b)] (Q : MultiTapeTM k Bool A)
    (P : (b : Bool) → MultiTapeTM k Bool (S b)) :
    Finite (StateOf (condGenerator Q P)) := by
  let := Fintype.ofFinite A
  let (b : Bool) : Fintype (S b) := Fintype.ofFinite (S b)
  unfold condGenerator generatedLength chooseEmpty chooseSymbol
  infer_instance

/-- Conditional composition preserves the old registers and clears its one extra tape.
Only the precondition of the branch selected by the generated test word is required. -/
theorem condGenerator_emitsIn {k : ℕ} {S : Bool → Type} {A : Type}
    {Q : MultiTapeTM k Bool A} {P : (b : Bool) → MultiTapeTM k Bool (S b)}
    {PreQ : List Bool → (Fin k → List Bool) → Prop}
    {PreP : Bool → List Bool → (Fin k → List Bool) → Prop}
    {V : List Bool → (Fin k → List Bool) → List Bool}
    {W : Bool → List Bool → (Fin k → List Bool) → List Bool}
    {TQ B : ℕ → ℕ} {TP : Bool → ℕ → ℕ}
    (hQ : EmitsIn Q PreQ (fun _ σ ↦ σ) V TQ B)
    (hP : ∀ b, EmitsIn (P b) (PreP b) (fun _ σ ↦ σ) (W b) (TP b) B)
    (hsize : ∀ input σ, PreQ input σ → Bounded σ (B input.length) →
      ((V input σ).length + 1).size ≤ B input.length) :
    EmitsIn (condGenerator Q P)
      (fun input σ ↦ PreQ input (fun i ↦ σ i.succ) ∧
        PreP (V input (fun i ↦ σ i.succ)).isEmpty input (fun i ↦ σ i.succ))
      (fun _ σ ↦ Function.update σ 0 [])
      (fun input σ ↦ W (V input (fun i ↦ σ i.succ)).isEmpty input (fun i ↦ σ i.succ))
      (fun n ↦ (4 * B n + 9 + TQ n * (2 * B n + 5)) +
        ((1 + max (TP false n) (TP true n)) + (4 * B n + 9))) B := by
  have ha (b : Bool) : EmitsIn (onTapes (P b) (reserveTape k))
      (fun input σ ↦ PreP b input (fun i ↦ σ i.succ)) (fun _ σ ↦ σ)
      (fun input σ ↦ W b input (fun i ↦ σ i.succ)) (TP b) B := by
    exact ((hP b).onTapes (reserveTape k)).congr
      (fun _ σ _ ↦ onTapesVal_self (reserveTape k) σ)
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (0 : Fin (k + 1)) (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
  have hs := ((generatedLength_transformsIn hQ hsize).seqEmitsIn
    ((chooseEmpty_emitsIn 0 ha).seqTransformsIn hc)).mono_pre
      (Pre' := fun input σ ↦ PreQ input (fun i ↦ σ i.succ) ∧
        PreP (V input (fun i ↦ σ i.succ)).isEmpty input (fun i ↦ σ i.succ)) (by
        intro input σ _ hp
        exact ⟨hp.1, by simpa only [Fin.cons_zero, Fin.cons_succ,
          counterWord_length_isEmpty] using hp.2, trivial⟩)
  have hf := hs.congr (F' := fun _ σ ↦ Function.update σ 0 []) (by
    intro input σ _
    funext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i)
  simpa only [condGenerator, Fin.cons_zero, Fin.cons_succ,
    counterWord_length_isEmpty] using hf

end

end Geb.Oitavem.Machine
