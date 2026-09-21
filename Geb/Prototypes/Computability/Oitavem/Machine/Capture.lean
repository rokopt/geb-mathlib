/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Generated
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.CopyRev

set_option doc.verso true in
/-!
# Capturing a bounded output prefix

A mask tape limits the output retained from a generator. Its bits are irrelevant:
each nonblank cell permits one output digit. The wrapper advances the mask and
capture heads together, then stops writing when the mask is exhausted. It continues
the underlying computation to its own halt, preserving the generator's final tapes.

## Main definitions

* {lit}`captureOutput` silently retains a prefix on an additional tape.
* {lit}`captureOutputCfg` describes the wrapper's configurations.
* {lit}`generatedPrefix` replaces a saved register after capturing the next value.

## Main statements

* {lit}`captureOutput_runsTo` preserves termination and bounds the retained prefix
  by the mask length, including a digit emitted on the generator's halting transition.
* {lit}`generatedPrefix_transformsIn` initializes and clears capture scratch,
  preserves the mask, and returns every work head parked.

## Implementation notes

Digits are written in emission order at increasing tape positions. The captured
register therefore represents the reverse of the prefix. Both extra heads stop
at the captured length. The run contracts inherit CSLib's
{lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, output prefix, bounded storage
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Retain emitted digits while the mask is nonblank, without emitting externally. -/
@[expose] def captureOutput {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :
    MultiTapeTM (k + 2) Bool S where
  q₀ := P.q₀
  tr q input work :=
    let a := P.tr q input (fun i ↦ work (oldTape i))
    let keep := a.output.isSome && (work countTape).isSome
    { inputTape := a.inputTape
      workTapes := tapeCase (none, if keep then 1 else 0)
        (if keep then (some a.output, 1) else (none, 0)) a.workTapes
      output := none
      state := a.state }

/-- The simulated configuration with a mask and the reverse captured prefix. -/
@[expose] def captureOutputCfg {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (mask w out : List Bool) : Cfg (k + 2) Bool S input where
  state := cfg.state
  inputPos := cfg.inputPos
  workTapes := tapeCase (tapeOf mask) (tapeOf (w.take mask.length).reverse) cfg.workTapes
  workTapePos := tapeCase ((w.take mask.length).length : ℤ)
    ((w.take mask.length).length : ℤ) cfg.workTapePos
  output := out

/-- A cell of a register inside its word is nonblank. -/
theorem tapeOf_isSome_of_lt (v : List Bool) (n : ℕ) (h : n < v.length) :
    (tapeOf v (n : ℤ)).isSome = true := by
  rw [tapeOf_of_lt v (n : ℤ) (by omega) (by exact_mod_cast h)]
  rfl

/-- A cell of a register beyond its word is blank. -/
theorem tapeOf_isSome_of_le (v : List Bool) (n : ℕ) (h : v.length ≤ n) :
    (tapeOf v (n : ℤ)).isSome = false := by
  rw [tapeOf_of_le v (n : ℤ) (by exact_mod_cast h)]
  rfl

/-- The state of a wrapped configuration is the generator's. -/
@[simp] theorem captureOutputCfg_state {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (mask w out : List Bool) :
    (captureOutputCfg cfg mask w out).state = cfg.state := rfl

/-- A wrapped configuration depends on the emitted word only through the prefix it retains. -/
theorem captureOutputCfg_congr {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (mask w w' out : List Bool)
    (hw : w.take mask.length = w'.take mask.length) :
    captureOutputCfg cfg mask w out = captureOutputCfg cfg mask w' out := by
  unfold captureOutputCfg
  rw [hw]

/-- The wrapper's action at a simulated step. -/
theorem captureOutput_tr {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (q : S) (mask w out : List Bool) :
    (captureOutput P).tr q (captureOutputCfg cfg mask w out).inputSymbol
        (captureOutputCfg cfg mask w out).workTapeSymbols =
      { inputTape := (P.tr q cfg.inputSymbol cfg.workTapeSymbols).inputTape
        workTapes := tapeCase
          (none, if (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output.isSome &&
            (tapeOf mask ((w.take mask.length).length : ℤ)).isSome then 1 else 0)
          (if (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output.isSome &&
            (tapeOf mask ((w.take mask.length).length : ℤ)).isSome then
              (some (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output, 1) else (none, 0))
          (P.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes
        output := none
        state := (P.tr q cfg.inputSymbol cfg.workTapeSymbols).state } := rfl

/-- A step at which nothing is retained: the generator steps on its own tapes, both extra
tapes and both extra heads stay as they are, and nothing is emitted. -/
theorem step_captureOutputCfg_of_not_keep {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (q : S) (hq : cfg.state = some q)
    (mask w out : List Bool)
    (hkeep : ((P.tr q cfg.inputSymbol cfg.workTapeSymbols).output.isSome &&
      (tapeOf mask ((w.take mask.length).length : ℤ)).isSome) = false) :
    (captureOutput P).step (captureOutputCfg cfg mask w out) =
      captureOutputCfg (P.step cfg) mask w out := by
  have hstate : (captureOutputCfg cfg mask w out).state = some q := hq
  rw [step_of_state (captureOutput P) _ q hstate, captureOutput_tr, hkeep,
    step_of_state P cfg q hq]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩ <;> rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
    · exact add_zero _
    · exact add_zero _
    · rfl
  · exact List.append_nil out

/-- A step at which a digit is retained: the generator steps on its own tapes, the digit is
written at the capture head, both extra heads advance, and nothing is emitted. -/
theorem step_captureOutputCfg_of_keep {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (q : S) (hq : cfg.state = some q)
    (mask w out : List Bool) (b : Bool)
    (hb : (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output = some b)
    (hlt : w.length < mask.length) :
    (captureOutput P).step (captureOutputCfg cfg mask w out) =
      captureOutputCfg (P.step cfg) mask (w ++ [b]) out := by
  have hstate : (captureOutputCfg cfg mask w out).state = some q := hq
  have htake : w.take mask.length = w := List.take_of_length_le (by omega)
  have htake' : (w ++ [b]).take mask.length = w ++ [b] := by
    refine List.take_of_length_le ?_
    rw [List.length_append, List.length_singleton]
    omega
  have hkeep : ((P.tr q cfg.inputSymbol cfg.workTapeSymbols).output.isSome &&
      (tapeOf mask ((w.take mask.length).length : ℤ)).isSome) = true := by
    rw [hb, htake]
    exact tapeOf_isSome_of_lt mask w.length hlt
  rw [step_of_state (captureOutput P) _ q hstate, captureOutput_tr, hkeep,
    step_of_state P cfg q hq]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
    · rfl
    · change Function.update (tapeOf (w.take mask.length).reverse)
        ((w.take mask.length).length : ℤ)
        (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output =
        tapeOf ((w ++ [b]).take mask.length).reverse
      rw [hb, htake, htake', List.reverse_append, List.reverse_singleton,
        List.singleton_append, tapeOf_cons, List.length_reverse]
    · rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
    · change ((w.take mask.length).length : ℤ) + 1 =
        (((w ++ [b]).take mask.length).length : ℤ)
      rw [htake, htake', List.length_append, List.length_singleton]
      omega
    · change ((w.take mask.length).length : ℤ) + 1 =
        (((w ++ [b]).take mask.length).length : ℤ)
      rw [htake, htake', List.length_append, List.length_singleton]
      omega
    · rfl
  · exact List.append_nil out

/-- Every generator transition is simulated in one step: the digit it emits is appended to the
emitted word, only the prefix of the mask's length is retained, the generator's own tapes and
heads are preserved, and the wrapper emits nothing. -/
theorem step_captureOutputCfg {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (q : S) (hq : cfg.state = some q) (mask w out : List Bool) :
    (captureOutput P).step (captureOutputCfg cfg mask w out) =
      captureOutputCfg (P.step cfg) mask (w ++ (P.outputSymbol cfg).toList) out := by
  have hout : P.outputSymbol cfg = (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output := by
    unfold MultiTapeTM.outputSymbol
    rw [hq]
  rw [hout]
  cases ho : (P.tr q cfg.inputSymbol cfg.workTapeSymbols).output with
  | none =>
    rw [step_captureOutputCfg_of_not_keep P cfg q hq mask w out (by rw [ho]; rfl)]
    exact congrArg (fun v ↦ captureOutputCfg (P.step cfg) mask v out) (List.append_nil w).symm
  | some b =>
    rcases Nat.lt_or_ge w.length mask.length with hlt | hge
    · exact step_captureOutputCfg_of_keep P cfg q hq mask w out b ho hlt
    · have hlen : (w.take mask.length).length = mask.length := by
        rw [List.length_take]
        omega
      have hkeep : ((P.tr q cfg.inputSymbol cfg.workTapeSymbols).output.isSome &&
          (tapeOf mask ((w.take mask.length).length : ℤ)).isSome) = false := by
        rw [hlen, tapeOf_isSome_of_le mask mask.length (le_refl _), Bool.and_false]
      rw [step_captureOutputCfg_of_not_keep P cfg q hq mask w out hkeep]
      refine captureOutputCfg_congr _ mask w _ out ?_
      exact (List.take_append_of_le_length hge).symm

/-- The wrapper never emits. -/
theorem captureOutput_outputSymbol {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (mask w out : List Bool) :
    (captureOutput P).outputSymbol (captureOutputCfg cfg mask w out) = none := by
  unfold MultiTapeTM.outputSymbol
  rw [captureOutputCfg_state]
  cases cfg.state with
  | none => rfl
  | some q => rfl

/-- The wrapper's heads stay within the bound as long as the generator's do and the mask fits. -/
theorem captureOutputCfg_pos {k : ℕ} {S : Type} {input : List Bool} (cfg : Cfg k Bool S input)
    (mask w out : List Bool) (B : ℕ) (hmask : mask.length ≤ B)
    (h : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) (j : Fin (k + 2)) :
    -1 ≤ (captureOutputCfg cfg mask w out).workTapePos j ∧
      (captureOutputCfg cfg mask w out).workTapePos j ≤ B := by
  have hle : ((w.take mask.length).length : ℤ) ≤ (B : ℤ) := by
    have hn : (w.take mask.length).length ≤ B :=
      le_trans (by rw [List.length_take]; omega) hmask
    exact_mod_cast hn
  rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨by change (-1 : ℤ) ≤ ((w.take mask.length).length : ℤ); omega, hle⟩
  · exact ⟨by change (-1 : ℤ) ≤ ((w.take mask.length).length : ℤ); omega, hle⟩
  · exact h i

/-- Bounded prefix capture simulates every generator transition in one step.
The extra tapes occupy no more cells than the mask, and the wrapper is silent. -/
theorem captureOutput_runsTo {k : ℕ} {S : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S} {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P cfg cfg' w t B) (mask out : List Bool) (hmask : mask.length ≤ B) :
    RunsTo (captureOutput P) (captureOutputCfg cfg mask [] out)
      (captureOutputCfg cfg' mask w out) t B := by
  have hstep : ∀ s < t, (captureOutput P).step
      (captureOutputCfg (P.runFrom cfg s) mask (P.outputString cfg s) out) =
      captureOutputCfg (P.runFrom cfg (s + 1)) mask (P.outputString cfg (s + 1)) out := by
    intro s hs
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (h.live s hs)
    rw [step_captureOutputCfg P (P.runFrom cfg s) q hq mask (P.outputString cfg s) out,
      runFrom_succ_eq_step', outputString_succ]
  have hpos : ∀ s ≤ t, ∀ j,
      -1 ≤ (captureOutputCfg (P.runFrom cfg s) mask (P.outputString cfg s) out).workTapePos j ∧
        (captureOutputCfg (P.runFrom cfg s) mask (P.outputString cfg s) out).workTapePos j ≤ B :=
    fun s hs ↦ captureOutputCfg_pos _ mask _ out B hmask (fun i ↦ h.pos s hs i)
  have key := Reaches.ofFamily (captureOutput P)
    (fun s ↦ captureOutputCfg (P.runFrom cfg s) mask (P.outputString cfg s) out) t B
    (fun s hs ↦ h.live s hs) hstep
    (fun s _ ↦ captureOutput_outputSymbol P _ mask _ out) hpos
  have h0 : captureOutputCfg (P.runFrom cfg 0) mask (P.outputString cfg 0) out =
      captureOutputCfg cfg mask [] out := by
    rw [runFrom_zero]
    rfl
  have ht : captureOutputCfg (P.runFrom cfg t) mask (P.outputString cfg t) out =
      captureOutputCfg cfg' mask w out := by
    rw [h.runFrom_eq, h.output]
  simp only [h0, ht] at key
  exact ⟨key, h.halted⟩

/-- Capture a prefix and park both additional heads, preserving the mask. -/
@[expose] def capturePrefix {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  seq (seq (captureOutput P) (returnTape countTape)) (returnTape resultTape)

/-- Prefix capture returns a bounded reversed word and restores all heads.
The generator can still read its original registers throughout the computation. -/
theorem capturePrefix_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) :
    TransformsIn (capturePrefix P)
      (fun input σ ↦ σ resultTape = [] ∧ Pre input (fun i ↦ σ (oldTape i)))
      (fun input σ ↦ tapeCase (σ countTape)
        ((W input (fun i ↦ σ (oldTape i))).take (σ countTape).length).reverse
        (F input (fun i ↦ σ (oldTape i))))
      (fun n ↦ T n + 2 * B n + 4) B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  let c : Cfg k Bool S input :=
    { state := some P.q₀
      inputPos := cfg.inputPos
      workTapes := fun i ↦ cfg.workTapes (oldTape i)
      workTapePos := fun i ↦ cfg.workTapePos (oldTape i)
      output := [] }
  obtain ⟨hFB, t, ht, he⟩ := hP input c (fun i ↦ σ (oldTape i)) rfl
    (fun i ↦ hpark (oldTape i)) hpos (fun i ↦ hσ (oldTape i)) hp.2
    (fun i ↦ hB (oldTape i))
  let w := W input (fun i ↦ σ (oldTape i))
  let mask := σ countTape
  let v := (w.take mask.length).reverse
  have hv : v.length ≤ B input.length := by
    dsimp [v]
    rw [List.length_reverse, List.length_take]
    exact (min_le_left ..).trans (hB countTape)
  let finish := { after c (F input (fun i ↦ σ (oldTape i))) with output := [] ++ w }
  have hc := captureOutput_runsTo he mask cfg.output (hB countTape)
  have hstart : captureOutputCfg c mask [] cfg.output =
      { cfg with state := some (captureOutput P).q₀ } := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
      · exact (hσ countTape).symm
      · simpa only [captureOutputCfg, tapeCase_resultTape, List.take_nil,
          List.reverse_nil] using ((hσ resultTape).trans (congrArg tapeOf hp.1)).symm
      · rfl
    · funext i
      rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
      · simpa only [captureOutputCfg, tapeCase_countTape, List.take_nil,
          List.length_nil, Nat.cast_zero] using (hpark countTape).symm
      · simpa only [captureOutputCfg, tapeCase_resultTape, List.take_nil,
          List.length_nil, Nat.cast_zero] using (hpark resultTape).symm
      · rfl
    · rfl
  rw [hstart] at hc
  let mid := captureOutputCfg finish mask w cfg.output
  have hheads (i : Fin (k + 2)) :
      -1 ≤ mid.workTapePos i ∧ mid.workTapePos i ≤ B input.length := by
    have hh := hc.pos t le_rfl i
    rw [hc.runFrom_eq] at hh
    exact hh
  have hmasklen : 0 ≤ mid.workTapePos countTape ∧
      mid.workTapePos countTape ≤ (mask.length : ℤ) := by
    change 0 ≤ ((w.take mask.length).length : ℤ) ∧
      ((w.take mask.length).length : ℤ) ≤ mask.length
    rw [List.length_take]
    constructor <;> omega
  have hr₁ := returnTape_runsTo countTape
    { mid with state := some (returnTape countTape).q₀ }
    rfl mask rfl (mid.workTapePos countTape) rfl hmasklen.1 hmasklen.2
    (B input.length) hheads
  let parkedMask : Cfg (k + 2) Bool Unit input := { mid with
    state := none
    workTapePos := Function.update mid.workTapePos countTape 0 }
  have hheads' := update_workTapePos_bounds countTape hheads 0 (by omega) (by omega)
  have hr₂ := returnTape_runsTo resultTape
    { parkedMask with state := some (returnTape resultTape).q₀ }
    rfl v rfl ((w.take mask.length).length : ℤ) (by rfl) (by omega)
    (by simp only [v, List.length_reverse]; exact le_rfl) (B input.length) hheads'
  have hs := RunsTo.seqStart hq (RunsTo.seqStart rfl hc hr₁) hr₂
  refine ⟨?_, t + (((w.take mask.length).length : ℤ) + 2).toNat +
      (((w.take mask.length).length : ℤ) + 2).toNat, ?_, hs.congr_target ?_⟩
  · intro i
    rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
    · exact hB countTape
    · exact hv
    · exact hFB i
  · have hl : (w.take mask.length).length ≤ B input.length := by
      simpa only [v, List.length_reverse] using hv
    dsimp only
    omega
  · apply Cfg.ext
    · rfl
    · rfl
    · funext i
      rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩ <;> rfl
    · funext i
      rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
      · exact (hpark countTape).symm
      · exact (hpark resultTape).symm
      · change Function.update (Function.update mid.workTapePos countTape 0)
          resultTape 0 (oldTape i) = cfg.workTapePos (oldTape i)
        rw [Function.update_of_ne (oldTape_ne_resultTape i),
          Function.update_of_ne (oldTape_ne_countTape i)]
        rfl
    · rfl

/-- Replace a saved register by a bounded prefix of a generated word.
The old register remains available to the generator until it finishes. -/
@[expose] def generatedPrefix {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (R : Fin k) :=
  seq (const [] resultTape) (seq (capturePrefix P)
    (seq (copyRev resultTape (oldTape R)) (const [] resultTape)))

/-- A generated prefix replaces one old register after the generator returns.
The mask is preserved and the capture scratch is initialized and cleared on every call. -/
theorem generatedPrefix_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) (R : Fin k) :
    TransformsIn (generatedPrefix P R)
      (fun input σ ↦ Pre input (fun i ↦ σ (oldTape i)))
      (fun input σ ↦ tapeCase (σ countTape) []
        (Function.update (F input (fun i ↦ σ (oldTape i))) R
          ((W input (fun i ↦ σ (oldTape i))).take (σ countTape).length)))
      (fun n ↦ (4 * B n + 9) + ((T n + 2 * B n + 4) +
        ((5 * B n + 12) + (4 * B n + 9)))) B := by
  have hc := Transforms.toIn_of (fun n ↦ const_transforms []
      (resultTape : Fin (k + 2)) (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
  have hr := Transforms.toIn_of (fun n ↦ copyRev_transforms
      resultTape (oldTape R) (oldTape_ne_resultTape R).symm (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (by
      simpa only [List.length_reverse] using hb resultTape))
  have hs := (hc.seq ((capturePrefix_transformsIn hP).seq (hr.seq hc))).mono_pre
    (Pre' := fun input σ ↦ Pre input (fun i ↦ σ (oldTape i))) (by
      intro input σ _ hp
      refine ⟨trivial, ⟨?_, trivial, trivial⟩⟩
      exact ⟨Function.update_self .., by
        simpa only [Function.update_of_ne (oldTape_ne_resultTape _)] using hp⟩)
  refine hs.congr ?_
  intro input σ _
  funext i
  rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
  · simp [Function.update_of_ne (oldTape_ne_resultTape _),
      Function.update_of_ne (oldTape_ne_countTape R).symm,
      Function.update_of_ne countTape_ne_resultTape]
  · simp
  · simp only [Function.update_of_ne (oldTape_ne_resultTape _),
      Function.update_of_ne countTape_ne_resultTape,
      tapeCase_resultTape, List.reverse_reverse]
    by_cases hi : i = R
    · subst i
      simp
    · simp [Function.update_of_ne hi, show oldTape i ≠ oldTape R from
        fun h ↦ hi (Fin.succ_injective _ (Fin.succ_injective _ h))]

end

end Geb.Oitavem.Machine
