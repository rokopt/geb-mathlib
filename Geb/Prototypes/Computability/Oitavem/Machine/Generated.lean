/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.CountOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.ReadOutput
public import Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Contract
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.InputMove
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Const

set_option doc.verso true in
/-!
# Calling generated-word readers

An emitter with a valuation contract supplies length and digit subroutines for its
output. The extra tapes are initialized on each call. The generator's valuation
transformer describes its scratch cleanup and preservation of the caller's data;
the readers inherit that transformer on the generator's tapes. All heads return
to their entry positions, and internal queries preserve the caller's output.

## Main definitions

* {lit}`EmitsIn` specifies emission with a bounded final valuation and parked heads.
* {lit}`generatedLength` initializes and runs an output counter.
* {lit}`generatedAt` copies a query, clears the result, reads a digit, and clears
  the consumed query counter.

## Main statements

* {lit}`countOutput_transformsIn` and {lit}`readOutput_transformsIn` lift emitter
  contracts to the existing subroutine contract.
* {lit}`generatedLength_transformsIn` and {lit}`generatedAt_transformsIn` include
  scratch initialization, allowing repeated calls through ordinary sequencing.
* {lit}`TransformsIn.seqEmitsIn` composes an internal query with an emitter.

## Implementation notes

The contracts relate programs to CSLib configurations and inherit their
{lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, generated word, subroutine, register preservation
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- A halting emitter from a parked valuation, with exact output, a bounded
final valuation, and the input head returned home. -/
@[expose] def EmitsIn {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (Pre : List Bool → (Fin k → List Bool) → Prop)
    (F : List Bool → (Fin k → List Bool) → Fin k → List Bool)
    (W : List Bool → (Fin k → List Bool) → List Bool) (T B : ℕ → ℕ) : Prop :=
  ∀ (input : List Bool) (cfg : Cfg k Bool S input) (σ : Fin k → List Bool),
    cfg.state = some P.q₀ → Parked cfg → cfg.inputPos.val = 0 → Holds cfg σ →
    Pre input σ → Bounded σ (B input.length) →
    Bounded (F input σ) (B input.length) ∧
      ∃ t ≤ T input.length,
        Emits P cfg { after cfg (F input σ) with output := cfg.output ++ W input σ }
          (W input σ) t (B input.length)

/-- An emitter contract holds under a stronger precondition. -/
theorem EmitsIn.mono_pre {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre Pre' : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B)
    (hpre : ∀ input σ, Bounded σ (B input.length) → Pre' input σ → Pre input σ) :
    EmitsIn P Pre' F W T B :=
  fun input cfg σ hq hpark hpos hσ hp hB ↦
    h input cfg σ hq hpark hpos hσ (hpre input σ hB hp) hB

/-- An emitter contract holds with a larger bound on the number of transitions. -/
theorem EmitsIn.mono_time {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T T' B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B) (hT : ∀ n, T n ≤ T' n) : EmitsIn P Pre F W T' B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  obtain ⟨hFB, t, ht, he⟩ := h input cfg σ hq hpark hpos hσ hp hB
  exact ⟨hFB, t, ht.trans (hT _), he⟩

/-- An emitter contract admits an equal valuation transformer on its precondition. -/
theorem EmitsIn.congr {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F F' : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B)
    (hF : ∀ input σ, Pre input σ → F input σ = F' input σ) :
    EmitsIn P Pre F' W T B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  obtain ⟨hFB, t, ht, he⟩ := h input cfg σ hq hpark hpos hσ hp hB
  rw [hF input σ hp] at hFB he
  exact ⟨hFB, t, ht, he⟩

/-- An emitter contract admits an equal output word wherever its precondition holds. -/
theorem EmitsIn.congr_output {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W V : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B) (hW : ∀ input σ, Pre input σ → W input σ = V input σ) :
    EmitsIn P Pre F V T B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  obtain ⟨hFB, t, ht, he⟩ := h input cfg σ hq hpark hpos hσ hp hB
  rw [hW input σ hp] at he
  exact ⟨hFB, t, ht, he⟩

/-- Counting a contracted emitter preserves its final valuation on the old tapes
and returns a binary length on the additional tape. -/
theorem countOutput_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B)
    (hsize : ∀ input σ, Pre input σ → Bounded σ (B input.length) →
      ((W input σ).length + 1).size ≤ B input.length) :
    TransformsIn (countOutput P)
      (fun input σ ↦ σ 0 = [] ∧ Pre input (fun i ↦ σ i.succ))
      (fun input σ ↦ Fin.cons (counterWord (W input (fun i ↦ σ i.succ)).length)
        (F input (fun i ↦ σ i.succ)))
      (fun n ↦ T n * (2 * B n + 5)) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  let c : Cfg k Bool S input :=
    { state := some P.q₀
      inputPos := cfg.inputPos
      workTapes := fun i ↦ cfg.workTapes i.succ
      workTapePos := fun i ↦ cfg.workTapePos i.succ
      output := [] }
  obtain ⟨hFB, t, ht, hem⟩ := hP input c (fun i ↦ σ i.succ) rfl
    (fun i ↦ hpark i.succ) hpos (fun i ↦ hσ i.succ) hpre.2 (fun i ↦ hB i.succ)
  have hs := hsize input (fun i ↦ σ i.succ) hpre.2 (fun i ↦ hB i.succ)
  obtain ⟨u, hu, hrun⟩ := countOutput_runsTo P hem 0 cfg.output (by simpa using hs)
  have hstart : countOutputCfg c 0 cfg.output = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      refine Fin.cases ?_ (fun _ ↦ rfl) i
      exact ((hσ 0).trans (congrArg tapeOf hpre.1)).symm
    · funext i
      exact Fin.cases (hpark 0).symm (fun _ ↦ rfl) i
    · rfl
  rw [hstart, Nat.zero_add] at hrun
  refine ⟨?_, u, hu.trans (Nat.mul_le_mul_right _ ht), hrun.congr_target ?_⟩
  · intro i
    refine Fin.cases ?_ hFB i
    change (counterWord _).length ≤ _
    rw [length_counterWord]
    exact (size_le_size (Nat.le_succ _)).trans hs
  · apply Cfg.ext
    · rfl
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    · funext i
      exact Fin.cases (hpark 0).symm (fun _ ↦ rfl) i
    · rfl

/-- Initialize the counter and count the emitter's output, including on reused tapes. -/
@[expose] def generatedLength {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  seq (const [] (0 : Fin (k + 1))) (countOutput P)

/-- A generated length reader initializes its extra counter. The emitter's
precondition and postcondition apply unchanged to its old tapes. -/
theorem generatedLength_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B)
    (hsize : ∀ input σ, Pre input σ → Bounded σ (B input.length) →
      ((W input σ).length + 1).size ≤ B input.length) :
    TransformsIn (generatedLength P)
      (fun input σ ↦ Pre input (fun i ↦ σ i.succ))
      (fun input σ ↦ Fin.cons (counterWord (W input (fun i ↦ σ i.succ)).length)
        (F input (fun i ↦ σ i.succ)))
      (fun n ↦ (4 * B n + 9) + T n * (2 * B n + 5)) B := by
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (0 : Fin (k + 1)) (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  refine ((hc.seq (countOutput_transformsIn hP hsize)).mono_pre ?_).congr ?_
  · intro input σ _ hpre
    exact ⟨trivial, Function.update_self .., by simpa using hpre⟩
  · intro input σ _
    simp

/-- Reading a contracted emitter returns a digit and preserves its final valuation
on the old tapes. The query counter is consumed by the underlying reader. -/
theorem readOutput_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (readOutput P)
      (fun input σ ↦ ∃ q, σ countTape = counterWord q ∧ σ resultTape = [] ∧
        Pre input (fun i ↦ σ (oldTape i)))
      (fun input σ ↦ tapeCase
        (counterWord (counterValue (σ countTape) - (W input (fun i ↦ σ (oldTape i))).length))
        ((W input (fun i ↦ σ (oldTape i)))[counterValue (σ countTape)]?).toList
        (F input (fun i ↦ σ (oldTape i))))
      (fun n ↦ T n * (2 * B n + 8)) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨q, hC, hR, hpre⟩ := hpre
  let c : Cfg k Bool S input :=
    { state := some P.q₀
      inputPos := cfg.inputPos
      workTapes := fun i ↦ cfg.workTapes (oldTape i)
      workTapePos := fun i ↦ cfg.workTapePos (oldTape i)
      output := [] }
  obtain ⟨hFB, t, ht, hem⟩ := hP input c (fun i ↦ σ (oldTape i)) rfl
    (fun i ↦ hpark (oldTape i)) hpos (fun i ↦ hσ (oldTape i)) hpre
    (fun i ↦ hB (oldTape i))
  have hqB : q.size ≤ B input.length := by
    simpa only [hC, length_counterWord] using hB countTape
  obtain ⟨u, hu, hrun⟩ := readOutput_runsTo P hem q cfg.output (B input.length) le_rfl hqB
  have hstart : wrapCfg c false q [] cfg.output = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      refine Fin.cases ?_ (Fin.cases ?_ (fun _ ↦ rfl)) i
      · exact ((hσ countTape).trans (congrArg tapeOf hC)).symm
      · exact ((hσ resultTape).trans (congrArg tapeOf hR)).symm
    · funext i
      exact Fin.cases (hpark countTape).symm
        (Fin.cases (hpark resultTape).symm (fun _ ↦ rfl)) i
    · rfl
  rw [hstart] at hrun
  dsimp only
  rw [hC, counterValue_counterWord]
  refine ⟨?_, u, hu.trans (Nat.mul_le_mul_right _ ht), hrun.congr_target ?_⟩
  · intro i
    refine Fin.cases ?_ (Fin.cases ?_ hFB) i
    · change (counterWord _).length ≤ _
      rw [length_counterWord]
      exact (size_le_size (Nat.sub_le _ _)).trans hqB
    · exact Option.length_toList_le.trans (hB1 _)
  · apply Cfg.ext
    · rfl
    · rfl
    · funext i
      exact Fin.cases rfl (Fin.cases rfl (fun _ ↦ rfl)) i
    · funext i
      exact Fin.cases (hpark countTape).symm
        (Fin.cases (hpark resultTape).symm (fun _ ↦ rfl)) i
    · rfl

/-- An emitter tape is distinct from the digit reader's result tape. -/
theorem oldTape_ne_resultTape {k : ℕ} (i : Fin k) : oldTape i ≠ resultTape := by
  intro h
  have := congrArg Fin.val h
  simp only [oldTape, resultTape, Fin.val_succ, Fin.val_zero] at this
  omega

/-- Read an emitted word at a saved query on an old tape, initializing both extra
tapes and clearing the countdown on return. -/
@[expose] def generatedAt {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (Q : Fin k) :=
  seq (copy (oldTape Q) countTape)
    (seq (const [] resultTape) (seq (readOutput P) (const [] countTape)))

/-- Generated digit queries accept arbitrary contents on their two extra tapes.
The query source and other old tapes follow the emitter's own transformer. -/
theorem generatedAt_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre F W T B) (Q : Fin k) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (generatedAt P Q)
      (fun input σ ↦ (∃ q, σ (oldTape Q) = counterWord q) ∧
        Pre input (fun i ↦ σ (oldTape i)))
      (fun input σ ↦ tapeCase []
        ((W input (fun i ↦ σ (oldTape i)))[counterValue (σ (oldTape Q))]?).toList
        (F input (fun i ↦ σ (oldTape i))))
      (fun n ↦ T n * (2 * B n + 8) + 13 * B n + 30) B := by
  have hc (i : Fin (k + 2)) :=
    Transforms.toIn_of (fun n ↦ const_transforms [] i (B n))
      (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hcopy := Transforms.toIn_of
    (fun n ↦ copy_transforms (oldTape Q) countTape (oldTape_ne_countTape Q) (B n))
    (fun _ _ ↦ True) (fun _ σ hB _ ↦ hB.update (hB (oldTape Q)))
  have h := hcopy.seq ((hc resultTape).seq ((readOutput_transformsIn hP hB1).seq (hc countTape)))
  refine ((h.mono_time (fun n ↦ by omega)).mono_pre ?_).congr ?_
  · intro input σ _ hpre
    obtain ⟨⟨q, hq⟩, hp⟩ := hpre
    refine ⟨trivial, trivial, ⟨q, ?_, Function.update_self .., ?_⟩, trivial⟩
    · simpa [Function.update_of_ne, countTape_ne_resultTape] using hq
    · simpa only [Function.update_of_ne (oldTape_ne_resultTape _),
        Function.update_of_ne (oldTape_ne_countTape _)] using hp
  · intro input σ _
    simp only [Function.update_of_ne (oldTape_ne_resultTape _),
      Function.update_of_ne (oldTape_ne_countTape _),
      Function.update_of_ne countTape_ne_resultTape, Function.update_self,
      update_tapeCase_countTape]

/-- A silent subroutine followed by an emitter composes their valuation effects
and uses the emitter's word at the intermediate valuation. -/
theorem _root_.Geb.SizeBounded.Logspace.Machine.TransformsIn.seqEmitsIn
    {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁} {Q : MultiTapeTM k Bool S₂}
    {Pre₁ Pre₂ : List Bool → (Fin k → List Bool) → Prop}
    {F G : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B : ℕ → ℕ}
    (hP : TransformsIn P Pre₁ F T₁ B) (hQ : EmitsIn Q Pre₂ G W T₂ B) :
    EmitsIn (seq P Q) (fun input σ ↦ Pre₁ input σ ∧ Pre₂ input (F input σ))
      (fun input σ ↦ G input (F input σ)) (fun input σ ↦ W input (F input σ))
      (fun n ↦ T₁ n + T₂ n) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨hFB, t₁, ht₁, r₁⟩ := hP input { cfg with state := some P.q₀ }
    σ rfl hpark hpos hσ hpre.1 hB
  obtain ⟨hGB, t₂, ht₂, r₂⟩ := hQ input
    { after cfg (F input σ) with state := some Q.q₀ }
    (F input σ) rfl hpark hpos (fun _ ↦ rfl) hpre.2 hFB
  exact ⟨hGB, t₁ + t₂, Nat.add_le_add ht₁ ht₂, RunsTo.seqStartEmits hq r₁ r₂⟩

/-- A halted emission's head bound controls space at every time, including after halting. -/
theorem _root_.Geb.SizeBounded.Machine.Emits.spaceUsed_le_all
    {k : ℕ} {S : Type} {input : List Bool} {P : MultiTapeTM k Bool S}
    {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P cfg cfg' w t B) (s : ℕ) : P.spaceUsed cfg s ≤ k * (B + 2) := by
  have hpos (u : ℕ) (i : Fin k) :
      -1 ≤ (P.runFrom cfg u).workTapePos i ∧ (P.runFrom cfg u).workTapePos i ≤ B := by
    by_cases hu : u ≤ t
    · exact h.pos u hu i
    · have he : P.runFrom cfg u = cfg' := by
        rw [← Nat.add_sub_of_le (by omega : t ≤ u), runFrom_add, h.runFrom_eq,
          runFrom_of_halt _ h.halted]
      rw [he]
      simpa only [h.runFrom_eq] using h.pos t le_rfl i
  unfold spaceUsed
  calc
    _ ≤ ∑ _ : Fin k, (B + 2) := Finset.sum_le_sum fun i _ ↦
      spaceUsedByTape_le_of_pos P cfg s B i (fun u _ ↦ hpos u i)
    _ = k * (B + 2) := by simp

/-- A finite emitter whose parked contract has logarithmic head bounds has simultaneous
polynomial time and logarithmic space. Moving the initial input head home is included. -/
theorem EmitsIn.computes_polytime_logspace {k : ℕ} {S : Type} [Finite S]
    {P : MultiTapeTM k Bool S} {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B) (hpre : ∀ input, Pre input (fun _ ↦ []))
    (c : ℕ) (hB : ∀ n, B n ≤ c * (n.size + 1)) :
    ∃ C d : ℕ, ComputesFunInTimeAndSpace (seq inBack P) (.refl _) (.refl _)
      (fun input ↦ W input (fun _ ↦ []))
      (fun input ↦ C * (input.length + 1) ^ d)
      (fun input ↦ C * (input.length.size + 1)) := by
  let : Fintype S := Fintype.ofFinite S
  have hem (input : List Bool) :
      ∃ cfg' t, Emits (seq inBack P) ((seq inBack P).initCfg input) cfg'
        (W input (fun _ ↦ [])) t (B input.length) := by
    let cfg := (seq inBack P).initCfg input
    have r₁ := inBack_runsTo_of_pos { cfg with state := some () } rfl
      (by change 1 ≠ 0; omega) (B input.length) (fun _ ↦ by
        change -1 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ B input.length
        constructor <;> omega)
    obtain ⟨_, t, _, r₂⟩ := h input
      { cfg with state := some P.q₀, inputPos := ⟨0, by omega⟩ }
      (fun _ ↦ []) rfl (fun _ ↦ rfl) rfl (fun _ ↦ tapeOf_nil.symm)
      (hpre input) (fun _ ↦ Nat.zero_le _)
    exact ⟨_, 1 + t, RunsTo.seqStartEmits rfl r₁ r₂⟩
  apply Machine.computes_polytime_logspace _ _ (k * (c + 2))
  · intro input
    obtain ⟨cfg', t, he⟩ := hem input
    refine ⟨t, ?_, ?_⟩
    · rw [he.runFrom_eq]
      exact he.halted
    · rw [initCfg_runFrom_output]
      exact he.output
  · intro input s
    obtain ⟨cfg', t, he⟩ := hem input
    refine (he.spaceUsed_le_all s).trans ?_
    calc
      k * (B input.length + 2) ≤ k * ((c + 2) * (input.length.size + 1)) :=
        Nat.mul_le_mul_left k (by rw [Nat.add_mul]; have := hB input.length; omega)
      _ = k * (c + 2) * (input.length.size + 1) := (Nat.mul_assoc ..).symm

end

end Geb.Oitavem.Machine
