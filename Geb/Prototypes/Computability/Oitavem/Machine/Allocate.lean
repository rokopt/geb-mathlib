/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Generated

set_option doc.verso true in
/-!
# Allocating subroutine tapes

A finite tape layout partitions the caller's tapes into a callee's tapes and
protected tapes. A callee runs with the same finite control and the same step
count under this layout. Protected tapes and their heads remain unchanged at
every step, including when the callee emits on its halting transition.

## Main definitions

* {lit}`onTapes` places a machine in a larger tape layout.
* {lit}`onTapesCfg` combines a callee configuration with protected tapes.

## Main statements

* {lit}`onTapes_step` and {lit}`onTapes_runFrom` give exact simulation.
* {lit}`EmitsIn.onTapes` and {lit}`TransformsIn.onTapes` preserve subroutine
  contracts, including their bounds and the caller's protected registers.

## Implementation notes

The layout is an explicit equivalence, so allocation requires no search or
choice. The run contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, register allocation, subroutine
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace.Machine

public section

/-- Run a machine on the left part of a tape layout, leaving the right part untouched. -/
@[expose] def onTapes {k m l : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (e : Fin m ≃ Fin k ⊕ Fin l) : MultiTapeTM m Bool S where
  q₀ := P.q₀
  tr q input work :=
    let a := P.tr q input (fun i ↦ work (e.symm (.inl i)))
    { inputTape := a.inputTape
      workTapes := fun i ↦ Sum.elim a.workTapes (fun _ ↦ (none, 0)) (e i)
      output := a.output
      state := a.state }

/-- Combine a callee configuration with the caller's protected tapes and heads. -/
@[expose] def onTapesCfg {k m l : ℕ} {S : Type} {input : List Bool}
    (e : Fin m ≃ Fin k ⊕ Fin l) (cfg : Cfg k Bool S input)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) : Cfg m Bool S input where
  state := cfg.state
  inputPos := cfg.inputPos
  workTapes := fun i ↦ Sum.elim cfg.workTapes tapes (e i)
  workTapePos := fun i ↦ Sum.elim cfg.workTapePos heads (e i)
  output := cfg.output

/-- Allocation commutes with a machine step, with all protected tapes fixed. -/
theorem onTapes_step {k m l : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (e : Fin m ≃ Fin k ⊕ Fin l)
    (cfg : Cfg k Bool S input) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (onTapes P e).step (onTapesCfg e cfg tapes heads) =
      onTapesCfg e (P.step cfg) tapes heads := by
  cases hq : cfg.state with
  | none => simp [step, onTapesCfg, hq]
  | some q =>
    simp only [step, onTapesCfg, hq, onTapes, Cfg.workTapeSymbols,
      Equiv.apply_symm_apply, Sum.elim_inl]
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      cases hi : e i <;> simp [Action.apply, hi]
      rfl
    · funext i
      cases hi : e i <;> simp [Action.apply, hi]
      rfl
    · rfl

/-- Allocation commutes with every finite run, keeping the caller's tapes fixed. -/
theorem onTapes_runFrom {k m l : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (e : Fin m ≃ Fin k ⊕ Fin l)
    (cfg : Cfg k Bool S input) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (t : ℕ) :
    (onTapes P e).runFrom (onTapesCfg e cfg tapes heads) t =
      onTapesCfg e (P.runFrom cfg t) tapes heads :=
  runFrom_comm_of_step (fun c ↦ onTapesCfg e c tapes heads)
    (fun c ↦ onTapes_step P e c tapes heads) cfg t

/-- Allocation preserves the symbol emitted by a transition. -/
theorem onTapes_outputSymbol {k m l : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (e : Fin m ≃ Fin k ⊕ Fin l)
    (cfg : Cfg k Bool S input) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (onTapes P e).outputSymbol (onTapesCfg e cfg tapes heads) = P.outputSymbol cfg := by
  cases hq : cfg.state <;>
    simp only [outputSymbol, onTapesCfg, hq, onTapes, Cfg.workTapeSymbols,
      Equiv.apply_symm_apply, Sum.elim_inl]
  rfl

/-- Allocation preserves the full output, including the halting transition. -/
theorem onTapes_outputString {k m l : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (e : Fin m ≃ Fin k ⊕ Fin l)
    (cfg : Cfg k Bool S input) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (t : ℕ) :
    (onTapes P e).outputString (onTapesCfg e cfg tapes heads) t = P.outputString cfg t := by
  refine Nat.rec rfl (fun t ih ↦ ?_) t
  rw [outputString_succ, outputString_succ, ih, onTapes_runFrom, onTapes_outputSymbol]

/-- A bounded emission lifts to a larger layout whose protected heads satisfy the bound. -/
theorem _root_.Geb.SizeBounded.Machine.Emits.onTapes
    {k m l : ℕ} {S : Type} {input : List Bool} {P : MultiTapeTM k Bool S}
    {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P cfg cfg' w t B) (e : Fin m ≃ Fin k ⊕ Fin l)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ)
    (hheads : ∀ i, -1 ≤ heads i ∧ heads i ≤ B) :
    Emits (onTapes P e) (onTapesCfg e cfg tapes heads) (onTapesCfg e cfg' tapes heads)
      w t B where
  live := by
    intro s hs
    rw [onTapes_runFrom]
    exact h.live s hs
  runFrom_eq := by rw [onTapes_runFrom, h.runFrom_eq]
  pos := by
    intro s hs i
    rw [onTapes_runFrom]
    change -1 ≤ Sum.elim _ heads (e i) ∧ Sum.elim _ heads (e i) ≤ (B : ℤ)
    cases e i with
    | inl j => exact h.pos s hs j
    | inr j => exact hheads j
  output := by rw [onTapes_outputString, h.output]
  halted := h.halted

/-- Insert a callee's final valuation into the caller's tape layout. -/
@[expose] def onTapesVal {k m l : ℕ} (e : Fin m ≃ Fin k ⊕ Fin l)
    (σ : Fin m → List Bool) (τ : Fin k → List Bool) : Fin m → List Bool :=
  fun i ↦ Sum.elim τ (fun j ↦ σ (e.symm (.inr j))) (e i)

/-- An allocated valuation agrees with the callee on its tapes. -/
@[simp] theorem onTapesVal_left {k m l : ℕ} (e : Fin m ≃ Fin k ⊕ Fin l)
    (σ : Fin m → List Bool) (τ : Fin k → List Bool) (i : Fin k) :
    onTapesVal e σ τ (e.symm (.inl i)) = τ i := by simp [onTapesVal]

/-- An allocated valuation preserves every protected register. -/
@[simp] theorem onTapesVal_right {k m l : ℕ} (e : Fin m ≃ Fin k ⊕ Fin l)
    (σ : Fin m → List Bool) (τ : Fin k → List Bool) (i : Fin l) :
    onTapesVal e σ τ (e.symm (.inr i)) = σ (e.symm (.inr i)) := by simp [onTapesVal]

/-- Reinstalling the unchanged callee registers preserves the whole caller valuation. -/
@[simp] theorem onTapesVal_self {k m l : ℕ} (e : Fin m ≃ Fin k ⊕ Fin l)
    (σ : Fin m → List Bool) :
    onTapesVal e σ (fun i ↦ σ (e.symm (.inl i))) = σ := by
  funext i
  dsimp only [onTapesVal]
  cases hi : e i <;> dsimp only [Sum.elim] <;> rw [← hi, e.symm_apply_apply]

/-- Updating one callee register updates exactly its allocated caller register. -/
@[simp] theorem onTapesVal_update {k m l : ℕ} (e : Fin m ≃ Fin k ⊕ Fin l)
    (σ : Fin m → List Bool) (R : Fin k) (w : List Bool) :
    onTapesVal e σ (Function.update (fun i ↦ σ (e.symm (.inl i))) R w) =
      Function.update σ (e.symm (.inl R)) w := by
  funext i
  rcases hi : e i with j | j
  · have he : i = e.symm (.inl j) := (e.symm_apply_apply i).symm.trans (congrArg e.symm hi)
    rw [he, onTapesVal_left]
    by_cases hj : j = R
    · subst j
      simp
    · rw [Function.update_of_ne hj, Function.update_of_ne]
      exact fun h ↦ hj (Sum.inl.inj (e.symm.injective h))
  · have he : i = e.symm (.inr j) := (e.symm_apply_apply i).symm.trans (congrArg e.symm hi)
    rw [he, onTapesVal_right, Function.update_of_ne]
    intro h
    have := e.symm.injective h
    cases this

/-- Reserve the first tape for a caller, placing the callee on successor-indexed tapes. -/
@[expose] def reserveTape (k : ℕ) : Fin (k + 1) ≃ Fin k ⊕ Fin 1 where
  toFun := Fin.cases (.inr 0) .inl
  invFun := Sum.elim Fin.succ (fun _ ↦ 0)
  left_inv := Fin.cases rfl (fun _ ↦ rfl)
  right_inv := Sum.rec (fun _ ↦ rfl) (Fin.cases rfl (fun i ↦ i.elim0))

/-- The callee's tape follows the reserved tape. -/
@[simp] theorem reserveTape_symm_inl (k : ℕ) (i : Fin k) :
    (reserveTape k).symm (.inl i) = i.succ := rfl

/-- The protected tape is the first tape. -/
@[simp] theorem reserveTape_symm_inr (k : ℕ) (i : Fin 1) :
    (reserveTape k).symm (.inr i) = 0 := rfl

/-- Emitter contracts survive tape allocation with the same time and head bounds. -/
theorem EmitsIn.onTapes {k m l : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F W T B) (e : Fin m ≃ Fin k ⊕ Fin l) :
    EmitsIn (onTapes P e)
      (fun input σ ↦ Pre input (fun i ↦ σ (e.symm (.inl i))))
      (fun input σ ↦ onTapesVal e σ (F input (fun i ↦ σ (e.symm (.inl i)))))
      (fun input σ ↦ W input (fun i ↦ σ (e.symm (.inl i)))) T B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  let c : Cfg k Bool S input :=
    { cfg with workTapes := fun i ↦ cfg.workTapes (e.symm (.inl i))
               workTapePos := fun i ↦ cfg.workTapePos (e.symm (.inl i)) }
  obtain ⟨hFB, t, ht, hem⟩ := h input c (fun i ↦ σ (e.symm (.inl i))) hq
    (fun i ↦ hpark _) hpos (fun i ↦ hσ _) hpre (fun i ↦ hB _)
  have he := hem.onTapes e (fun i ↦ cfg.workTapes (e.symm (.inr i)))
    (fun i ↦ cfg.workTapePos (e.symm (.inr i))) (by
      intro i
      rw [hpark]
      constructor <;> omega)
  have hstart : onTapesCfg e c (fun i ↦ cfg.workTapes (e.symm (.inr i)))
      (fun i ↦ cfg.workTapePos (e.symm (.inr i))) = cfg := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      simp only [onTapesCfg, c]
      cases hi : e i <;> dsimp only [Sum.elim] <;> rw [← hi, e.symm_apply_apply]
    · funext i
      simp only [onTapesCfg, c]
      cases hi : e i <;> dsimp only [Sum.elim] <;> rw [← hi, e.symm_apply_apply]
  rw [hstart] at he
  refine ⟨?_, t, ht, he.congr_target ?_⟩
  · intro i
    dsimp only [onTapesVal]
    cases e i with
    | inl j => exact hFB j
    | inr j => exact hB _
  · refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      dsimp only [onTapesCfg, after, onTapesVal]
      cases hi : e i with
      | inl j => rfl
      | inr j => exact hσ _
    · simpa only [onTapesCfg, after] using congrArg Cfg.workTapePos hstart

/-- Silent subroutine contracts are emitter contracts for the empty word. -/
theorem _root_.Geb.SizeBounded.Logspace.Machine.TransformsIn.toEmitsIn
    {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : TransformsIn P Pre F T B) : EmitsIn P Pre F (fun _ _ ↦ []) T B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨hFB, t, ht, hr⟩ := h input cfg σ hq hpark hpos hσ hpre hB
  exact ⟨hFB, t, ht, by simpa only [List.append_nil, after] using hr.toEmits⟩

/-- An emitter contract for the empty word is a silent subroutine contract. -/
theorem EmitsIn.toTransformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : EmitsIn P Pre F (fun _ _ ↦ []) T B) : TransformsIn P Pre F T B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  obtain ⟨hFB, t, ht, hr⟩ := h input cfg σ hq hpark hpos hσ hpre hB
  exact ⟨hFB, t, ht, by simpa only [List.append_nil, after] using hr.toRunsTo⟩

/-- Sequential emitters concatenate their words and compose their valuation effects.
The second word is evaluated in the valuation returned by the first emitter. -/
theorem EmitsIn.seqEmitsIn {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {Q : MultiTapeTM k Bool S₂} {Pre₁ Pre₂ : List Bool → (Fin k → List Bool) → Prop}
    {F G : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W V : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B : ℕ → ℕ}
    (hP : EmitsIn P Pre₁ F W T₁ B) (hQ : EmitsIn Q Pre₂ G V T₂ B) :
    EmitsIn (seq P Q) (fun input σ ↦ Pre₁ input σ ∧ Pre₂ input (F input σ))
      (fun input σ ↦ G input (F input σ))
      (fun input σ ↦ W input σ ++ V input (F input σ)) (fun n ↦ T₁ n + T₂ n) B := by
  intro input cfg σ hq hpark hpos hσ hpre hB
  rw [liftL_start P Q cfg hq]
  obtain ⟨hFB, t₁, ht₁, r₁⟩ := hP input { cfg with state := some P.q₀ }
    σ rfl hpark hpos hσ hpre.1 hB
  obtain ⟨hGB, t₂, ht₂, r₂⟩ := hQ input
    { after cfg (F input σ) with state := some Q.q₀, output := cfg.output ++ W input σ }
    (F input σ) rfl hpark hpos (fun _ ↦ rfl) hpre.2 hFB
  refine ⟨hGB, t₁ + t₂, Nat.add_le_add ht₁ ht₂, (r₁.seqEmits r₂).congr_target ?_⟩
  apply Cfg.ext <;> try rfl
  exact List.append_assoc ..

/-- A silent cleanup after emission preserves the emitted word. -/
theorem EmitsIn.seqTransformsIn {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {Q : MultiTapeTM k Bool S₂} {Pre₁ Pre₂ : List Bool → (Fin k → List Bool) → Prop}
    {F G : List Bool → (Fin k → List Bool) → Fin k → List Bool}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B : ℕ → ℕ}
    (hP : EmitsIn P Pre₁ F W T₁ B) (hQ : TransformsIn Q Pre₂ G T₂ B) :
    EmitsIn (seq P Q) (fun input σ ↦ Pre₁ input σ ∧ Pre₂ input (F input σ))
      (fun input σ ↦ G input (F input σ)) W (fun n ↦ T₁ n + T₂ n) B := by
  simpa only [List.append_nil] using hP.seqEmitsIn hQ.toEmitsIn

/-- Silent reader contracts survive allocation without changing time or head bounds. -/
theorem _root_.Geb.SizeBounded.Logspace.Machine.TransformsIn.onTapes
    {k m l : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ → ℕ}
    (h : TransformsIn P Pre F T B) (e : Fin m ≃ Fin k ⊕ Fin l) :
    TransformsIn (Machine.onTapes P e)
      (fun input σ ↦ Pre input (fun i ↦ σ (e.symm (.inl i))))
      (fun input σ ↦ onTapesVal e σ (F input (fun i ↦ σ (e.symm (.inl i))))) T B :=
  (h.toEmitsIn.onTapes e).toTransformsIn

end

end Geb.Oitavem.Machine
