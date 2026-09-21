/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Compose
public import Geb.Prototypes.Computability.Oitavem.Machine.Initial
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Family
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Wrapper
public import Mathlib.Logic.Equiv.Fin.Basic

set_option doc.verso true in
/-!
# Generators with a protected environment

A {lit}`Generator` has a fixed finite machine and a fixed set of environment
registers. All other registers start and finish blank. Its contract holds at
every sufficiently large workspace bound, so several generators can use a
common bound when composed. The output is specified as a function of the
physical input and the protected environment.

## Main definitions

* {lit}`Initialized` requires blank scratch registers outside the environment.
* {lit}`Generator` packages a restoring logarithmic-space emitter.
* {lit}`Generator.mapOutput` applies a finite output transformation.
* {lit}`Generator.length` computes the numerical length of a generated word.
* {lit}`Generator.rename` imports selected values from a caller environment.
* {lit}`Generator.product` combines independent generators in one workspace.

## Main statements

* {lit}`Generator.computes` turns a closed generator into a machine with
  simultaneous polynomial time and logarithmic space bounds.
* {lit}`Generator.call_emitsIn` verifies environment import and private cleanup.

## Implementation notes

These contracts use CSLib configurations and inherit their
{lit}`Classical.choice` dependency. The compiled programs use fixed tape layouts
and executable copies; their allocation does not use choice.

## Tags

Turing machine, logarithmic space, generator, environment, composition
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Every register outside the protected environment is blank. -/
@[expose] def Initialized {m k : ℕ} (env : Fin m → Fin k) (σ : Fin k → List Bool) : Prop :=
  ∀ i, (∀ j, i ≠ env j) → σ i = []

/-- Adding a fresh scratch register preserves initialization on the old registers. -/
theorem Initialized.succ {m k : ℕ} {env : Fin m → Fin k} {σ : Fin (k + 1) → List Bool}
    (h : Initialized (fun i ↦ (env i).succ) σ) :
    Initialized env (fun i ↦ σ i.succ) := by
  intro i hi
  exact h i.succ (fun j he ↦ hi j (Fin.succ_injective _ he))

/-- A fresh first scratch register is blank in an initialized valuation. -/
theorem Initialized.zero {m k : ℕ} {env : Fin m → Fin k} {σ : Fin (k + 1) → List Bool}
    (h : Initialized (fun i ↦ (env i).succ) σ) : σ 0 = [] :=
  h 0 (fun j ↦ (Fin.succ_ne_zero (env j)).symm)

/-- Updating a protected register preserves blank scratch registers. -/
theorem Initialized.update {m k : ℕ} {env : Fin m → Fin k} {σ : Fin k → List Bool}
    (h : Initialized env σ) (j : Fin m) (w : List Bool) :
    Initialized env (Function.update σ (env j) w) := by
  intro i hi
  rw [Function.update_of_ne (hi j)]
  exact h i hi

/-- Restricting an initialized caller to the callee's tapes preserves initialization. -/
theorem Initialized.onTapes {m k l a : ℕ} {env : Fin m → Fin k}
    (e : Fin l ≃ Fin k ⊕ Fin a) {σ : Fin l → List Bool}
    (h : Initialized (fun j ↦ e.symm (.inl (env j))) σ) :
    Initialized env (fun i ↦ σ (e.symm (.inl i))) := by
  intro i hi
  exact h _ (fun j he ↦ hi j (Sum.inl.inj (e.symm.injective he)))

/-- Executable generator data at fixed tape and state types. -/
@[ext] structure GeneratorData (m k : ℕ) (S : Type) : Type where
  /-- Protected environment registers. -/
  env : Fin m → Fin k
  /-- The actual emitting program. -/
  program : MultiTapeTM k Bool S
  /-- A coefficient for the logarithmic head bound. -/
  space : ℕ

/-- Correctness and finiteness of a generator's executable data. -/
@[ext] structure GeneratorBody (m k : ℕ) (S : Type)
    (Pre : List Bool → (Fin m → List Bool) → Prop)
    (W : List Bool → (Fin m → List Bool) → List Bool) : Type extends GeneratorData m k S where
  /-- The control has only finitely many states. -/
  finite : Finite S
  /-- Distinct environment entries occupy distinct registers. -/
  env_injective : Function.Injective env
  /-- The program restores the environment and its initialized scratch registers. -/
  correct : ∀ B : ℕ → ℕ, (∀ n, space * (n.size + 1) ≤ B n) →
    ∃ T, EmitsIn program
      (fun input σ ↦ Pre input (fun i ↦ σ (env i)) ∧ Initialized env σ)
      (fun _ σ ↦ σ) (fun input σ ↦ W input (fun i ↦ σ (env i))) T B

/-- A finite, restoring generator over a protected stored environment. Its tape
and state types are fixed before execution, and its contract holds at every
sufficiently large workspace bound. -/
@[expose] def Generator (m : ℕ)
    (Pre : List Bool → (Fin m → List Bool) → Prop)
    (W : List Bool → (Fin m → List Bool) → List Bool) : Type 1 :=
  Σ k : ℕ, Σ S : Type, GeneratorBody m k S Pre W

namespace Generator

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {W : List Bool → (Fin m → List Bool) → List Bool}

/-- The fixed number of work tapes. -/
abbrev tapes (G : Generator m Pre W) : ℕ := G.1

/-- The fixed control type. -/
abbrev State (G : Generator m Pre W) : Type := G.2.1

/-- The generator's protected register layout. -/
abbrev env (G : Generator m Pre W) : Fin m → Fin G.tapes := G.2.2.env

/-- The generator's executable machine. -/
abbrev program (G : Generator m Pre W) : MultiTapeTM G.tapes Bool G.State := G.2.2.program

/-- The generator's logarithmic workspace coefficient. -/
abbrev space (G : Generator m Pre W) : ℕ := G.2.2.space

/-- A packaged generator has finite control. -/
instance finite (G : Generator m Pre W) : Finite G.State := G.2.2.finite

/-- A packaged generator assigns distinct registers to its environment. -/
theorem env_injective (G : Generator m Pre W) : Function.Injective G.env := G.2.2.env_injective

/-- A packaged generator's restoring contract. -/
theorem correct (G : Generator m Pre W) (B : ℕ → ℕ)
    (hB : ∀ n, G.space * (n.size + 1) ≤ B n) :
    ∃ T, EmitsIn G.program
      (fun input σ ↦ Pre input (fun i ↦ σ (G.env i)) ∧ Initialized G.env σ)
      (fun _ σ ↦ σ) (fun input σ ↦ W input (fun i ↦ σ (G.env i))) T B := G.2.2.correct B hB

end Generator

/-- A family of fixed writes sets its distinct destinations and preserves other registers. -/
theorem composeFin_const {k m : ℕ} (dst : Fin m → Fin k) (w : Fin m → List Bool)
    (hdst : Function.Injective dst) (σ : Fin k → List Bool) :
    (∀ j, composeFin m (fun j σ ↦ Function.update σ (dst j) (w j)) σ (dst j) = w j) ∧
    (∀ i, (∀ j, i ≠ dst j) →
      composeFin m (fun j σ ↦ Function.update σ (dst j) (w j)) σ i = σ i) := by
  revert dst w hdst
  refine Nat.rec (fun _ _ _ ↦ ⟨fun i ↦ i.elim0, fun _ _ ↦ rfl⟩) ?_ m
  intro m ih dst w hdst
  have hs := ih (fun i ↦ dst i.castSucc) (fun i ↦ w i.castSucc)
    (fun i j h ↦ Fin.castSucc_injective _ (hdst h))
  have hne (j : Fin m) : dst j.castSucc ≠ dst (Fin.last m) := by
    intro h
    have h' := congrArg Fin.val (hdst h)
    simp only [Fin.val_castSucc, Fin.val_last] at h'
    omega
  constructor
  · refine Fin.lastCases ?_ (fun j ↦ ?_)
    · rw [composeFin_succ, Function.update_self]
    · rw [composeFin_succ, Function.update_of_ne (hne j)]
      exact hs.1 j
  · intro i hi
    rw [composeFin_succ, Function.update_of_ne (hi (Fin.last m))]
    exact hs.2 i (fun j ↦ hi j.castSucc)

/-- A sequence of register copies preserves a common bound and needs no precondition. -/
theorem copyFamily_transformsIn {k m : ℕ} (src dst : Fin m → Fin k)
    (hne : ∀ j, src j ≠ dst j) (B : ℕ → ℕ) :
    TransformsIn (seqFin m (fun j ↦ StateOf (copy (src j) (dst j)))
      (fun j ↦ copy (src j) (dst j))).2 (fun _ _ ↦ True)
      (fun _ σ ↦ composeFin m (fun j σ ↦ Function.update σ (dst j) (σ (src j))) σ)
      (fun n ↦ m * (5 * B n + 12) + 1) B := by
  have h (j : Fin m) := Transforms.toIn_of
    (fun n ↦ copy_transforms (src j) (dst j) (hne j) (B n)) (fun _ _ ↦ True)
    (fun _ _ hB _ ↦ hB.update (hB (src j)))
  refine (TransformsIn.seqFin B (fun n ↦ 5 * B n + 12) m _ _ _ _ h).mono_pre ?_
  intro input σ _ _
  exact preFin_of_invariant (fun _ _ ↦ True) m _ (fun _ _ _ _ ↦ trivial) input σ trivial

/-- Clearing a fixed family restores reusable scratch registers. -/
theorem clearFamily_transformsIn {k m : ℕ} (dst : Fin m → Fin k) (B : ℕ → ℕ) :
    TransformsIn (seqFin m (fun j ↦ StateOf (const [] (dst j)))
      (fun j ↦ const [] (dst j))).2 (fun _ _ ↦ True)
      (fun _ σ ↦ composeFin m (fun j σ ↦ Function.update σ (dst j) []) σ)
      (fun n ↦ m * (4 * B n + 9) + 1) B := by
  have h (j : Fin m) := Transforms.toIn_of
    (fun n ↦ const_transforms [] (dst j) (B n)) (fun _ _ ↦ True)
    (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  refine (TransformsIn.seqFin B (fun n ↦ 4 * B n + 9) m _ _ _ _ h).mono_pre ?_
  intro input σ _ _
  exact preFin_of_invariant (fun _ _ ↦ True) m _ (fun _ _ _ _ ↦ trivial) input σ trivial

/-- A finite sequence of finite programs has finite control. -/
theorem seqFin_finite {k : ℕ} (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i)) (hS : ∀ i, Finite (S i)) :
    Finite (seqFin m S P).1 := by
  revert S P hS
  refine Nat.rec ?_ ?_ m
  · intro _ _ _
    change Finite Unit
    infer_instance
  intro m ih S P hS
  let := Fintype.ofFinite (S (Fin.last m))
  let := ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ hS i.castSucc)
  let := Fintype.ofFinite (seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1
  change Finite ((seqFin m (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc)).1 ⊕
    S (Fin.last m))
  infer_instance

/-- Emit a protected register and return its head to the parked position. -/
@[expose] def storedGenerator {k : ℕ} (R : Fin k) := seq (writer R) (moveRight R)

/-- Stored-word emission preserves every register, including its source. -/
theorem storedGenerator_emitsIn {k : ℕ} (R : Fin k) (B : ℕ → ℕ) :
    EmitsIn (storedGenerator R) (fun _ _ ↦ True) (fun _ σ ↦ σ)
      (fun _ σ ↦ σ R) (fun n ↦ 2 * B n + 4) B := by
  intro input cfg σ hq hpark _ hσ _ hB
  have hheads (i : Fin k) : -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    rw [hpark i]
    constructor <;> omega
  have he := writer_emits R { cfg with state := some (writer R).q₀ }
    rfl (σ R) (hσ R) hpark (B input.length) (hB R)
  have hr := moveRight_runsTo R
    { cfg with state := some ()
               workTapePos := Function.update cfg.workTapePos R (-1)
               output := cfg.output ++ σ R } rfl (B input.length)
    (update_workTapePos_bounds R hheads _ (by omega) (by omega)) (by simp)
  have h := he.seqEmits hr.toEmits
  rw [← liftL_start (writer R) (moveRight R) cfg hq, List.append_nil] at h
  have hreturn : Function.update cfg.workTapePos R 0 = cfg.workTapePos := by
    rw [← hpark R]
    exact Function.update_eq_self ..
  refine ⟨hB, _, ?_, h.congr_target ?_⟩
  · change 2 * (σ R).length + 3 + 1 ≤ 2 * B input.length + 4
    have := hB R
    omega
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext hσ
  · simp only [liftR, Function.update_self, neg_add_cancel, Function.update_idem, hreturn, after]
  · rfl

namespace Generator

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {W : List Bool → (Fin m → List Bool) → List Bool}

/-- Allocate a generator's tapes within a larger workspace. -/
@[expose] def allocate (G : Generator m Pre W) {k l : ℕ}
    (e : Fin k ≃ Fin G.tapes ⊕ Fin l) : Generator m Pre W :=
  ⟨k, G.State,
    { finite := G.finite
      env := fun i ↦ e.symm (.inl (G.env i))
      env_injective := fun _ _ h ↦ G.env_injective (Sum.inl.inj (e.symm.injective h))
      program := onTapes G.program e
      space := G.space
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B hB
        refine ⟨T, ((hT.onTapes e).congr (fun _ σ _ ↦ onTapesVal_self e σ)).mono_pre ?_⟩
        intro input σ _ hp
        refine ⟨hp.1, fun i hi ↦ hp.2 _ (fun j he ↦ ?_)⟩
        exact hi j (Sum.inl.inj (e.symm.injective he))
    }⟩

/-- Replace the output specification by an equal word on the environment precondition. -/
@[expose] def congr (G : Generator m Pre W)
    {V : List Bool → (Fin m → List Bool) → List Bool}
    (hW : ∀ input σ, Pre input σ → W input σ = V input σ) : Generator m Pre V :=
  ⟨G.tapes, G.State,
    { finite := G.finite
      env := G.env
      env_injective := G.env_injective
      program := G.program
      space := G.space
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B hB
        exact ⟨T, hT.congr_output (fun input σ hp ↦ hW input _ hp.1)⟩
    }⟩

/-- Place a callee after the caller's protected environment. -/
@[expose] def callLayout (m k : ℕ) : Fin (m + k) ≃ Fin k ⊕ Fin m :=
  finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

/-- Callee registers follow the caller's environment registers. -/
@[simp] theorem callLayout_symm_inl (m k : ℕ) (i : Fin k) :
    (callLayout m k).symm (.inl i) = i.natAdd m := rfl

/-- Caller registers occupy the initial segment of the combined layout. -/
@[simp] theorem callLayout_symm_inr (m k : ℕ) (i : Fin m) :
    (callLayout m k).symm (.inr i) = i.castAdd k := rfl

/-- Copy selected caller values into a private environment, run the generator,
then clear the private environment. Selection may repeat caller registers. -/
@[expose] def call {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) :=
  let sourceReg (i : Fin m) := (src i).castAdd G.tapes
  let targetReg (i : Fin m) := (G.env i).natAdd l
  seq (seq (seqFin m (fun i ↦ StateOf (copy (sourceReg i) (targetReg i)))
      (fun i ↦ copy (sourceReg i) (targetReg i))).2 (onTapes G.program (callLayout l G.tapes)))
    (seqFin m (fun i ↦ StateOf (const [] (targetReg i))) (fun i ↦ const [] (targetReg i))).2

/-- Importing an environment uses finitely many additional copies and states. -/
theorem call_finite {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) :
    Finite (StateOf (G.call src)) := by
  let := Fintype.ofFinite G.State
  let sourceReg (i : Fin m) := (src i).castAdd G.tapes
  let targetReg (i : Fin m) := (G.env i).natAdd l
  let h₁ := seqFin_finite m (fun i ↦ StateOf (copy (sourceReg i) (targetReg i)))
    (fun i ↦ copy (sourceReg i) (targetReg i)) (fun _ ↦ inferInstance)
  let h₂ := seqFin_finite m (fun i ↦ StateOf (const [] (targetReg i)))
    (fun i ↦ const [] (targetReg i)) (fun _ ↦ inferInstance)
  let := Fintype.ofFinite (seqFin m (fun i ↦ StateOf (copy (sourceReg i) (targetReg i)))
    (fun i ↦ copy (sourceReg i) (targetReg i))).1
  let := Fintype.ofFinite (seqFin m (fun i ↦ StateOf (const [] (targetReg i)))
    (fun i ↦ const [] (targetReg i))).1
  unfold call
  infer_instance

/-- Calls preserve the caller's environment and return all private tapes blank. -/
theorem call_emitsIn {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    {Pre' : List Bool → (Fin l → List Bool) → Prop}
    (hpre : ∀ input σ, Pre' input σ → Pre input (fun i ↦ σ (src i)))
    (B : ℕ → ℕ) (hB : ∀ n, G.space * (n.size + 1) ≤ B n) :
    ∃ T, EmitsIn (G.call src)
      (fun input σ ↦ Pre' input (fun i ↦ σ (i.castAdd G.tapes)) ∧
        Initialized (Fin.castAdd G.tapes) σ)
      (fun _ σ ↦ σ) (fun input σ ↦ W input (fun i ↦ σ ((src i).castAdd G.tapes))) T B := by
  obtain ⟨T, hT⟩ := G.correct B hB
  let sourceReg (i : Fin m) := (src i).castAdd G.tapes
  let targetReg (i : Fin m) := (G.env i).natAdd l
  let copied (σ : Fin (l + G.tapes) → List Bool) :=
    composeFin m (fun i σ ↦ Function.update σ (targetReg i) (σ (sourceReg i))) σ
  have hto : Function.Injective targetReg := (Fin.natAdd_injective G.tapes l).comp G.env_injective
  have hsep (i : Fin G.tapes) (j : Fin l) : i.natAdd l ≠ j.castAdd G.tapes := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_natAdd, Fin.val_castAdd]
    omega
  have hds (i j : Fin m) : targetReg i ≠ sourceReg j := hsep (G.env i) (src j)
  have hcopy (σ : Fin (l + G.tapes) → List Bool) := composeFin_copy targetReg sourceReg hto hds σ
  have hcopied (σ : Fin (l + G.tapes) → List Bool) :
      (fun i ↦ copied σ (targetReg i)) = fun i ↦ σ (sourceReg i) := funext (hcopy σ).1
  have hg := (hT.onTapes (callLayout l G.tapes)).congr
    (F' := fun _ σ ↦ σ) (fun _ σ _ ↦ onTapesVal_self _ σ)
  have hc := copyFamily_transformsIn sourceReg targetReg (fun i ↦ (hds i i).symm) B
  have he := (hc.seqEmitsIn hg).seqTransformsIn (clearFamily_transformsIn targetReg B)
  refine ⟨_, ((he.mono_pre ?_).congr ?_).congr_output ?_⟩
  · intro input σ _ hp
    refine ⟨⟨trivial, ?_⟩, trivial⟩
    change Pre input (fun i ↦ copied σ (targetReg i)) ∧
      Initialized G.env (fun i ↦ copied σ (i.natAdd l))
    refine ⟨?_, ?_⟩
    · rw [hcopied]
      exact hpre input (fun i ↦ σ (i.castAdd G.tapes)) hp.1
    · intro i hi
      exact ((hcopy σ).2 (i.natAdd l)
        (fun j he ↦ hi j (Fin.natAdd_injective G.tapes l he))).trans
        (hp.2 (i.natAdd l) (hsep i))
  · intro input σ hp
    change composeFin m (fun i σ ↦ Function.update σ (targetReg i) []) (copied σ) = σ
    have hclear := composeFin_const targetReg (fun _ ↦ []) hto (copied σ)
    funext i
    by_cases hi : ∃ j, i = targetReg j
    · obtain ⟨j, rfl⟩ := hi
      rw [hclear.1 j]
      exact (hp.2 (targetReg j) (hsep (G.env j))).symm
    · have hn (j) : i ≠ targetReg j := fun he ↦ hi ⟨j, he⟩
      exact (hclear.2 i hn).trans ((hcopy σ).2 i hn)
  · intro input σ _
    change W input (fun i ↦ copied σ (targetReg i)) = _
    rw [hcopied]

/-- Run a generator from selected values in a new protected environment.
The machine copies those values into its fixed private layout on every call. -/
@[expose] def rename {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    {Pre' : List Bool → (Fin l → List Bool) → Prop}
    (hpre : ∀ input σ, Pre' input σ → Pre input (fun i ↦ σ (src i))) :
    Generator l Pre' (fun input σ ↦ W input (fun i ↦ σ (src i))) :=
  ⟨l + G.tapes, StateOf (G.call src),
    { finite := G.call_finite src
      env := Fin.castAdd G.tapes
      env_injective := Fin.castAdd_injective _ _
      program := G.call src
      space := G.space
      correct B hB := G.call_emitsIn src hpre B hB
    }⟩

/-- Two private workspaces share the same caller environment. -/
@[expose] def leftLayout (m k l : ℕ) : Fin (m + (k + l)) ≃ Fin (m + k) ⊕ Fin l :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm) |>.trans
    (Equiv.sumAssoc _ _ _).symm |>.trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))

/-- The second private workspace uses the same caller prefix as the first. -/
@[expose] def rightLayout (m k l : ℕ) : Fin (m + (k + l)) ≃ Fin (m + l) ⊕ Fin k :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))) |>.trans
    (Equiv.sumAssoc _ _ _).symm |>.trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))

/-- The first allocation preserves the caller's register numbers. -/
@[simp] theorem leftLayout_env (m k l : ℕ) (i : Fin m) :
    (leftLayout m k l).symm (.inl (i.castAdd k)) = i.castAdd (k + l) := by
  simp [leftLayout]

/-- The second allocation preserves the same caller register numbers. -/
@[simp] theorem rightLayout_env (m k l : ℕ) (i : Fin m) :
    (rightLayout m k l).symm (.inl (i.castAdd l)) = i.castAdd (k + l) := by
  simp [rightLayout]

/-- Call a generator using the first of two private workspaces. -/
@[expose] def left (G : Generator m Pre W) (l : ℕ) : Generator m Pre W :=
  (G.rename id (fun _ _ h ↦ h)).allocate (leftLayout m G.tapes l)

/-- Call a generator using the second of two private workspaces. -/
@[expose] def right (G : Generator m Pre W) (k : ℕ) : Generator m Pre W :=
  (G.rename id (fun _ _ h ↦ h)).allocate (rightLayout m k G.tapes)

/-- The first call uses the common caller environment. -/
@[simp] theorem left_env (G : Generator m Pre W) (l : ℕ) :
    (G.left l).env = Fin.castAdd (G.tapes + l) := funext (leftLayout_env m G.tapes l)

/-- The second call uses the common caller environment. -/
@[simp] theorem right_env (G : Generator m Pre W) (k : ℕ) :
    (G.right k).env = Fin.castAdd (k + G.tapes) := funext (rightLayout_env m k G.tapes)

/-- The empty word needs no scratch registers. -/
@[expose] def empty (m : ℕ) (Pre : List Bool → (Fin m → List Bool) → Prop) :
    Generator m Pre (fun _ _ ↦ []) :=
  ⟨m, Unit,
    { finite := inferInstance
      env := id
      env_injective := Function.injective_id
      program := emitSymbol none
      space := 0
      correct B _ := ⟨fun _ ↦ 1, (emitSymbol_emitsIn none B).mono_pre
        (fun _ _ _ _ ↦ trivial)⟩
    }⟩

/-- A protected word can be emitted without changing its register. -/
@[expose] def stored (m : ℕ) (Pre : List Bool → (Fin m → List Bool) → Prop) (i : Fin m) :
    Generator m Pre (fun _ σ ↦ σ i) :=
  ⟨m, StateOf (storedGenerator i),
    { finite := inferInstance
      env := id
      env_injective := Function.injective_id
      program := storedGenerator i
      space := 0
      correct B _ := ⟨_, (storedGenerator_emitsIn i B).mono_pre (fun _ _ _ _ ↦ trivial)⟩
    }⟩

/-- Stream the physical input through its restoring digit reader. -/
@[expose] def input : Generator 0 (fun _ _ ↦ True) (fun w _ ↦ w) :=
  ⟨3, StateOf (seq (emitReader (inputAt (0 : Fin 3) 1 2) 0 2) (const [] 0)),
    { finite := inferInstance
      env := Fin.elim0
      env_injective := fun i _ _ ↦ i.elim0
      program := seq (emitReader (inputAt (0 : Fin 3) 1 2) 0 2) (const [] 0)
      space := 1
      correct B hB := by
        have hB1 (n) : 1 ≤ B n := by have := hB n; omega
        have hsize (n) : n.size ≤ B n := by have := hB n; omega
        have hr := inputAt_readsAt (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) B hB1
        have he := emitReader_emitsIn 0 2 (by decide) hr
          (fun _ σ q r hp ↦ by simpa using hp) (fun _ _ _ _ ↦ rfl)
          (N := id) (fun _ _ _ ↦ le_rfl) hsize hB1
        have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (0 : Fin 3) (B n))
          (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
        refine ⟨_, ((he.seqTransformsIn hc).mono_pre ?_).congr ?_⟩
        · intro w σ _ hp
          exact ⟨hp.2 1 (fun j ↦ j.elim0), trivial⟩
        · intro w σ hp
          have hz (i : Fin 3) : σ i = [] := hp.2 i (fun j ↦ j.elim0)
          simp only [Function.update_comm (by decide : (0 : Fin 3) ≠ 2), Function.update_idem]
          funext i
          simp [Function.update_apply, hz]
    }⟩

/-- A finite output transformation preserves a generator's stored environment. -/
@[expose] def mapOutput (G : Generator m Pre W) {A : Type} [Finite A]
    (a : A) (step : A → Bool → A × Option Bool) (finish : A → Option Bool) :
    Generator m Pre (fun input σ ↦ outputWord step finish a (W input σ)) :=
  ⟨G.tapes, StateOf (Machine.mapOutput G.program a step finish),
    { finite := inferInstance
      env := G.env
      env_injective := G.env_injective
      program := Machine.mapOutput G.program a step finish
      space := G.space
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B hB
        exact ⟨fun n ↦ T n + 1, mapOutput_emitsIn hT a step finish⟩
    }⟩

/-- A fixed initial output digit uses no additional work tape. -/
@[expose] def succ (G : Generator m Pre W) (b : Bool) :
    Generator m Pre (fun input σ ↦ b :: W input σ) :=
  ⟨G.tapes, StateOf (seq (emitSymbol (some b)) G.program),
    { finite := by
        let := Fintype.ofFinite G.State
        infer_instance
      env := G.env
      env_injective := G.env_injective
      program := seq (emitSymbol (some b)) G.program
      space := G.space
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B hB
        exact ⟨_, succGenerator_emitsIn hT b⟩
    }⟩

/-- A fixed final output digit uses no additional work tape. -/
@[expose] def appendBit (G : Generator m Pre W) (b : Bool) :
    Generator m Pre (fun input σ ↦ W input σ ++ [b]) :=
  ⟨G.tapes, StateOf (seq G.program (emitSymbol (some b))),
    { finite := by
        let := Fintype.ofFinite G.State
        infer_instance
      env := G.env
      env_injective := G.env_injective
      program := seq G.program (emitSymbol (some b))
      space := G.space
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B hB
        exact ⟨_, (hT.seqEmitsIn (emitSymbol_emitsIn (some b) B)).mono_pre
          (fun _ _ _ hp ↦ ⟨hp, trivial⟩)⟩
    }⟩

/-- Numerical successor changes only finite output control. -/
@[expose] def numericSucc (G : Generator m Pre W) :
    Generator m Pre (fun input σ ↦ Oitavem.numericSucc (W input σ)) :=
  (G.mapOutput true numericSuccStep numericSuccFinish).congr
    (fun input σ _ ↦ outputWord_numericSucc_true (W input σ))

/-- Numerical predecessor changes only finite output control. -/
@[expose] def numericPred (G : Generator m Pre W) :
    Generator m Pre (fun input σ ↦ Oitavem.numericPred (W input σ)) :=
  (G.mapOutput (true, none) numericPredStep numericPredFinish).congr (by
    intro input σ _
    rw [outputWord_numericPred_true]
    cases W input σ <;> rfl)

/-- String predecessor discards the first generated digit. -/
@[expose] def pred (G : Generator m Pre W) :
    Generator m Pre (fun input σ ↦ (W input σ).tail) :=
  (G.mapOutput false predStep (fun _ ↦ none)).congr
    (fun input σ _ ↦ outputWord_pred (W input σ) false)

/-- Last-digit extraction in the word representation emits one fixed-size result. -/
@[expose] def last (G : Generator m Pre W) :
    Generator m Pre (fun input σ ↦ [(W input σ).headD false]) :=
  (G.mapOutput none lastStep (fun first ↦ some (first.getD false))).congr
    (fun input σ _ ↦ outputWord_last (W input σ) none)

/-- Numerical length adds one scratch counter; a bound on its binary size suffices. -/
@[expose] def length (G : Generator m Pre W) (C : ℕ)
    (hsize : ∀ input σ, Pre input σ →
      ((W input σ).length + 1).size ≤ C * (input.length.size + 1)) :
    Generator m Pre (fun input σ ↦ unrank (W input σ).length) :=
  ⟨G.tapes + 1, StateOf (lengthGenerator G.program),
    { finite := by
        let := Fintype.ofFinite G.State
        unfold lengthGenerator generatedLength emitNumberClean
        infer_instance
      env := fun i ↦ (G.env i).succ
      env_injective := (Fin.succ_injective _).comp G.env_injective
      program := lengthGenerator G.program
      space := max G.space C
      correct B hB := by
        obtain ⟨T, hT⟩ := G.correct B (fun n ↦
          (Nat.mul_le_mul_right _ (Nat.le_max_left G.space C)).trans (hB n))
        have h := lengthGenerator_emitsIn hT (fun input σ hp _ ↦
          (hsize input (fun i ↦ σ (G.env i)) hp.1).trans
            ((Nat.mul_le_mul_right _ (Nat.le_max_right G.space C)).trans (hB input.length)))
        refine ⟨_, (h.mono_pre ?_).congr ?_⟩
        · intro input σ _ hp
          exact ⟨hp.1, hp.2.succ⟩
        · intro input σ hp
          funext i
          exact Fin.cases hp.2.zero.symm (fun _ ↦ rfl) i
    }⟩

/-- Concatenate two generated outputs over the same protected environment. -/
@[expose] def append (G : Generator m Pre W)
    {V : List Bool → (Fin m → List Bool) → List Bool} (H : Generator m Pre V) :
    Generator m Pre (fun input σ ↦ W input σ ++ V input σ) :=
  ⟨m + (G.tapes + H.tapes),
    StateOf (seq (G.left H.tapes).program (H.right G.tapes).program),
    { finite := by
        let := Fintype.ofFinite (G.left H.tapes).State
        let := Fintype.ofFinite (H.right G.tapes).State
        infer_instance
      env := Fin.castAdd (G.tapes + H.tapes)
      env_injective := Fin.castAdd_injective _ _
      program := seq (G.left H.tapes).program (H.right G.tapes).program
      space := G.space + H.space
      correct B hB := by
        obtain ⟨TG, hG⟩ := (G.left H.tapes).correct B (fun n ↦
          (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)).trans (hB n))
        obtain ⟨TH, hH⟩ := (H.right G.tapes).correct B (fun n ↦
          (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans (hB n))
        simp only [left_env] at hG
        simp only [right_env] at hH
        exact ⟨_, (hG.seqEmitsIn hH).mono_pre (fun _ _ _ hp ↦ ⟨hp, hp⟩)⟩
    }⟩

/-- String product combines independently compiled arguments over one environment.
Only the repetition count is retained between regenerated copies. -/
@[expose] def product (G : Generator m Pre W)
    {V : List Bool → (Fin m → List Bool) → List Bool} (H : Generator m Pre V)
    (N : ℕ → ℕ) (C : ℕ) (hlen : ∀ input σ, Pre input σ → (V input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n + 1).size ≤ C * (n.size + 1)) :
    Generator m Pre (fun input σ ↦ (List.replicate (V input σ).length (W input σ)).flatten) :=
  ⟨m + (G.tapes + H.tapes) + 1,
    StateOf (productGenerator (G.left H.tapes).program (H.right G.tapes).program),
    { finite := by
        let := Fintype.ofFinite (G.left H.tapes).State
        let := Fintype.ofFinite (H.right G.tapes).State
        unfold productGenerator generatedLength repeatGenerator
        infer_instance
      env := fun i ↦ (i.castAdd (G.tapes + H.tapes)).succ
      env_injective := (Fin.succ_injective _).comp (Fin.castAdd_injective _ _)
      program := productGenerator (G.left H.tapes).program (H.right G.tapes).program
      space := max (max G.space H.space) C
      correct B hB := by
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ ((Nat.le_max_left G.space H.space).trans
            (Nat.le_max_left _ C))).trans (hB n)
        have hH (n) : H.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ ((Nat.le_max_right G.space H.space).trans
            (Nat.le_max_left _ C))).trans (hB n)
        have hC (n) : (N n + 1).size ≤ B n := (hsize n).trans
          ((Nat.mul_le_mul_right _ (Nat.le_max_right (max G.space H.space) C)).trans (hB n))
        obtain ⟨T₁, h₁⟩ := (G.left H.tapes).correct B hG
        obtain ⟨T₂, h₂⟩ := (H.right G.tapes).correct B hH
        simp only [left_env] at h₁
        simp only [right_env] at h₂
        have h := productGenerator_emitsIn h₁ h₂
          (fun input σ hp ↦ hlen input _ hp.1)
          (fun input σ hp _ ↦ (size_le_size (Nat.add_le_add_right (hlen input _ hp.1) 1)).trans
            (hC input.length))
        refine ⟨_, (h.mono_pre ?_).congr ?_⟩
        · intro input σ _ hp
          exact ⟨⟨hp.1, hp.2.succ⟩, ⟨hp.1, hp.2.succ⟩⟩
        · intro input σ hp
          rw [← hp.2.zero]
          exact Function.update_eq_self ..
    }⟩

/-- A generator with no environment yields simultaneous polynomial time and
logarithmic space for its physical-input function. -/
theorem computes {Pre : List Bool → (Fin 0 → List Bool) → Prop}
    {W : List Bool → (Fin 0 → List Bool) → List Bool}
    (G : Generator 0 Pre W) (hpre : ∀ input, Pre input Fin.elim0) :
    ∃ C d : ℕ, ComputesFunInTimeAndSpace (seq inBack G.program) (.refl _) (.refl _)
      (fun input ↦ W input Fin.elim0)
      (fun input ↦ C * (input.length + 1) ^ d)
      (fun input ↦ C * (input.length.size + 1)) := by
  obtain ⟨T, hT⟩ := G.correct (fun n ↦ G.space * (n.size + 1)) (fun _ ↦ le_rfl)
  have he : (fun _ : Fin 0 ↦ ([] : List Bool)) = Fin.elim0 := by funext i; exact i.elim0
  simpa only [he] using hT.computes_polytime_logspace
    (fun input ↦ ⟨by simpa only [he] using hpre input, fun _ _ ↦ rfl⟩)
    G.space (fun _ ↦ le_rfl)

end Generator

end

end Geb.Oitavem.Machine
