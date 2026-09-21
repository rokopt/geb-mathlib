/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer

set_option doc.verso true in
/-!
# Generated readers over a caller environment

Length and digit readers import their arguments through a generator's existing
call interface. They copy the answer to a caller register and clear their
temporary result before returning. Caller registers may alias the selected
arguments: the answer depends on their values on entry.

## Main definitions

* {lit}`copyClear` exports a result and clears its temporary register.
* {lit}`Generator.lengthCall` computes a generated word's binary length.
* {lit}`Generator.atCall` computes a digit at a saved binary index.

## Main statements

* {lit}`Generator.lengthCall_readsLength` verifies the length adapter.
* {lit}`Generator.atCall_readsAtAll` verifies every canonical digit query.

## Implementation notes

These are adapters for the existing generator and reader contracts. They use
fixed executable tape layouts and inherit the contracts' {lit}`Classical.choice`
dependency from CSLib.

## Tags

Turing machine, logarithmic space, generator, length, digit reader
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Export a temporary register and clear it for the next call. -/
@[expose] def copyClear {k : ℕ} (sourceReg targetReg : Fin k) :=
  seq (copy sourceReg targetReg) (const [] sourceReg)

/-- Exporting an answer preserves every other register. -/
theorem copyClear_transformsIn {k : ℕ} (sourceReg targetReg : Fin k)
    (hne : sourceReg ≠ targetReg) (B : ℕ → ℕ) :
    TransformsIn (copyClear sourceReg targetReg) (fun _ _ ↦ True)
      (fun _ σ ↦ Function.update (Function.update σ targetReg (σ sourceReg)) sourceReg [])
      (fun n ↦ (5 * B n + 12) + (4 * B n + 9)) B := by
  have hc := Transforms.toIn_of (fun n ↦ copy_transforms sourceReg targetReg hne (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB sourceReg))
  have he := Transforms.toIn_of (fun n ↦ const_transforms [] sourceReg (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  exact (hc.seq he).mono_pre (fun _ _ _ _ ↦ ⟨trivial, trivial⟩)

/-- Writing a temporary answer, exporting it, and clearing the initially blank
temporary register leaves only the exported answer. -/
theorem update_copyClear {k : ℕ} (σ : Fin k → List Bool) (sourceReg targetReg : Fin k)
    (hne : sourceReg ≠ targetReg) (hz : σ sourceReg = []) (w : List Bool) :
    Function.update (Function.update (Function.update σ sourceReg w) targetReg w) sourceReg [] =
      Function.update σ targetReg w := by
  rw [Function.update_comm hne, Function.update_idem,
    Function.update_comm hne.symm, ← hz, Function.update_eq_self]

/-- Allocate a length reader while keeping the same caller prefix. -/
theorem ReadsLength.onEnvironment {m k l a : ℕ} {S : Type}
    {P : MultiTapeTM (m + k) Bool S} {R : Fin m}
    {Pre : List Bool → (Fin m → List Bool) → Prop}
    {W : List Bool → (Fin m → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : ReadsLength P (R.castAdd k)
      (fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd k)) ∧ Initialized (Fin.castAdd k) σ)
      (fun input σ ↦ W input (fun i ↦ σ (i.castAdd k))) T B)
    (e : Fin (m + l) ≃ Fin (m + k) ⊕ Fin a)
    (he : ∀ i : Fin m, e.symm (.inl (i.castAdd k)) = i.castAdd l) :
    ReadsLength (Machine.onTapes P e) (R.castAdd l)
      (fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd l)) ∧ Initialized (Fin.castAdd l) σ)
      (fun input σ ↦ W input (fun i ↦ σ (i.castAdd l))) T B := by
  have h := hP.onTapes e
  simp only [he] at h
  refine h.mono_pre ?_
  intro input σ _ hp
  refine ⟨hp.1, Initialized.onTapes e ?_⟩
  simpa only [he] using hp.2

/-- Allocate an all-index digit reader while keeping the same caller prefix. -/
theorem ReadsAtAll.onEnvironment {m k l a : ℕ} {S : Type}
    {P : MultiTapeTM (m + k) Bool S} {Q R : Fin m}
    {Pre : List Bool → (Fin m → List Bool) → Prop}
    {W : List Bool → (Fin m → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : ReadsAtAll P (Q.castAdd k) (R.castAdd k)
      (fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd k)) ∧ Initialized (Fin.castAdd k) σ)
      (fun input σ ↦ W input (fun i ↦ σ (i.castAdd k))) T B)
    (e : Fin (m + l) ≃ Fin (m + k) ⊕ Fin a)
    (he : ∀ i : Fin m, e.symm (.inl (i.castAdd k)) = i.castAdd l) :
    ReadsAtAll (Machine.onTapes P e) (Q.castAdd l) (R.castAdd l)
      (fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd l)) ∧ Initialized (Fin.castAdd l) σ)
      (fun input σ ↦ W input (fun i ↦ σ (i.castAdd l))) T B := by
  have h := hP.onTapes e
  simp only [he] at h
  refine h.mono_pre ?_
  intro input σ _ hp
  refine ⟨⟨hp.1.1, Initialized.onTapes e ?_⟩, hp.2⟩
  simpa only [he] using hp.1.2

namespace Generator

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {W : List Bool → (Fin m → List Bool) → List Bool}

/-- Count a called generator and export its binary length to a caller register. -/
@[expose] def lengthCall {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) (R : Fin l) :=
  seq (generatedLength (G.call src)) (copyClear 0 (R.castAdd G.tapes).succ)

/-- The length adapter has finite control. -/
theorem lengthCall_finite {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) (R : Fin l) :
    Finite (StateOf (G.lengthCall src R)) := by
  let := G.call_finite src
  let := Fintype.ofFinite (StateOf (G.call src))
  unfold lengthCall generatedLength copyClear
  infer_instance

/-- A generated length is returned to the caller, with all private registers cleared. -/
theorem lengthCall_readsLength {l : ℕ} (G : Generator m Pre W)
    (src : Fin m → Fin l) (R : Fin l) (B : ℕ → ℕ)
    (hB : ∀ n, G.space * (n.size + 1) ≤ B n)
    (hsize : ∀ input σ, Pre input σ →
      ((W input σ).length + 1).size ≤ B input.length) :
    ∃ T, ReadsLength (G.lengthCall src R) (R.castAdd G.tapes).succ
      (fun input σ ↦ Pre input (fun i ↦ σ ((src i).castAdd G.tapes).succ) ∧
        Initialized (fun i : Fin l ↦ (i.castAdd G.tapes).succ) σ)
      (fun input σ ↦ W input (fun i ↦ σ ((src i).castAdd G.tapes).succ)) T B := by
  obtain ⟨T, hT⟩ := G.call_emitsIn src (fun _ _ h ↦ h) B hB
  have hr := generatedLength_readsLength hT (fun input σ hp _ ↦ hsize input _ hp.1)
  have hc := copyClear_transformsIn (0 : Fin (l + G.tapes + 1))
    (R.castAdd G.tapes).succ (Fin.succ_ne_zero _).symm B
  refine ⟨_, ((hr.seq hc).mono_pre ?_).congr ?_⟩
  · intro input σ _ hp
    exact ⟨⟨hp.1, hp.2.succ⟩, trivial⟩
  · intro input σ hp
    simp only [Function.update_self]
    exact update_copyClear σ 0 _ (Fin.succ_ne_zero _).symm hp.2.zero _

/-- Read a called generator at the caller's saved query and export its result. -/
@[expose] def atCall {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) (Q R : Fin l) :=
  seq (generatedAt (G.call src) (Q.castAdd G.tapes))
    (copyClear resultTape (oldTape (R.castAdd G.tapes)))

/-- The digit adapter has finite control. -/
theorem atCall_finite {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l) (Q R : Fin l) :
    Finite (StateOf (G.atCall src Q R)) := by
  let := G.call_finite src
  let := Fintype.ofFinite (StateOf (G.call src))
  unfold atCall generatedAt copyClear
  infer_instance

/-- A generated digit is returned to the caller for every canonical query,
including indices beyond the generated word's end. -/
theorem atCall_readsAtAll {l : ℕ} (G : Generator m Pre W)
    (src : Fin m → Fin l) (Q R : Fin l) (B : ℕ → ℕ)
    (hB : ∀ n, G.space * (n.size + 1) ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    ∃ T, ReadsAtAll (G.atCall src Q R) (oldTape (Q.castAdd G.tapes))
      (oldTape (R.castAdd G.tapes))
      (fun input σ ↦ Pre input (fun i ↦ σ (oldTape ((src i).castAdd G.tapes))) ∧
        Initialized (fun i : Fin l ↦ oldTape (i.castAdd G.tapes)) σ)
      (fun input σ ↦ W input (fun i ↦ σ (oldTape ((src i).castAdd G.tapes)))) T B := by
  obtain ⟨T, hT⟩ := G.call_emitsIn src (fun _ _ h ↦ h) B hB
  have hr := generatedAt_all_queries hT (Q.castAdd G.tapes) hB1
  have hc := copyClear_transformsIn resultTape (oldTape (R.castAdd G.tapes))
    (oldTape_ne_resultTape _).symm B
  refine ⟨_, ((hr.seq hc).mono_pre ?_).congr ?_⟩
  · intro input σ _ hp
    exact ⟨⟨⟨hp.1.2.zero, hp.1.1, hp.1.2.succ.succ⟩, hp.2⟩, trivial⟩
  · intro input σ hp
    simp only [Function.update_self]
    exact update_copyClear σ resultTape _ (oldTape_ne_resultTape _).symm hp.1.2.succ.zero _

/-- Pad a private workspace, preserving the common caller prefix. -/
@[expose] def padLayout (m k K : ℕ) (hk : k ≤ K) :
    Fin (m + K) ≃ Fin (m + k) ⊕ Fin (K - k) :=
  (finCongr (by omega : m + K = m + (k + (K - k)))).trans (leftLayout m k (K - k))

/-- Padding a private workspace leaves every caller register in place. -/
@[simp] theorem padLayout_env (m k K : ℕ) (hk : k ≤ K) (i : Fin m) :
    (padLayout m k K hk).symm (.inl (i.castAdd k)) = i.castAdd K := by
  apply Fin.ext
  simp [padLayout]

/-- Call a generator in a padded private workspace after a common caller prefix. -/
@[expose] def pad (G : Generator m Pre W) (K : ℕ) (hK : G.tapes ≤ K) : Generator m Pre W :=
  (G.rename id (fun _ _ hp ↦ hp)).allocate (padLayout m G.tapes K hK)

/-- Padding aligns a generator with the common caller environment. -/
@[simp] theorem pad_env (G : Generator m Pre W) (K : ℕ) (hK : G.tapes ≤ K) :
    (G.pad K hK).env = Fin.castAdd K := funext (padLayout_env m G.tapes K hK)

/-- Place a length call's extra counter after its caller and private registers. -/
@[expose] def lengthLayout (m k : ℕ) : Fin (m + (k + 1)) ≃ Fin (m + k + 1) ⊕ Fin 0 :=
  (leftLayout m k 1).trans (reserveTape (m + k)).symm |>.trans (Equiv.sumEmpty _ _).symm

/-- Length-reader allocation preserves the caller's register numbers. -/
@[simp] theorem lengthLayout_env (m k : ℕ) (i : Fin m) :
    (lengthLayout m k).symm (.inl (i.castAdd k).succ) = i.castAdd (k + 1) :=
  leftLayout_env m k 1 i

/-- Reserve the first two tapes, leaving the old tapes in their original order. -/
@[expose] def reserveTwo (k : ℕ) : Fin (k + 2) ≃ Fin k ⊕ Fin 2 where
  toFun := Fin.cases (.inr 0) (Fin.cases (.inr 1) .inl)
  invFun := Sum.elim oldTape (Fin.cases 0 (Fin.cases 1 Fin.elim0))
  left_inv := Fin.cases rfl (Fin.cases rfl (fun _ ↦ rfl))
  right_inv := Sum.rec (fun _ ↦ rfl) (Fin.cases rfl (Fin.cases rfl (fun i ↦ i.elim0)))

/-- Place a digit call's two temporary tapes after its private registers. -/
@[expose] def atLayout (m k : ℕ) : Fin (m + (k + 2)) ≃ Fin (m + k + 2) ⊕ Fin 0 :=
  (leftLayout m k 2).trans (reserveTwo (m + k)).symm |>.trans (Equiv.sumEmpty _ _).symm

/-- Digit-reader allocation preserves the caller's register numbers. -/
@[simp] theorem atLayout_env (m k : ℕ) (i : Fin m) :
    (atLayout m k).symm (.inl (oldTape (i.castAdd k))) = i.castAdd (k + 2) :=
  leftLayout_env m k 2 i

/-- A generated length reader whose caller registers form a common initial segment. -/
@[expose] def lengthReader {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    (R : Fin l) := onTapes (G.lengthCall src R) (lengthLayout l G.tapes)

/-- A generated digit reader whose caller registers form a common initial segment. -/
@[expose] def atReader {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    (Q R : Fin l) := onTapes (G.atCall src Q R) (atLayout l G.tapes)

/-- Length-reader allocation retains finite control. -/
theorem lengthReader_finite {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    (R : Fin l) : Finite (StateOf (G.lengthReader src R)) := G.lengthCall_finite src R

/-- Digit-reader allocation retains finite control. -/
theorem atReader_finite {l : ℕ} (G : Generator m Pre W) (src : Fin m → Fin l)
    (Q R : Fin l) : Finite (StateOf (G.atReader src Q R)) := G.atCall_finite src Q R

/-- The allocated length reader changes only its designated caller result register. -/
theorem lengthReader_readsLength {l : ℕ} (G : Generator m Pre W)
    (src : Fin m → Fin l) (R : Fin l) (B : ℕ → ℕ)
    (hB : ∀ n, G.space * (n.size + 1) ≤ B n)
    (hsize : ∀ input σ, Pre input σ →
      ((W input σ).length + 1).size ≤ B input.length) :
    ∃ T, ReadsLength (G.lengthReader src R) (R.castAdd (G.tapes + 1))
      (fun input σ ↦ Pre input (fun i ↦ σ ((src i).castAdd (G.tapes + 1))) ∧
        Initialized (Fin.castAdd (G.tapes + 1) : Fin l → _) σ)
      (fun input σ ↦ W input (fun i ↦ σ ((src i).castAdd (G.tapes + 1)))) T B := by
  obtain ⟨T, hT⟩ := G.lengthCall_readsLength src R B hB hsize
  have h := hT.onTapes (lengthLayout l G.tapes)
  simp only [lengthLayout_env] at h
  refine ⟨T, h.mono_pre ?_⟩
  intro input σ _ hp
  refine ⟨hp.1, Initialized.onTapes (lengthLayout l G.tapes) ?_⟩
  simpa only [lengthLayout_env] using hp.2

/-- The allocated digit reader accepts every canonical index and changes only its result. -/
theorem atReader_readsAtAll {l : ℕ} (G : Generator m Pre W)
    (src : Fin m → Fin l) (Q R : Fin l) (B : ℕ → ℕ)
    (hB : ∀ n, G.space * (n.size + 1) ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    ∃ T, ReadsAtAll (G.atReader src Q R) (Q.castAdd (G.tapes + 2))
      (R.castAdd (G.tapes + 2))
      (fun input σ ↦ Pre input (fun i ↦ σ ((src i).castAdd (G.tapes + 2))) ∧
        Initialized (Fin.castAdd (G.tapes + 2) : Fin l → _) σ)
      (fun input σ ↦ W input (fun i ↦ σ ((src i).castAdd (G.tapes + 2)))) T B := by
  obtain ⟨T, hT⟩ := G.atCall_readsAtAll src Q R B hB hB1
  have h := hT.onTapes (atLayout l G.tapes)
  simp only [atLayout_env] at h
  refine ⟨T, h.mono_pre ?_⟩
  intro input σ _ hp
  refine ⟨⟨hp.1.1, Initialized.onTapes (atLayout l G.tapes) ?_⟩, hp.2⟩
  simpa only [atLayout_env] using hp.1.2

end Generator

end

end Geb.Oitavem.Machine
