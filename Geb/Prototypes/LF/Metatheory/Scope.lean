/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Weakening
public import Mathlib.Data.List.Infix
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Scoping

An expression judged in a context has its free variables among the context's: its renaming
depends only on the renaming's values below the context's length ({lit}`judgeWith_scoped`). In
particular the kind or type of each constant of a formed signature, judged in the empty context,
is closed ({lit}`Sig.ok_closed`), which discharges the hypothesis of weakening
({name}`Geb.LF.judge_rename`). An expression is in scope in a context when it is so, a property
stated by its renamings rather than by a fold of its own ({lit}`ScopedBelow`).

The proof is by induction on the expression, through the inversion of the judgments at a node
({lit}`judgeWith_node_inv`): a judged node's head variable, where it has one, is in the context,
and each child is judged in the context extended by as many types as the node binds over it.

## Main definitions

* {lit}`ScopedBelow` — an expression's renaming depends only on the variables below a bound.

## Main statements

* {lit}`spine_args` — the arguments of a spine that instantiates are checked.
* {lit}`judgeWith_node_inv` — the inversion of the judgments at a node.
* {lit}`judgeWith_scoped` — a judged expression is in the scope of its context.
* {lit}`Sig.ok_closed` — the declarations of a formed signature are closed.

## Tags

logical framework, LF, scoping, closed term
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- An expression's renaming depends only on the renaming's values below {lit}`k`: its free
variables are below {lit}`k`. -/
def ScopedBelow (k : ℕ) (e : Expr) : Prop :=
  ∀ ρ σ : ℕ → ℕ, (∀ i < k, ρ i = σ i) → e.rename ρ = e.rename σ

/-- Renamings that agree below {lit}`k` agree, lifted under {lit}`b` binders, below
{lit}`k + b`. -/
theorem iterate_liftR_agree {k : ℕ} {ρ σ : ℕ → ℕ} (h : ∀ i < k, ρ i = σ i) (b : ℕ) :
    ∀ i < k + b, liftR^[b] ρ i = liftR^[b] σ i := by
  intro i hi
  rw [iterate_liftR_apply, iterate_liftR_apply]
  split_ifs with hib
  · rfl
  · rw [h (i - b) (by omega)]

/-- The arguments of a spine along which a classifier instantiates are each checked against a
type. -/
theorem spine_args {J : Expr → Ctx → Mode → Bool} {Γ : Ctx} :
    ∀ (ms : List Expr) (c r : Expr), spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, J m Γ (.check a) = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr),
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r → ∀ m ∈ ms, ∃ a, J m Γ (.check a) = true)
    (fun _ _ _ m hm ↦ absurd hm List.not_mem_nil)
    (fun m ms ih c r h m' hm' ↦ by
      simp only [spine, List.map_cons, List.foldlM_cons] at h
      obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l, cs, rfl⟩ := exists_node c
      rw [RoseTree.label_node, RoseTree.children_node] at hc'
      rcases l with _ | _ | _ | _
      · simp at hc'
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp at hc'
        · simp at hc'
        · simp only at hc'
          split_ifs at hc' with hJ
          rcases List.mem_cons.mp hm' with rfl | hm'
          · exact ⟨a, hJ⟩
          · exact ih c' r hr m' hm'
        · simp at hc'
      · simp at hc'
      · simp at hc')

/-- The inversion of the judgments at a node: a judged node's head variable, where it has one,
is in the context, and each child is judged in a context extended by as many types as the node
binds over it. -/
theorem judgeWith_node_inv {eqv : Expr → Expr → Bool} {sig : Sig} {l : Label} {cs : List Expr}
    {Γ : Ctx} {md : Mode} (h : judgeWith eqv sig (RoseTree.node l cs) Γ md = true) :
    (∀ i, l = .app (.var i) → i < Γ.length) ∧
      ∀ (k : ℕ) (hk : k < cs.length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + l.binders k ∧ judgeWith eqv sig cs[k] Γ' md' = true := by
  rw [judgeWith_node] at h
  have hpi : ∀ {a b : Expr} {ma mb : Mode} {Γb : Ctx}, Γb.length = Γ.length + 1 →
      judgeWith eqv sig a Γ ma = true → judgeWith eqv sig b Γb mb = true →
      ∀ (k : ℕ) (hk : k < [a, b].length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + Label.pi.binders k ∧ judgeWith eqv sig [a, b][k] Γ' md' = true := by
    intro a b ma mb Γb hΓb ha hb k hk
    rcases k with _ | _ | k
    · exact ⟨Γ, ma, rfl, ha⟩
    · exact ⟨Γb, mb, hΓb, hb⟩
    · exact absurd hk (by simp)
  have hargs : ∀ {hd : Head} {c r : Expr},
      spine Γ c (cs.map fun c ↦ (c, judgeWith eqv sig c)) = some r →
      ∀ (k : ℕ) (hk : k < cs.length), ∃ (Γ' : Ctx) (md' : Mode),
        Γ'.length = Γ.length + (Label.app hd).binders k ∧ judgeWith eqv sig cs[k] Γ' md' = true :=
    fun hs k hk ↦ by
      obtain ⟨a, ha⟩ := spine_args cs _ _ hs cs[k] (List.getElem_mem hk)
      exact ⟨Γ, .check a, rfl, ha⟩
  rcases md with _ | _ | p
  · rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · exact ⟨fun i h ↦ (by cases h), fun k hk ↦ absurd hk (by simp)⟩
      · simp [judgeStep] at h
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at h
        exact ⟨fun i h ↦ (by cases h), hpi (Γb := a :: Γ) rfl h.1 h.2⟩
      · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp [judgeStep] at h
  · rcases l with _ | _ | _ | (i | c)
    · simp [judgeStep] at h
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [judgeStep] at h
      · simp [judgeStep] at h
      · simp only [judgeStep, List.map_cons, List.map_nil, Bool.and_eq_true] at h
        exact ⟨fun i h ↦ (by cases h), hpi (Γb := a :: Γ) rfl h.1 h.2⟩
      · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp [judgeStep] at h
    · simp only [judgeStep, beq_iff_eq, Option.bind_eq_some_iff] at h
      obtain ⟨k, -, hs⟩ := h
      exact ⟨fun i h ↦ (by cases h), hargs hs⟩
  · rcases l with _ | _ | _ | hd
    · simp [judgeStep] at h
    · simp [judgeStep] at h
    · rcases cs with _ | ⟨m, _ | ⟨d, cs⟩⟩
      · simp [judgeStep] at h
      · obtain ⟨pl, pcs, rfl⟩ := exists_node p
        simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
          RoseTree.children_node] at h
        rcases pl with _ | _ | _ | _
        · simp at h
        · rcases pcs with _ | ⟨a, _ | ⟨b, _ | ⟨d', pcs⟩⟩⟩
          · simp at h
          · simp at h
          · refine ⟨fun i h ↦ (by cases h), fun k hk ↦ ?_⟩
            rcases k with _ | k
            · exact ⟨a :: Γ, .check b, rfl, h⟩
            · simp at hk
          · simp at h
        · simp at h
        · simp at h
      · simp [judgeStep] at h
    · simp only [judgeStep, Bool.and_eq_true] at h
      obtain ⟨-, hm⟩ := h
      rcases hC : classOf sig Γ hd with _ | C
      · rw [hC] at hm
        simp at hm
      · rw [hC, Option.bind_some] at hm
        rcases hS : spine Γ C (cs.map fun c ↦ (c, judgeWith eqv sig c)) with _ | A
        · rw [hS] at hm
          simp at hm
        · refine ⟨fun i hi ↦ ?_, hargs hS⟩
          cases hi
          simp only [classOf, Option.map_eq_some_iff] at hC
          obtain ⟨a, ha, -⟩ := hC
          exact (List.getElem?_eq_some_iff.mp ha).1

/-- A judged expression is in the scope of its context. -/
theorem judgeWith_scoped {eqv : Expr → Expr → Bool} {sig : Sig} :
    ∀ (e : Expr) (Γ : Ctx) (md : Mode), judgeWith eqv sig e Γ md = true →
      ScopedBelow Γ.length e :=
  RoseTree.ind fun l cs ih Γ md h ρ σ hρσ ↦ by
    obtain ⟨hvar, hch⟩ := judgeWith_node_inv h
    rw [rename_node, rename_node]
    congr 1
    · rcases l with _ | _ | _ | (i | c)
      · rfl
      · rfl
      · rfl
      · simp only [Label.rename, Head.rename, hρσ i (hvar i rfl)]
      · rfl
    · refine List.ext_getElem (by simp) fun k h₁ h₂ ↦ ?_
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
      obtain ⟨Γ', md', hlen, hj⟩ := hch k (by simpa using h₁)
      exact ih _ (List.getElem_mem _) Γ' md' hj _ _ (by
        rw [hlen]
        exact iterate_liftR_agree hρσ _)

/-- An expression in scope below zero is closed: renaming leaves it in place. -/
theorem ScopedBelow.rename_eq {e : Expr} (h : ScopedBelow 0 e) (ρ : ℕ → ℕ) : e.rename ρ = e :=
  (h ρ id fun i hi ↦ absurd hi (Nat.not_lt_zero i)).trans (rename_id e)

/-- The declarations of a formed signature are closed. -/
theorem Sig.ok_closed {sig : Sig} (h : sig.ok = true) : SigClosed sig := by
  intro c a hc ρ
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  rw [Sig.ok, List.all_eq_true] at h
  have hmem : (sig[c], sig.take c) ∈ sig.zip sig.inits := by
    rw [List.mem_iff_getElem]
    refine ⟨c, by simp [List.length_inits]; omega, ?_⟩
    simp [List.getElem_inits]
  have hd := h _ hmem
  simp only [Bool.or_eq_true, IsKind, IsType] at hd
  rcases hd with hd | hd
  · exact ScopedBelow.rename_eq (judgeWith_scoped _ [] _ hd) ρ
  · exact ScopedBelow.rename_eq (judgeWith_scoped _ [] _ hd) ρ

end Geb.LF

end
