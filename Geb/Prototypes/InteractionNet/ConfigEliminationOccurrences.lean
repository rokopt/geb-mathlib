/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigSubstitutionGraph
public import Geb.Prototypes.InteractionNet.ConfigHeadOccurrences
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Leaf occurrences retained by wire elimination

Eliminating a name with one occurrence in the remaining configuration replaces that leaf
by the replacement term's leaves. Every other leaf keeps its individual position and name.
The occurrence bijection distinguishes repeated names, so it can transport the named wire
matching without identifying its separate endpoints.

## Main definitions

* {lit}`Config.substLeavesEquiv` — substitution leaves indexed by their original occurrence.
* {lit}`Config.eliminationLeavesEquiv` — replacement leaves and all unaffected occurrences.

## Main statements

* {lit}`Config.eliminationLeavesEquiv_name` — the occurrence bijection preserves wire names.
* {lit}`Config.eliminationLeaf_matching` — elimination deletes precisely the selected named wire.

## Tags

interaction net, compiler, wire, elimination, substitution, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Substitution leaves retain the original occurrence and their replacement's leaf position. -/
def substLeavesEquiv (σ : ℕ → Term arity ℕ) (c : Config arity) :
    (c.subst σ).GraphLeaf ≃ (Σ p : c.GraphLeaf, (σ (c.graphLeafName p)).fragment.Leaf) :=
  (c.substForestLeaves σ).trans (Equiv.sigmaAssoc
    (fun i (p : (c.graphFragments i).Leaf) ↦
      (σ ((c.graphFragments i).name p)).fragment.Leaf)).symm

/-- The occurrence-indexed replacement leaf has the same name as the substituted syntax leaf. -/
theorem substLeavesEquiv_name (σ : ℕ → Term arity ℕ) (c : Config arity)
    (p : (c.subst σ).GraphLeaf) :
    (σ (c.graphLeafName (c.substLeavesEquiv σ p).1)).fragment.name
      (c.substLeavesEquiv σ p).2 = (c.subst σ).graphLeafName p :=
  c.substForestLeaves_name σ p

/-- Separate the inserted term's leaves from the unchanged variable occurrences. -/
def eliminationReplacementLeavesEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (Σ q : c.GraphLeaf,
      (if c.graphLeafName q = x then t else Term.var (c.graphLeafName q)).fragment.Leaf) ≃
        t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x} where
  toFun q := if h : c.graphLeafName q.1 = x then
    .inl (Term.fragmentLeafEquiv (ite_eq_left h) q.2) else .inr ⟨q.1, h⟩
  invFun q := match q with
    | .inl q => ⟨p, (Term.fragmentLeafEquiv (ite_eq_left hp)).symm q⟩
    | .inr ⟨q, hq⟩ => ⟨q, (Term.fragmentLeafEquiv (ite_eq_right hq)).symm
        (Term.fragmentVarLeaf (c.graphLeafName q))⟩
  left_inv q := by
    rcases q with ⟨q, v⟩
    dsimp only
    by_cases hq : c.graphLeafName q = x
    · have he := unique q hq
      subst q
      rw [dite_eq_left hp]
      exact congrArg (Sigma.mk p) ((Term.fragmentLeafEquiv (ite_eq_left hp)).symm_apply_apply v)
    · rw [dite_eq_right hq]
      apply congrArg (Sigma.mk q)
      apply (Term.fragmentLeafEquiv (ite_eq_right hq)).injective
      exact ((Term.fragmentLeafEquiv (ite_eq_right hq)).apply_symm_apply _).trans
        (Term.fragmentVarLeaf_unique _ _).symm
  right_inv q := by
    cases q with
    | inl q =>
      dsimp only
      rw [dite_eq_left hp]
      exact congrArg Sum.inl ((Term.fragmentLeafEquiv (ite_eq_left hp)).apply_symm_apply q)
    | inr q =>
      dsimp only
      rw [dite_eq_right q.property]

/-- Separating the replacement leaves preserves the name written at every occurrence. -/
theorem eliminationReplacementLeavesEquiv_name (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : Σ q : c.GraphLeaf,
      (if c.graphLeafName q = x then t else Term.var (c.graphLeafName q)).fragment.Leaf) :
    Sum.elim t.fragment.name (fun q ↦ c.graphLeafName q.val)
      (c.eliminationReplacementLeavesEquiv x t p hp unique q) =
        (if c.graphLeafName q.1 = x then t else Term.var (c.graphLeafName q.1)).fragment.name
          q.2 := by
  rcases q with ⟨q, v⟩
  change Sum.elim t.fragment.name
    (fun q : {q : c.GraphLeaf // c.graphLeafName q ≠ x} ↦ c.graphLeafName q.val)
      (if h : c.graphLeafName q = x then
        Sum.inl (Term.fragmentLeafEquiv (ite_eq_left h) v) else Sum.inr ⟨q, h⟩) = _
  by_cases hq : c.graphLeafName q = x
  · rw [dite_eq_left hq]
    exact Term.fragment_name_cast (ite_eq_left hq) v
  · rw [dite_eq_right hq]
    exact Term.fragment_name_cast (ite_eq_right hq) v

/-- Elimination leaves consist of one copy of the replacement and every unaffected occurrence. -/
def eliminationLeavesEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf ≃
      t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x} :=
  (c.substLeavesEquiv (fun y ↦ if y = x then t else Term.var y)).trans
    (c.eliminationReplacementLeavesEquiv x t p hp unique)

/-- The complete elimination occurrence correspondence preserves every wire name. -/
theorem eliminationLeavesEquiv_name (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf) :
    Sum.elim t.fragment.name (fun q ↦ c.graphLeafName q.val)
      (c.eliminationLeavesEquiv x t p hp unique q) =
        (c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafName q :=
  (c.eliminationReplacementLeavesEquiv_name x t p hp unique _).trans
    (c.substLeavesEquiv_name _ q)

/-- Locate each surviving leaf in the original configuration containing the wire equation. -/
def eliminationLeafEmbedding (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf ↪
      ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).GraphLeaf :=
  (c.eliminationLeavesEquiv x t p hp unique).toEmbedding.trans
    ((Function.Embedding.sumMap (.refl _) (.subtype _)).trans
      (Function.Embedding.inr.trans (c.headLeafEquiv (Term.var x, t)).toEmbedding))

/-- The source occurrence of a surviving leaf has exactly its resulting name. -/
theorem eliminationLeafEmbedding_name (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf) :
    ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).graphLeafName
      (c.eliminationLeafEmbedding x t p hp unique q) =
        (c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafName q := by
  have h := c.headLeafEquiv_name (Term.var x, t)
    (.inr ((Function.Embedding.sumMap (.refl _) (.subtype _))
      (c.eliminationLeavesEquiv x t p hp unique q)))
  apply h.trans
  have hn := c.eliminationLeavesEquiv_name x t p hp unique q
  cases he : c.eliminationLeavesEquiv x t p hp unique q with
  | inl q => rw [he] at hn; exact hn
  | inr q => rw [he] at hn; exact hn

/-- Wire elimination preserves every matching edge between its surviving named occurrences. -/
theorem eliminationLeafEmbedding_wiring (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    Wiring.Respects (c.eliminationLeafEmbedding x t p hp unique)
      ((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed)
      (({ c with equations := (Term.var x, t) :: c.equations } :
        Config arity).graphLeafWiring sourceClosed) := by
  apply graphLeafWiring_respects _ _ targetClosed sourceClosed
  intro q r h
  rw [c.eliminationLeafEmbedding_name x t p hp unique,
    c.eliminationLeafEmbedding_name x t p hp unique]
  exact h

/-- Delete the variable head and its unique occurrence from the separated source leaves. -/
def retainedHeadLeavesEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    t.fragment.Leaf ⊕ {q : c.GraphLeaf // c.graphLeafName q ≠ x} ≃
      {q : (Term.var (arity := arity) x).fragment.Leaf ⊕ (t.fragment.Leaf ⊕ c.GraphLeaf) //
        q ≠ .inl (Term.fragmentVarLeaf x) ∧ q ≠ .inr (.inr p)} where
  toFun q := match q with
    | .inl q => ⟨.inr (.inl q), by constructor <;> intro h <;> cases h⟩
    | .inr ⟨q, hq⟩ => ⟨.inr (.inr q), by
        constructor
        · intro h; cases h
        · intro h
          exact hq ((congrArg c.graphLeafName (Sum.inr.inj (Sum.inr.inj h))).trans hp)⟩
  invFun q := match q with
    | ⟨.inl q, h⟩ => (h.1 (congrArg Sum.inl (Term.fragmentVarLeaf_unique x q))).elim
    | ⟨.inr (.inl q), _⟩ => .inl q
    | ⟨.inr (.inr q), h⟩ => .inr ⟨q, fun hq ↦
        h.2 (congrArg Sum.inr (congrArg Sum.inr (unique q hq)))⟩
  left_inv q := by cases q <;> rfl
  right_inv q := by
    rcases q with ⟨q | (q | q), h⟩
    · exact (h.1 (congrArg Sum.inl (Term.fragmentVarLeaf_unique x q))).elim
    · rfl
    · rfl

/-- The target leaves are exactly the source leaves other than the eliminated name's two ends. -/
def eliminationLeafComplementEquiv (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p) :
    (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf ≃
      {q : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).GraphLeaf //
        q ≠ c.headLeafEquiv (Term.var x, t) (.inl (Term.fragmentVarLeaf x)) ∧
        q ≠ c.headLeafEquiv (Term.var x, t) (.inr (.inr p))} :=
  (c.eliminationLeavesEquiv x t p hp unique).trans
    ((c.retainedHeadLeavesEquiv x t p hp unique).trans
      ((c.headLeafEquiv (Term.var x, t)).subtypeEquiv (fun _ ↦ by
        constructor
        · rintro ⟨ha, hb⟩
          exact ⟨fun h ↦ ha ((c.headLeafEquiv (Term.var x, t)).injective h),
            fun h ↦ hb ((c.headLeafEquiv (Term.var x, t)).injective h)⟩
        · rintro ⟨ha, hb⟩
          exact ⟨fun h ↦ ha (congrArg (c.headLeafEquiv (Term.var x, t)) h),
            fun h ↦ hb (congrArg (c.headLeafEquiv (Term.var x, t)) h)⟩)))

/-- The complement bijection has exactly the previously specified source occurrence embedding. -/
theorem eliminationLeafComplementEquiv_val (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (q : (c.subst (fun y ↦ if y = x then t else Term.var y)).GraphLeaf) :
    (c.eliminationLeafComplementEquiv x t p hp unique q).val =
      c.eliminationLeafEmbedding x t p hp unique q := by
  change (c.headLeafEquiv (Term.var x, t))
    ((c.retainedHeadLeavesEquiv x t p hp unique)
      (c.eliminationLeavesEquiv x t p hp unique q)).val = _
  cases he : c.eliminationLeavesEquiv x t p hp unique q with
  | inl v =>
    change c.headLeafEquiv (Term.var x, t) (.inr (.inl v)) = _
    change _ = c.headLeafEquiv (Term.var x, t)
      (.inr ((Function.Embedding.sumMap (.refl _) (.subtype _))
        (c.eliminationLeavesEquiv x t p hp unique q)))
    rw [he]
    rfl
  | inr v =>
    change c.headLeafEquiv (Term.var x, t) (.inr (.inr v.val)) = _
    change _ = c.headLeafEquiv (Term.var x, t)
      (.inr ((Function.Embedding.sumMap (.refl _) (.subtype _))
        (c.eliminationLeavesEquiv x t p hp unique q)))
    rw [he]
    rfl

/-- The head variable's named wire meets the selected occurrence in the remaining context. -/
theorem head_variable_partner (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (closed : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed) :
    (({ c with equations := (Term.var x, t) :: c.equations } : Config arity).graphLeafWiring
      closed).partner (c.headLeafEquiv (Term.var x, t) (.inl (Term.fragmentVarLeaf x))) =
        c.headLeafEquiv (Term.var x, t) (.inr (.inr p)) := by
  let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
  let := d.graphLeafEnum
  apply Wiring.ofNames_partner_eq d.graphLeafOrder
    (TermFragment.forestOrder_unique _ d.graphRootOrder_unique d.graphFragments)
    (TermFragment.forestOrder_cover _ d.graphRootOrder_cover d.graphFragments)
    d.graphLeafName (d.graphLeaf_two closed)
  · exact (c.headLeaf_left_ne_rest (Term.var x, t) (Term.fragmentVarLeaf x) p).symm
  · change ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).graphLeafName
      (c.headLeafEquiv (Term.var x, t) (.inr (.inr p))) = _
    rw [headLeafEquiv_name, headLeafEquiv_name]
    exact hp

/-- Elimination's leaf matching is the original matching with the selected wire removed. -/
theorem eliminationLeaf_matching (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (p : c.GraphLeaf) (hp : c.graphLeafName p = x)
    (unique : ∀ q, c.graphLeafName q = x → q = p)
    (sourceClosed : ({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).Closed)
    (targetClosed : (c.subst (fun y ↦ if y = x then t else Term.var y)).Closed) :
    let d : Config arity := { c with equations := (Term.var x, t) :: c.equations }
    let := d.graphLeafEnum
    ((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed).map
      (c.eliminationLeafComplementEquiv x t p hp unique) =
        (d.graphLeafWiring sourceClosed).splice
          (c.headLeafEquiv (Term.var x, t) (.inl (Term.fragmentVarLeaf x)))
          (c.headLeafEquiv (Term.var x, t) (.inr (.inr p)))
          (c.headLeaf_left_ne_rest (Term.var x, t) (Term.fragmentVarLeaf x) p) := by
  intro d
  let := d.graphLeafEnum
  dsimp only
  let a := c.headLeafEquiv (Term.var x, t) (.inl (Term.fragmentVarLeaf x))
  let b := c.headLeafEquiv (Term.var x, t) (.inr (.inr p))
  have hab := c.headLeaf_left_ne_rest (Term.var x, t) (Term.fragmentVarLeaf x) p
  have pair : (d.graphLeafWiring sourceClosed).partner a = b :=
    c.head_variable_partner x t p hp sourceClosed
  have hs := c.eliminationLeafEmbedding_wiring x t p hp unique sourceClosed targetClosed
  have hr := Wiring.respects_restrict ((d.graphLeafWiring sourceClosed).force a b)
    (fun q ↦ q ≠ a ∧ q ≠ b) ((d.graphLeafWiring sourceClosed).force_closed hab)
  have hs' : Wiring.Respects (c.eliminationLeafEmbedding x t p hp unique)
      ((c.subst (fun y ↦ if y = x then t else Term.var y)).graphLeafWiring targetClosed)
      ((d.graphLeafWiring sourceClosed).force a b) := by
    rw [Wiring.force_of_partner_eq _ pair]
    exact hs
  exact hs'.map_eq hr (c.eliminationLeafComplementEquiv x t p hp unique)
    (fun q ↦ (c.eliminationLeafComplementEquiv_val x t p hp unique q).symm)

end Geb.InteractionNet.Config

end
