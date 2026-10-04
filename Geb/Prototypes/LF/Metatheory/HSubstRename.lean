/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.HSubst
public import Geb.Prototypes.LF.Metatheory.Rename
public import Geb.Prototypes.PartialHorn.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Hereditary substitution and renaming

Hereditary substitution commutes with renaming: substituting and then renaming the result is
renaming the expression and the substituted term and then substituting. With de Bruijn indices,
the substitution for the variable of index {lit}`j` acts on an expression in a context of
{lit}`j` variables, the substituted one, and an outer context; a renaming of the outer context
is lifted past the {lit}`j` inner variables on the result and the substituted term, and past the
substituted one as well on the expression.

The substitution into an expression commutes with renaming whenever the reduction it is given
does ({lit}`hsubWith_rename`), by induction on the expression; the reduction at a simple type
does ({lit}`reduce_rename`), by induction on the simple type, its substitution at the domain
being the substitution of the first case. Both are the de Bruijn form of the stability of
hereditary substitution under weakening and exchange ({cite}`HarperLicata2007`, Lemmas 2.6 and
2.7).

## Main definitions

* {lit}`RenameCompat` — a reduction commutes with renaming.

## Main statements

* {lit}`hsubWith_node`, {lit}`hsubWith_var`, {lit}`hsubWith_node_of_ne` — the computation
  rules of the substitution.
* {lit}`hsubWith_rename` — the substitution commutes with renaming, given a reduction that does.
* {lit}`reduce_rename`, {lit}`hsub_rename` — the reduction and the hereditary substitution at a
  simple type commute with renaming.

## References

* {cite}`HarperLicata2007`, Section 2.3.

## Tags

logical framework, LF, hereditary substitution, renaming, weakening
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- A list of partial values all has values exactly when it is the list of those values. -/
theorem mapM_id_eq_some_iff {β : Type} (xs : List (Option β)) (ys : List β) :
    xs.mapM id = some ys ↔ xs = ys.map some := by
  rw [PartialHorn.mapM_eq_some_iff, List.map_id]

/-- A list of partial values all of which have values, in order, element by element. -/
theorem mapM_id_eq_some_of_getElem {β : Type} {xs : List (Option β)} {ys : List β}
    (hl : xs.length = ys.length) (h : ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length),
      xs[k] = some ys[k]) : xs.mapM id = some ys := by
  rw [mapM_id_eq_some_iff]
  exact List.ext_getElem (by simp [hl]) fun k h₁ h₂ ↦ by
    simpa using h k h₁ (by simpa using h₂)

/-- The values of a list of partial values all of which have them, element by element. -/
theorem getElem_of_mapM_id_eq_some {β : Type} {xs : List (Option β)} {ys : List β}
    (h : xs.mapM id = some ys) :
    xs.length = ys.length ∧ ∀ k (h₁ : k < xs.length) (h₂ : k < ys.length), xs[k] = some ys[k] := by
  rw [mapM_id_eq_some_iff] at h
  subst h
  exact ⟨by simp, fun k _ _ ↦ by simp⟩

/-- Mapping with indices after mapping is mapping with indices by the composite. -/
theorem mapIdx_map {α β γ : Type} (f : α → β) (g : ℕ → β → γ) (l : List α) :
    (l.map f).mapIdx g = l.mapIdx fun k a ↦ g k (f a) :=
  List.ext_getElem (by simp) fun k _ _ ↦ by simp

/-- The computation rule of the substitution. -/
theorem hsubWith_node (red : Expr → List Expr → Option Expr) (l : Label) (cs : List Expr)
    (n : Expr) (j : ℕ) :
    hsubWith red (RoseTree.node l cs) n j = hsubStep red l (cs.map (hsubWith red)) n j :=
  congrFun (congrFun (RoseTree.elim_node _ l cs) n) j

/-- The substitution into an application of a variable: the substitution into its spine, then
the reduction where the variable is the substituted one, and the renumbering of the variable
otherwise. -/
theorem hsubWith_var (red : Expr → List Expr → Option Expr) (i : ℕ) (cs : List Expr) (n : Expr)
    (j : ℕ) :
    hsubWith red (RoseTree.node (.app (.var i)) cs) n j =
      ((cs.map fun c ↦ hsubWith red c n j).mapM id).bind fun ms ↦
        if i = j then red n ms else some (Expr.var (if j < i then i - 1 else i) ms) := by
  rw [hsubWith_node, hsubStep, List.mapM_map, List.mapM_map]
  rfl

/-- The substitution into a node other than an application of a variable: the substitution into
each child, under the variables the node binds over it. -/
theorem hsubWith_node_of_ne (red : Expr → List Expr → Option Expr) (l : Label)
    (hl : ∀ i, l ≠ .app (.var i)) (cs : List Expr) (n : Expr) (j : ℕ) :
    hsubWith red (RoseTree.node l cs) n j = RoseTree.node l <$>
      (cs.mapIdx fun k c ↦ hsubWith red c (Expr.shift^[l.binders k] n) (j + l.binders k)).mapM
        id := by
  rw [hsubWith_node]
  rcases l with _ | _ | _ | (i | c)
  · simp only [hsubStep, mapIdx_map]
  · simp only [hsubStep, mapIdx_map]
  · simp only [hsubStep, mapIdx_map]
  · exact absurd rfl (hl i)
  · simp only [hsubStep, mapIdx_map]

/-- A reduction commutes with renaming: reducing and renaming the result is renaming the term
and the spine and reducing. -/
def RenameCompat (red : Expr → List Expr → Option Expr) : Prop :=
  ∀ (n : Expr) (ms : List Expr) (r : Expr) (ρ : ℕ → ℕ), red n ms = some r →
    red (n.rename ρ) (ms.map fun m ↦ m.rename ρ) = some (r.rename ρ)

/-- A label other than an application of a variable is left in place by renaming. -/
theorem Label.rename_of_ne {l : Label} (hl : ∀ i, l ≠ .app (.var i)) (σ : ℕ → ℕ) :
    l.rename σ = l := by
  rcases l with _ | _ | _ | (i | c)
  · rfl
  · rfl
  · rfl
  · exact absurd rfl (hl i)
  · rfl

/-- An application of a variable binds no variable over its spine. -/
@[simp] theorem Label.binders_app (h : Head) (k : ℕ) : (Label.app h).binders k = 0 := rfl

/-- The renumbering of a variable other than the substituted one commutes with renaming: the
variable of index {lit}`i` in a context with the variable of index {lit}`j` removed. -/
theorem iterate_liftR_renumber (j i : ℕ) (ρ : ℕ → ℕ) (h : i ≠ j) :
    liftR^[j] ρ (if j < i then i - 1 else i) =
      if j < liftR^[j + 1] ρ i then liftR^[j + 1] ρ i - 1 else liftR^[j + 1] ρ i := by
  rw [iterate_liftR_apply (j + 1), iterate_liftR_apply j]
  by_cases hij : i < j
  · simp [hij, show i < j + 1 by omega, show ¬ j < i by omega]
  · have hji : j < i := by omega
    simp only [hji, ↓reduceIte, show ¬ i < j + 1 by omega,
      show ¬ i - 1 < j by omega, show i - 1 - j = i - (j + 1) by omega]
    split_ifs <;> omega

/-- The renaming of the application of a variable: the variable renamed, and the spine. -/
theorem rename_var (i : ℕ) (ms : List Expr) (ρ : ℕ → ℕ) :
    (Expr.var i ms).rename ρ = Expr.var (ρ i) (ms.map fun m ↦ m.rename ρ) := by
  rw [Expr.var, Expr.app, rename_node]
  exact congrArg _ (List.ext_getElem (by simp) fun k _ _ ↦ by simp)

/-- The substitution into an expression commutes with renaming, given a reduction that does: a
renaming of the context outside the substituted variable and the {lit}`j` variables inside it. -/
theorem hsubWith_rename {red : Expr → List Expr → Option Expr} (hred : RenameCompat red) :
    ∀ (e n : Expr) (j : ℕ) (ρ : ℕ → ℕ) (e' : Expr), hsubWith red e n j = some e' →
      hsubWith red (e.rename (liftR^[j + 1] ρ)) (n.rename (liftR^[j] ρ)) j =
        some (e'.rename (liftR^[j] ρ)) :=
  RoseTree.ind fun l cs ih n j ρ e' h ↦ by
    by_cases hv : ∃ i, l = .app (.var i)
    · obtain ⟨i, rfl⟩ := hv
      rw [hsubWith_var, Option.bind_eq_some_iff] at h
      obtain ⟨ms, hms, h⟩ := h
      obtain ⟨hl, hk⟩ := getElem_of_mapM_id_eq_some hms
      rw [rename_node]
      simp only [Label.rename, Head.rename, Label.binders_app, Function.iterate_zero_apply]
      rw [hsubWith_var]
      have hms' : ((cs.mapIdx fun _ c ↦ Expr.rename c (liftR^[j + 1] ρ)).map
          fun c ↦ hsubWith red c (n.rename (liftR^[j] ρ)) j).mapM id =
          some (ms.map fun m ↦ m.rename (liftR^[j] ρ)) :=
        mapM_id_eq_some_of_getElem (by simpa using hl) fun k h₁ h₂ ↦ by
          have hk' := hk k (by simpa using h₁) (by simpa using h₂)
          simp only [List.getElem_map, List.getElem_mapIdx] at hk' ⊢
          exact ih _ (List.getElem_mem _) _ _ _ _ hk'
      rw [hms', Option.bind_some]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte] at h
        have hii : liftR^[i + 1] ρ i = i := by
          rw [iterate_liftR_apply]
          simp
        simp only [hii, ↓reduceIte]
        exact hred _ _ _ _ h
      · simp only [hij, ↓reduceIte] at h
        obtain rfl := Option.some.inj h
        have hne : liftR^[j + 1] ρ i ≠ j := by
          rw [iterate_liftR_apply]
          split_ifs <;> omega
        simp only [hne, ↓reduceIte]
        rw [rename_var, iterate_liftR_renumber j i ρ hij]
    · have hl : ∀ i, l ≠ .app (.var i) := fun i h ↦ hv ⟨i, h⟩
      rw [hsubWith_node_of_ne red l hl, Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨ys, hys, rfl⟩ := h
      obtain ⟨hlen, hk⟩ := getElem_of_mapM_id_eq_some hys
      rw [rename_node, Label.rename_of_ne hl, hsubWith_node_of_ne red l hl, rename_node,
        Label.rename_of_ne hl]
      refine congrArg (Option.map _) (mapM_id_eq_some_of_getElem (by simpa using hlen)
        fun k h₁ h₂ ↦ ?_)
      have hk' := hk k (by simpa using h₁) (by simpa using h₂)
      simp only [List.getElem_mapIdx] at hk' ⊢
      have := ih _ (List.getElem_mem _) _ _ ρ _ hk'
      rw [iterate_shift_rename, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
      rw [show l.binders k + (j + 1) = j + l.binders k + 1 by omega,
        show l.binders k + j = j + l.binders k by omega]
      exact this

/-- The computation rule of the reduction. -/
theorem reduce_node (l : SimpleLabel) (cs : List SimpleTy) :
    reduce (RoseTree.node l cs) = reduceStep l (cs.map reduce) :=
  RoseTree.elim_node _ l cs

/-- The reduction at a simple type commutes with renaming. -/
theorem reduce_rename : ∀ α : SimpleTy, RenameCompat (reduce α) :=
  RoseTree.ind fun l cs ih n ms r ρ h ↦ by
    rw [reduce_node] at h ⊢
    rcases l with a | _
    · rcases cs with _ | ⟨c, cs⟩
      · rcases ms with _ | ⟨m, ms⟩
        · change some n = some r at h
          change some (n.rename ρ) = some (r.rename ρ)
          rw [Option.some.inj h]
        · simp [reduceStep] at h
      · simp [reduceStep] at h
    · rcases cs with _ | ⟨α₁, _ | ⟨α₂, _ | ⟨α₃, cs⟩⟩⟩
      · simp [reduceStep] at h
      · simp [reduceStep] at h
      · rcases ms with _ | ⟨m, ms⟩
        · simp [reduceStep] at h
        · obtain ⟨l', cs', rfl⟩ : ∃ l' cs', n = RoseTree.node l' cs' :=
            ⟨n.label, n.children, (RoseTree.node_label_children n).symm⟩
          simp only [List.map_cons, List.map_nil, reduceStep, RoseTree.label_node,
            RoseTree.children_node] at h
          simp only [List.map_cons, List.map_nil, reduceStep, rename_node, RoseTree.label_node,
            RoseTree.children_node]
          rcases l' with _ | _ | _ | _
          · simp at h
          · simp at h
          · rcases cs' with _ | ⟨b, _ | ⟨b₂, cs'⟩⟩
            · simp at h
            · obtain ⟨b', hb, hr⟩ := Option.bind_eq_some_iff.mp h
              have hb' := hsubWith_rename (ih α₁ (by simp)) b m 0 ρ b' hb
              simp only [zero_add, Function.iterate_one, Function.iterate_zero_apply] at hb'
              simp only [Label.rename, List.mapIdx_cons, List.mapIdx_nil]
              rw [show Label.lam.binders 0 = 1 from rfl, Function.iterate_one, hb',
                Option.bind_some]
              exact ih α₂ (by simp) _ _ _ _ hr
            · simp at h
          · simp at h
      · simp [reduceStep] at h

/-- The hereditary substitution at a simple type commutes with renaming. -/
theorem hsub_rename (α : SimpleTy) (e n : Expr) (j : ℕ) (ρ : ℕ → ℕ) (e' : Expr)
    (h : hsub α n e j = some e') :
    hsub α (n.rename (liftR^[j] ρ)) (e.rename (liftR^[j + 1] ρ)) j =
      some (e'.rename (liftR^[j] ρ)) :=
  hsubWith_rename (reduce_rename α) e n j ρ e' h

end Geb.LF

end
