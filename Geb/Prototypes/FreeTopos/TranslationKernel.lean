/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.TranslationLibrary
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The kernel's values represented in the topos of types and functional relations

The translation of the kernel ({name}`Geb.FreeTopos.Translation.term`) takes each
kernel type to an object of the internal language ({name}`Geb.FreeTopos.Translation.ty`) and each
well-typed kernel term to a term of the internal language. This module relates the kernel's
denotation of each type ({name}`Geb.Kernel.Ty.den`) to the value of its translation in the topos
of types and functional relations: a tree to the tree of the bitstrings of its labels in the
enumeration of {cite}`Oitavem2010`, and the unit, product, function and list types
componentwise. It proves the fundamental lemma of that logical relation: a kernel term's
translation, in a represented context, has the type the kernel's checker infers and represents
the term's denotation.

## Main definitions

* {lit}`RN` — the representation of a label by its bitstring.
* {lit}`MTy`, {lit}`KRel` — the value of a kernel type's translation, and the representation of
  the type's denotation by it.
* {lit}`CtxRep` — a kernel context represented at a context of the internal language.
* {lit}`GlobRep` — a kernel program's globals represented by the translated program's definitions.

## Main statements

* {lit}`ty_spec` — a kernel type's translation is a type of the internal language whose value is
  {lit}`MTy`.
* {lit}`repC_primT`, {lit}`repC_foldT`, {lit}`repC_iterT`, {lit}`repC_foldrT`,
  {lit}`repC_lcaseT`, {lit}`repC_quote` — the translations of the kernel's primitives, constants
  and quoted trees represent them.
* {lit}`repC_term` — the fundamental lemma.

## Implementation notes

The library's definitions are specified through the indices of bitstrings; the lemmas
{lit}`represents_bin`, {lit}`represents_lab` and their companions convert those specifications to
the kernel's labels. The representations of the kernel's constants hold in every context, their
variables reached through {lit}`repC_var0` and {lit}`repC_varS`.

## References

* {cite}`Oitavem2010`, Remark 2.2, for the enumeration of the bitstrings.

## Tags

translation, kernel, logical relation, representation, functional relation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Globals RepC objs compileDefs)
open Sorts
open scoped Internal
open scoped FinEnum

/-- The representation of a label by the bitstring of its index. -/
def RN : ℕ → List Bit → Prop := fun n w ↦ w = ofNum n

/-- The value of a kernel type's translation in the topos of types and functional relations:
the trees of bitstrings for the base type, and the terminal type, products, functional relations
and lists for the others. -/
def MTy : Kernel.Tree → Type :=
  WType.elim Type fun ⟨(l, k), g⟩ ↦
    match l, k, g with
    | Kernel.Label.tyTree, 0, _ => RoseTree (List Bit)
    | Kernel.Label.tyProd, 2, g => g 0 × g 1
    | Kernel.Label.tyArrow, 2, g => FunRel (g 0) (g 1)
    | Kernel.Label.tyList, 1, g => List (g 0)
    | _, _, _ => Unit

/-- The representation of a kernel type's denotation by the value of its translation: a tree by
the tree of its labels' bitstrings, and the unit, product, function and list types
componentwise. -/
def KRel : (T : Kernel.Tree) → Kernel.Ty.den T → MTy T → Prop :=
  WType.rec (motive := fun T ↦ Kernel.Ty.den T → MTy T → Prop) fun a g ih ↦
    match a, g, ih with
    | (Kernel.Label.tyTree, 0), _, _ => Rep.rose RN
    | (Kernel.Label.tyProd, 2), _, ih => Rep.prod (ih 0) (ih 1)
    | (Kernel.Label.tyArrow, 2), _, ih => Rep.exp (ih 0) (ih 1)
    | (Kernel.Label.tyList, 1), _, ih => Rep.list (ih 0)
    | _, _, _ => fun _ _ ↦ True

variable {ds : List PartialHorn.Defn}

/-! The representations that are graphs of functions. -/

section Graphs

variable {S A : Type}

/-- Lists represent lists elementwise by a function exactly when they are its image. -/
theorem list_iff_map {R : S → A → Prop} {f : S → A} :
    ∀ (l : List S), (∀ s ∈ l, ∀ a, R s a ↔ a = f s) → ∀ l', Rep.list R l l' ↔ l' = l.map f :=
  List.rec (fun _ l' ↦ by simp [Rep.list]) fun s l ih h l' ↦ by
    rw [Rep.list, List.forall₂_cons_left_iff]
    have ih' := ih fun s' hs' ↦ h s' (List.mem_cons_of_mem s hs')
    refine ⟨fun ⟨a, l'', h₁, h₂, h₃⟩ ↦ ?_, fun h' ↦
      ⟨f s, l.map f, (h s List.mem_cons_self _).mpr rfl, (ih' _).mpr rfl, h'⟩⟩
    rw [h₃, (h s List.mem_cons_self a).mp h₁, (ih' l'').mp h₂, List.map_cons]

/-- Trees represent trees node by node by a function exactly when they are its image. -/
theorem rose_iff_map {R : S → A → Prop} {f : S → A} (h : ∀ s a, R s a ↔ a = f s) :
    ∀ (t : RoseTree S) (u : RoseTree A), Rep.rose R t u ↔ u = t.map f :=
  RoseTree.ind fun l cs ih u ↦ by
    rw [← RoseTree.node_label_children u, Rep.rose_node, RoseTree.map_node, eq_comm,
      RoseTree.node_eq_iff, RoseTree.label_node, RoseTree.children_node, h, eq_comm,
      list_iff_map cs (fun c hc ↦ ih c hc) u.children, eq_comm (a := List.map _ cs)]

end Graphs

/-- A bit represents exactly itself. -/
theorem rbit_iff (b c : Bit) : RBit b c ↔ c = id b := by
  rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases c with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [RBit, Rep.sum, Rep.unit]

/-- A bitstring represents exactly itself. -/
theorem rbits_iff (w u : List Bit) : RBits w u ↔ u = w := by
  rw [RBits, list_iff_map w fun b _ ↦ rbit_iff b, List.map_id]

/-- A tree of bitstrings represents exactly itself. -/
theorem rtree_iff (t u : RoseTree (List Bit)) : RTree t u ↔ u = t := by
  rw [RTree, rose_iff_map (f := id) rbits_iff, RoseTree.map_id]

/-- A kernel tree is represented exactly by the tree of its labels' bitstrings. -/
theorem rose_rn_iff (t : RoseTree ℕ) (u : RoseTree (List Bit)) :
    Rep.rose RN t u ↔ u = t.map ofNum :=
  rose_iff_map (fun _ _ ↦ Iff.rfl) t u


/-- A representation of a function is one of each function it computes after conversions of
its arguments and values between representations. -/
theorem represents_change {ρ : List relTopos.model.Val} {f : Tree} {S T S' T' A B : Type}
    {R : S → A → Prop} {R' : T → B → Prop} {F : S → T} (h : Represents ρ f R R' F)
    {Q : S' → A → Prop} {Q' : T' → B → Prop} (g : S' → S) (k : T → T')
    (hQ : ∀ s a, Q s a → R (g s) a) (hQ' : ∀ t b, R' t b → Q' (k t) b) {F' : S' → T'}
    (hF : ∀ s, k (F (g s)) = F' s) : Represents ρ f Q Q' F' :=
  (h.mono g k hQ hQ').congr hF

/-- A representation of a function by a term is one of each equal function. -/
theorem repC_congr {G : Globals} {n : ℕ} {ρ : List relTopos.model.Val} {t : Term} {X : Tree}
    {e : List (Tree × Tree)} {a : Tree} {S T A B : Type} {R : S → A → Prop} {R' : T → B → Prop}
    {F F' : S → T} (h : RepC G n ds ρ t X e a R R' F) (hF : ∀ s, F s = F' s) :
    RepC G n ds ρ t X e a R R' F' :=
  let ⟨f, hf, hr⟩ := h
  ⟨f, hf, hr.congr hF⟩

/-- A bitstring represents a label's bitstring as the label represents it. -/
theorem rbits_of_rn {m : ℕ} {w : List Bit} (h : RN m w) : RBits (ofNum m) w := (rbits_iff _ _).mpr h

/-- A bitstring represents its index as it represents itself. -/
theorem rn_of_rbits {w u : List Bit} (h : RBits w u) : RN (rankB w) u := by
  rw [RN, (rbits_iff _ _).mp h, ofNum_rankB]

/-- A tree of bitstrings represents a kernel tree's image as the kernel tree represents it. -/
theorem rtree_of_rose {t : RoseTree ℕ} {u : RoseTree (List Bit)} (h : Rep.rose RN t u) :
    RTree (t.map ofNum) u :=
  (rtree_iff _ _).mpr ((rose_rn_iff _ _).mp h)

/-- A tree of bitstrings represents the tree of its indices as it represents itself. -/
theorem rose_of_rtree {t u : RoseTree (List Bit)} (h : RTree t u) :
    Rep.rose RN (t.map rankB) u := by
  rw [rose_rn_iff, (rtree_iff _ _).mp h, RoseTree.map_map]
  conv_lhs => rw [← RoseTree.map_id t]
  exact congrArg (RoseTree.map · t) (funext fun w ↦ (ofNum_rankB w).symm)

/-- A representation of a binary operation of indices by bitstrings is one of the operation by
labels. -/
theorem represents_bin {ρ : List relTopos.model.Val} {f : Tree} {op : ℕ → ℕ → ℕ}
    (h : Represents ρ f (Rep.prod RBits RBits) RBits fun p ↦ ofNum (op (rankB p.1) (rankB p.2))) :
    Represents ρ f (Rep.prod RN RN) RN fun p ↦ op p.1 p.2 :=
  represents_change h (fun p ↦ (ofNum p.1, ofNum p.2)) rankB
    (fun _ _ h ↦ ⟨rbits_of_rn h.1, rbits_of_rn h.2⟩) (fun _ _ ↦ rn_of_rbits) fun _ ↦ by simp

/-- A representation of a unary operation of indices by bitstrings is one of the operation by
labels. -/
theorem represents_un {ρ : List relTopos.model.Val} {f : Tree} {op : ℕ → ℕ}
    (h : Represents ρ f RBits RBits fun w ↦ ofNum (op (rankB w))) :
    Represents ρ f RN RN op :=
  represents_change h ofNum rankB (fun _ _ ↦ rbits_of_rn) (fun _ _ ↦ rn_of_rbits) fun _ ↦ by simp

/-- A representation of the quotient and remainder of indices by bitstrings is one of those of
labels. -/
theorem represents_divMod {ρ : List relTopos.model.Val} {f : Tree}
    (h : Represents ρ f (Rep.prod RBits RBits) (Rep.prod RBits RBits)
      fun p ↦ (ofNum (rankB p.1 / rankB p.2), ofNum (rankB p.1 % rankB p.2))) :
    Represents ρ f (Rep.prod RN RN) (Rep.prod RN RN) fun p ↦ (p.1 / p.2, p.1 % p.2) :=
  represents_change h (fun p ↦ (ofNum p.1, ofNum p.2)) (fun p ↦ (rankB p.1, rankB p.2))
    (fun _ _ h ↦ ⟨rbits_of_rn h.1, rbits_of_rn h.2⟩)
    (fun _ _ h ↦ ⟨rn_of_rbits h.1, rn_of_rbits h.2⟩) fun _ ↦ by simp

/-- The bitstrings of a tree's labels' indices are its labels. -/
@[simp] theorem map_rankB_map_ofNum (t : RoseTree ℕ) : (t.map ofNum).map rankB = t := by
  rw [RoseTree.map_map]
  conv_rhs => rw [← RoseTree.map_id t]
  exact congrArg (RoseTree.map · t) (funext rankB_ofNum)

/-- A representation of the label of trees of bitstrings is one of the label of kernel trees. -/
theorem represents_lab {ρ : List relTopos.model.Val} {f : Tree}
    (h : Represents ρ f RTree RBits RoseTree.label) :
    Represents ρ f (Rep.rose RN) RN RoseTree.label :=
  represents_change h (RoseTree.map ofNum) rankB (fun _ _ ↦ rtree_of_rose)
    (fun _ _ ↦ rn_of_rbits) fun _ ↦ by simp

/-- A representation of the children of trees of bitstrings is one of the children of kernel
trees. -/
theorem represents_children {ρ : List relTopos.model.Val} {f : Tree}
    (h : Represents ρ f RTree (Rep.list RTree) RoseTree.children) :
    Represents ρ f (Rep.rose RN) (Rep.list (Rep.rose RN)) RoseTree.children :=
  represents_change h (RoseTree.map ofNum) (List.map (RoseTree.map rankB))
    (fun _ _ ↦ rtree_of_rose)
    (fun _ _ h ↦ List.forall₂_map_left_iff.mpr (h.imp fun _ _ ↦ rose_of_rtree)) fun t ↦ by
      rw [RoseTree.children_map, List.map_map]
      conv_rhs => rw [← List.map_id t.children]
      exact List.map_congr_left fun c _ ↦ map_rankB_map_ofNum c

/-- A representation of the length of lists by bitstrings is one by labels. -/
theorem represents_length {ρ : List relTopos.model.Val} {f : Tree} {S A : Type}
    {R : S → A → Prop} (h : Represents ρ f (Rep.list R) RBits fun l ↦ ofNum l.length) :
    Represents ρ f (Rep.list R) RN List.length :=
  represents_change h id rankB (fun _ _ h ↦ h) (fun _ _ ↦ rn_of_rbits) fun _ ↦ by simp

/-- The bitstring of a positive index is not empty. -/
theorem ofNum_succ_ne_nil (m : ℕ) : ofNum (m + 1) ≠ [] := fun h ↦ by
  simpa using congrArg rankB h

/-- A representation of the conditional on bitstrings is one of the conditional on labels, the
first branch at a label other than zero. -/
theorem represents_cond {ρ : List relTopos.model.Val} {f : Tree} {S A : Type}
    {R : S → A → Prop}
    (h : Represents ρ f (Rep.prod (Rep.prod RBits R) R) R fun p ↦ p.1.1.rec p.2 fun _ _ _ ↦ p.1.2) :
    Represents ρ f (Rep.prod (Rep.prod RN R) R) R fun p ↦ if p.1.1 ≠ 0 then p.1.2 else p.2 :=
  represents_change h (fun p ↦ ((ofNum p.1.1, p.1.2), p.2)) id
    (fun _ _ h ↦ ⟨⟨rbits_of_rn h.1.1, h.1.2⟩, h.2⟩) (fun _ _ h ↦ h) fun p ↦ by
      rcases p with ⟨⟨_ | m, x⟩, y⟩
      · simp
      · rcases hw : ofNum (m + 1) with _ | ⟨b, w⟩
        · exact (ofNum_succ_ne_nil m hw).elim
        · simp

/-- A representation of iteration by bitstrings is one by labels. -/
theorem represents_iter {ρ : List relTopos.model.Val} {f : Tree} {S A : Type}
    {R : S → A → Prop}
    (h : Represents ρ f (Rep.prod (Rep.prod RBits (Rep.exp R R)) R) R
      fun p ↦ Nat.repeat p.1.2 (rankB p.1.1) p.2) :
    Represents ρ f (Rep.prod (Rep.prod RN (Rep.exp R R)) R) R
      fun p ↦ Nat.repeat p.1.2 p.1.1 p.2 :=
  represents_change h (fun p ↦ ((ofNum p.1.1, p.1.2), p.2)) id
    (fun _ _ h ↦ ⟨⟨rbits_of_rn h.1.1, h.1.2⟩, h.2⟩) (fun _ _ h ↦ h) fun _ ↦ by simp

/-- Kernel trees are equal exactly when the trees of their labels' bitstrings are. -/
theorem map_ofNum_inj {t u : RoseTree ℕ} : t.map ofNum = u.map ofNum ↔ t = u :=
  ⟨fun h ↦ by rw [← map_rankB_map_ofNum t, h, map_rankB_map_ofNum], congrArg _⟩

/-- A representation of the equality of trees of bitstrings is one of the equality of kernel
trees. -/
theorem represents_equal {ρ : List relTopos.model.Val} {f : Tree}
    (h : Represents ρ f (Rep.prod RTree RTree) RBits
      fun p ↦ ofNum (if p.1 = p.2 then 1 else 0)) :
    Represents ρ f (Rep.prod (Rep.rose RN) (Rep.rose RN)) RN
      fun p ↦ if p.1 = p.2 then 1 else 0 :=
  represents_change h (fun p ↦ (p.1.map ofNum, p.2.map ofNum)) rankB
    (fun _ _ h ↦ ⟨rtree_of_rose h.1, rtree_of_rose h.2⟩) (fun _ _ ↦ rn_of_rbits) fun p ↦ by
      rw [rankB_ofNum]
      by_cases hp : p.1 = p.2
      · rw [ite_eq_left hp, ite_eq_left (congrArg _ hp)]
      · rw [ite_eq_right hp, ite_eq_right (fun h ↦ hp (map_ofNum_inj.mp h))]

/-- The translation of the base type. -/
@[simp] theorem ty_tT : ty Kernel.tT = some treeTy := rfl

/-- The translation of the unit type. -/
@[simp] theorem ty_tUnit : ty Kernel.tUnit = some one := rfl

/-- The translation of a product type. -/
@[simp] theorem ty_tProd (A B : Kernel.Tree) :
    ty (Kernel.tProd A B) = (do pure (prod (← ty A) (← ty B))) := rfl

/-- The translation of a function type. -/
@[simp] theorem ty_tArrow (A B : Kernel.Tree) :
    ty (Kernel.tArrow A B) = (do pure (exp (← ty A) (← ty B))) := rfl

/-- The translation of a list type. -/
@[simp] theorem ty_tList (A : Kernel.Tree) :
    ty (Kernel.tList A) = (do pure (list (← ty A))) := rfl

/-- A kernel type's translation is a type of the internal language, over the operations of the
theory, whose value is {name}`MTy`. -/
theorem ty_spec {G : Globals} {n : ℕ} {ρ : List relTopos.model.Val} :
    ∀ (T : Kernel.Tree) {a : Tree}, ty T = some a →
      Internal.IsTy G n a = true ∧ PartialHorn.OpsBelow sig.length a = true ∧
        ObjVal ρ (unfoldTerm sig ds a) (MTy T) :=
  RoseTree.ind fun l cs ih a h ↦ by
    rw [ty, RoseTree.elim_node] at h
    have two : ∀ {c₀ c₁ : Kernel.Tree} {f : Tree → Tree → Tree}, cs = [c₀, c₁] →
        (do pure (f (← ty c₀) (← ty c₁))) = some a →
        ∃ x y, a = f x y ∧ (Internal.IsTy G n x = true ∧ PartialHorn.OpsBelow sig.length x = true ∧
          ObjVal ρ (unfoldTerm sig ds x) (MTy c₀)) ∧ (Internal.IsTy G n y = true ∧
          PartialHorn.OpsBelow sig.length y = true ∧ ObjVal ρ (unfoldTerm sig ds y) (MTy c₁)) := by
      intro c₀ c₁ f hcs h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      exact ⟨x, y, rfl, ih c₀ (by simp [hcs]) hx, ih c₁ (by simp [hcs]) hy⟩
    have ops : ∀ {k : ℕ} {ts : List Tree}, k < 43 → (∀ t ∈ ts, PartialHorn.OpsBelow sig.length t) →
        PartialHorn.OpsBelow sig.length (PartialHorn.op k ts) = true := fun hk hts ↦ by
      rw [PartialHorn.op, PartialHorn.opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, Internal.sig_length]
      exact ⟨hk, hts⟩
    split at h
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      obtain rfl := Option.some.inj h
      refine ⟨by is_ty, by simp only [Internal.sig_length]; decide, by obj_val⟩
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      obtain rfl := Option.some.inj h
      refine ⟨by is_ty, by simp only [Internal.sig_length]; decide, by obj_val⟩
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      obtain ⟨x, y, rfl, ⟨i₀, o₀, v₀⟩, i₁, o₁, v₁⟩ := two rfl h
      refine ⟨by simp [Internal.isTy_prod, i₀, i₁], ops (by decide) (by simp [o₀, o₁]), ?_⟩
      simp_unfold
      exact eval_prod v₀ v₁
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      obtain ⟨x, y, rfl, ⟨i₀, o₀, v₀⟩, i₁, o₁, v₁⟩ := two rfl h
      refine ⟨by simp [Internal.isTy_exp, i₀, i₁], ops (by decide) (by simp [o₀, o₁]), ?_⟩
      simp_unfold
      exact eval_exp v₀ v₁
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, cs⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, -⟩ := hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨i₀, o₀, v₀⟩ := ih c₀ (by simp) hx
      refine ⟨by simp [Internal.isTy_list, i₀], ops (by decide) (by simp [o₀]), ?_⟩
      simp_unfold
      exact eval_list v₀
    · exact nomatch h

/-- The value of a kernel type's translation, not unfolded, is {name}`MTy`. -/
theorem objVal_ty {T : Kernel.Tree} {a : Tree} (hT : ty T = some a) : ObjVal [] a (MTy T) := by
  obtain ⟨-, ho, hv⟩ := ty_spec (G := ⟨[], [], 0⟩) (n := 0) (ρ := []) (ds := []) T hT
  rwa [unfoldTerm_of_opsBelow [] sig a ho] at hv

/-- The value of a kernel type's translation, unfolded, is {name}`MTy`. -/
theorem objVal_ty' {T : Kernel.Tree} {a : Tree} (hT : ty T = some a) :
    ObjVal [] (unfoldTerm sig ds a) (MTy T) :=
  (ty_spec (G := ⟨[], [], 0⟩) (n := 0) (ρ := []) (ds := ds) T hT).2.2

/-- A kernel type with a translation is a type. -/
theorem isTy_of_ty : ∀ (T : Kernel.Tree) {a : Tree}, ty T = some a → Kernel.Ty.IsTy T = true :=
  RoseTree.ind fun l cs ih a h ↦ by
    rw [ty, RoseTree.elim_node] at h
    rw [Kernel.Ty.IsTy, RoseTree.elim_node]
    have two : ∀ {c₀ c₁ : Kernel.Tree} {f : Tree → Tree → Tree}, cs = [c₀, c₁] →
        (do pure (f (← ty c₀) (← ty c₁))) = some a →
        Kernel.Ty.IsTy c₀ = true ∧ Kernel.Ty.IsTy c₁ = true := by
      intro c₀ c₁ f hcs h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, -⟩ := h
      exact ⟨ih c₀ (by simp [hcs]) hx, ih c₁ (by simp [hcs]) hy⟩
    split at h
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      exact Bool.and_eq_true_iff.mpr (two rfl h)
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      exact Bool.and_eq_true_iff.mpr (two rfl h)
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, cs⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, -⟩ := hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, -⟩ := h
      exact ih c₀ (by simp) hx
    · exact nomatch h

/-! The representations of kernel contexts. -/

/-- A kernel context represented at a context object and an environment of the internal
language: the object's value is the type of the representations, and each variable's arrow
represents the projection, from the kernel's value of the context, to the variable's value. -/
def CtxRep (G : Globals) (ds : List PartialHorn.Defn) (Γ : Kernel.Ctx) (X : Tree)
    (e : List (Tree × Tree)) {S A : Type} (R : S → A → Prop) (proj : S → Γ.den) : Prop :=
  ObjVal [] (unfoldTerm sig ds X) A ∧ ∀ i p, Γ.var i = some p →
    ∃ a, ty p.1 = some a ∧ RepC G 0 ds [] (Term.var i) X e a R (KRel p.1) (p.2 ∘ proj)

/-- The empty context is represented at the terminal object. -/
theorem ctxRep_nil (G : Globals) : CtxRep G ds [] one [] Rep.unit fun _ ↦ () :=
  ⟨by obj_val, fun _ _ h ↦ nomatch h⟩

/-- A context extended by a variable is represented at the product with the variable's type. -/
theorem ctxRep_cons {G : Globals} {Γ : Kernel.Ctx} {X : Tree} {e : List (Tree × Tree)}
    {S A : Type} {R : S → A → Prop} {proj : S → Γ.den} (h : CtxRep G ds Γ X e R proj)
    {T : Kernel.Tree} {a : Tree} (hT : ty T = some a) :
    CtxRep G ds (T :: Γ) (prod X a) (Internal.extEnv X a e) (Rep.prod R (KRel T))
      fun s ↦ (s.2, proj s.1) := by
  have ha := (ty_spec (G := G) (n := 0) (ρ := []) (ds := ds) T hT).2.2
  have hX := h.1
  refine ⟨by obj_val, fun i p hp ↦ ?_⟩
  rcases i with _ | i
  · obtain rfl := (Option.some.inj hp).symm
    exact ⟨a, hT, repC_var0 h.1 ha⟩
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
    obtain ⟨b, hb, hr⟩ := h.2 i q hq
    exact ⟨b, hb, repC_varS h.1 ha hr⟩

/-! The primitives. -/

/-- The kernel's number of children is the length of the list of children. -/
theorem const_arity (t : Kernel.Tree) : Kernel.Const.arity t = Kernel.leaf t.children.length := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children t).symm⟩
  rw [RoseTree.children_node]
  rfl

/-- Repeating the tail drops as many elements. -/
theorem repeat_tail {α : Type} : ∀ (n : ℕ) (l : List α), Nat.repeat List.tail n l = l.drop n :=
  Nat.rec (fun _ ↦ rfl) fun n ih l ↦ by
    change List.tail (Nat.repeat List.tail n l) = _
    rw [ih, List.tail_drop]

/-- The kernel's child by index is the head of the children after as many tails as the index's
label, the leaf of label zero past their end. -/
theorem const_child (t i : Kernel.Tree) :
    Kernel.Const.child t i = (Nat.repeat List.tail i.label t.children).headD (Kernel.leaf 0) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children t).symm⟩
  rw [RoseTree.children_node, repeat_tail, List.headD_eq_head?_getD, List.head?_drop]
  change (if h : i.label < cs.length then cs.toArray[i.label] else Kernel.leaf 0) = _
  split_ifs with h
  · rw [List.getElem_toArray, List.getElem?_eq_getElem h, Option.getD_some]
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt h), Option.getD_none]

section Prims

open Internal (repC_lam repC_app repC_pair repC_fst repC_snd repC_nil repC_cons repC_lnode
  repC_star repC_call₀ repC_call₁ repC_call₂ repC_call₃ compiled_language)

variable {defs defsF : List Defn} (hF : compileDefs (globals defsF) = some ds)
  (hwf : PartialHorn.DefnsWF sig ds) {X : Tree} {e : List (Tree × Tree)} {S A : Type}
  {R : S → A → Prop} (hX : ObjVal [] (unfoldTerm sig ds X) A)
include hX

/-- The leaf of a label represents the leaf of the label it represents. -/
theorem repC_leaf {l : Term} {F : S → ℕ} (h : RepC (globals defs) 0 ds [] l X e bitsTy R RN F) :
    RepC (globals defs) 0 ds [] (leafT l) X e treeTy R (Rep.rose RN)
      fun s ↦ RoseTree.node (F s) [] := by
  refine repC_lnode rfl ?_ (repC_pair h (repC_nil rfl ?_ (repC_star hX _) ?_ (Rep.rose RN))) ?_
  side_goals

include hF hwf

/-- The label primitive represents the leaf of a tree's label. -/
theorem repC_prim_label :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (leafT (call D.lab [] [v 0]))) X e
      (exp treeTy treeTy) R (KRel (Kernel.tArrow Kernel.tT Kernel.tT))
      fun _ ↦ Kernel.Const.label := by
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_leaf ?_
    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
      (represents_lab (rep_lab hF hfl)) (repC_var0 hX ?_)))) fun _ ↦ rfl
  side_goals

omit hF hwf in
/-- A binary primitive represents the leaf of a function of its arguments' labels, when the
function its body computes does. -/
theorem repC_binT {f : Term → Term → Term} {op : ℕ → ℕ → ℕ}
    (h : RepC (globals defs) 0 ds [] (f (call D.lab [] [v 1]) (call D.lab [] [v 0]))
      (prod (prod X treeTy) treeTy)
      (Internal.extEnv (prod X treeTy) treeTy (Internal.extEnv X treeTy e)) bitsTy
      (Rep.prod (Rep.prod R (Rep.rose RN)) (Rep.rose RN)) RN
      fun s ↦ op s.1.2.label s.2.label) :
    RepC (globals defs) 0 ds [] (binT f) X e (exp treeTy (exp treeTy treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
      fun _ x y ↦ RoseTree.node (op x.label y.label) [] := by
  refine repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_leaf ?_ h))
  side_goals

/-- The application of a binary definition to the labels of the two innermost variables
represents the function the definition represents of the labels. -/
theorem repC_labs {k : ℕ} {d : Defn} {fk : Tree}
    (hk : (globals defs).defs[k]? = some (.language d))
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) (har : d.arity = 0) {a : Tree}
    (hty : PartialHorn.subst [] d.type = a)
    (hpar : d.params.map (PartialHorn.subst []) = [bitsTy, bitsTy]) {T B : Type}
    {Rt : T → B → Prop} {op : ℕ × ℕ → T}
    (hop : Represents [] (unfoldTerm sig ds fk) (Rep.prod RN RN) Rt op) :
    RepC (globals defs) 0 ds [] (call k [] [call D.lab [] [v 1], call D.lab [] [v 0]])
      (prod (prod X treeTy) treeTy)
      (Internal.extEnv (prod X treeTy) treeTy (Internal.extEnv X treeTy e)) a
      (Rep.prod (Rep.prod R (Rep.rose RN)) (Rep.rose RN)) Rt
      fun s ↦ op (s.1.2.label, s.2.label) := by
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  refine repC_call₂ (τ' := []) rfl hk hwf hdk (by simp [har]) (by simp) (by simp) .nil hty hpar hop
    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
      (represents_lab (rep_lab hF hfl)) (repC_varS ?_ ?_ (repC_var0 hX ?_)))
    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
      (represents_lab (rep_lab hF hfl)) (repC_var0 ?_ ?_))
  side_goals

/-- The addition primitive represents the addition of labels. -/
theorem repC_prim_add : RepC (globals defs) 0 ds [] (binT fun m n ↦ call D.add [] [m, n]) X e
    (exp treeTy (exp treeTy treeTy)) R
    (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
    fun _ ↦ Kernel.Const.add := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.add) (d := lib[D.add]) rfl
  exact repC_congr (repC_binT hX (repC_labs hF hwf hX rfl hf rfl rfl rfl
    (represents_bin (rep_add hF hwf hf)))) fun _ ↦ rfl

/-- The subtraction primitive represents the truncated subtraction of labels. -/
theorem repC_prim_sub : RepC (globals defs) 0 ds [] (binT fun m n ↦ call D.sub [] [m, n]) X e
    (exp treeTy (exp treeTy treeTy)) R
    (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
    fun _ ↦ Kernel.Const.sub := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.sub) (d := lib[D.sub]) rfl
  exact repC_congr (repC_binT hX (repC_labs hF hwf hX rfl hf rfl rfl rfl
    (represents_bin (rep_sub hF hwf hf)))) fun _ ↦ rfl

/-- The multiplication primitive represents the multiplication of labels. -/
theorem repC_prim_mul : RepC (globals defs) 0 ds [] (binT fun m n ↦ call D.mul [] [m, n]) X e
    (exp treeTy (exp treeTy treeTy)) R
    (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
    fun _ ↦ Kernel.Const.mul := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.mul) (d := lib[D.mul]) rfl
  exact repC_congr (repC_binT hX (repC_labs hF hwf hX rfl hf rfl rfl rfl
    (represents_bin (rep_mul hF hwf hf)))) fun _ ↦ rfl

/-- The division primitive represents the quotient of labels. -/
theorem repC_prim_div :
    RepC (globals defs) 0 ds [] (binT fun m n ↦ Term.fst (call D.divMod [] [m, n])) X e
      (exp treeTy (exp treeTy treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
      fun _ ↦ Kernel.Const.div := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.divMod) (d := lib[D.divMod]) rfl
  refine repC_congr (repC_binT hX (repC_fst (repC_labs hF hwf hX (a := prod bitsTy bitsTy) rfl hf
    rfl rfl rfl
    (represents_divMod (rep_divMod hF hwf hf))) ?_ ?_)) fun _ ↦ rfl
  side_goals

/-- The remainder primitive represents the remainder of labels. -/
theorem repC_prim_mod :
    RepC (globals defs) 0 ds [] (binT fun m n ↦ Term.snd (call D.divMod [] [m, n])) X e
      (exp treeTy (exp treeTy treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
      fun _ ↦ Kernel.Const.mod := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.divMod) (d := lib[D.divMod]) rfl
  refine repC_congr (repC_binT hX (repC_snd (repC_labs hF hwf hX (a := prod bitsTy bitsTy) rfl hf
    rfl rfl rfl
    (represents_divMod (rep_divMod hF hwf hf))) ?_ ?_)) fun _ ↦ rfl
  side_goals

/-- The equality primitive represents the test of equality of labels. -/
theorem repC_prim_eq : RepC (globals defs) 0 ds [] (binT fun m n ↦ call D.eqB [] [m, n]) X e
    (exp treeTy (exp treeTy treeTy)) R
    (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
    fun _ ↦ Kernel.Const.eq := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.eqB) (d := lib[D.eqB]) rfl
  refine repC_congr (repC_binT (op := fun m n ↦ if m = n then 1 else 0) hX
    (repC_labs hF hwf hX rfl hf rfl rfl rfl
      (represents_bin (op := fun m n ↦ if m = n then 1 else 0) (rep_eqB hF hwf hf)))) fun _ ↦ ?_
  funext x y
  simp only [Kernel.Const.eq, Kernel.ofBool, Kernel.leaf, beq_iff_eq]

/-- The comparison primitive represents the test of order of labels. -/
theorem repC_prim_lt : RepC (globals defs) 0 ds [] (binT fun m n ↦ call D.ltB [] [m, n]) X e
    (exp treeTy (exp treeTy treeTy)) R
    (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
    fun _ ↦ Kernel.Const.lt := by
  obtain ⟨f, hf⟩ := compiled_language hF (k := D.ltB) (d := lib[D.ltB]) rfl
  refine repC_congr (repC_binT (op := fun m n ↦ if m < n then 1 else 0) hX
    (repC_labs hF hwf hX rfl hf rfl rfl rfl
      (represents_bin (op := fun m n ↦ if m < n then 1 else 0) (rep_ltB hF hwf hf)))) fun _ ↦ ?_
  funext x y
  simp only [Kernel.Const.lt, Kernel.ofBool, Kernel.leaf, decide_eq_true_eq]

/-- The logarithm primitive represents the leaf of the base-two logarithm of a label. -/
theorem repC_prim_log2 :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (leafT (call D.log2 [] [call D.lab [] [v 0]])))
      X e (exp treeTy treeTy) R (KRel (Kernel.tArrow Kernel.tT Kernel.tT))
      fun _ ↦ Kernel.Const.log2 := by
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  obtain ⟨fg, hfg⟩ := compiled_language hF (k := D.log2) (d := lib[D.log2]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_leaf ?_
    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfg rfl (by simp) (by simp) .nil rfl rfl
      (represents_un (rep_log2 hF hwf hfg))
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
        (represents_lab (rep_lab hF hfl)) (repC_var0 hX ?_))))) fun _ ↦ rfl
  side_goals

/-- The children primitive represents the list of a tree's children. -/
theorem repC_prim_children :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (call D.children [] [v 0])) X e
      (exp treeTy (list treeTy)) R (KRel (Kernel.tArrow Kernel.tT (Kernel.tList Kernel.tT)))
      fun _ ↦ Kernel.Const.children := by
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.children) (d := lib[D.children]) rfl
  refine repC_congr (repC_lam ?_ hX ?_
    (repC_call₁ (τ' := []) (a := list treeTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil rfl
      rfl (represents_children (rep_children hF hwf hfc)) (repC_var0 hX ?_))) fun _ ↦ rfl
  side_goals

/-- The node primitive represents the node of a tree's label over a list of children. -/
theorem repC_prim_node :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (Term.lam (list treeTy)
      (nodeT (Term.pair (call D.lab [] [v 1]) (v 0))))) X e
      (exp treeTy (exp (list treeTy) treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow (Kernel.tList Kernel.tT) Kernel.tT)))
      fun _ ↦ Kernel.Const.node := by
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_lnode rfl ?_ (repC_pair
    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
      (represents_lab (rep_lab hF hfl)) (repC_varS ?_ ?_ (repC_var0 hX ?_)))
    (repC_var0 ?_ ?_)) ?_))) fun _ ↦ rfl
  side_goals

/-- The equality of trees primitive represents the test of equality of kernel trees. -/
theorem repC_prim_equal :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (Term.lam treeTy
      (leafT (call D.equal [] [v 1, v 0])))) X e (exp treeTy (exp treeTy treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
      fun _ ↦ Kernel.Const.equal := by
  obtain ⟨fe, hfe⟩ := compiled_language hF (k := D.equal) (d := lib[D.equal]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_leaf ?_
    (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfe rfl (by simp) (by simp) .nil rfl rfl
      (represents_equal (rep_equal hF hwf hfe)) (repC_varS ?_ ?_ (repC_var0 hX ?_))
      (repC_var0 ?_ ?_))))) fun _ ↦ ?hc
  case hc =>
    funext (x : Kernel.Tree) (y : Kernel.Tree)
    change RoseTree.node (if x = y then 1 else 0) [] = Kernel.Const.equal x y
    by_cases h : x = y <;> simp [h, Kernel.Const.equal, Kernel.ofBool, Kernel.leaf]
  side_goals

/-- The number of children primitive represents the leaf of the length of a tree's children. -/
theorem repC_prim_arity :
    RepC (globals defs) 0 ds [] (Term.lam treeTy
      (leafT (call D.length [treeTy] [call D.children [] [v 0]]))) X e (exp treeTy treeTy) R
      (KRel (Kernel.tArrow Kernel.tT Kernel.tT)) fun _ ↦ Kernel.Const.arity := by
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.length) (d := lib[D.length]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.children) (d := lib[D.children]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_leaf ?_
    (repC_call₁ (τ' := [RoseTree (List Bit)]) (a := bitsTy) rfl rfl hwf hfl rfl ?_ ?_
      (.cons ?_ .nil) rfl rfl (represents_length (rep_length hF hwf hfl (Rep.rose RN)))
      (repC_call₁ (τ' := []) (a := list treeTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil rfl
        rfl (represents_children (rep_children hF hwf hfc)) (repC_var0 hX ?_)))))
    fun _ ↦ funext fun t ↦ (const_arity t).symm
  side_goals

/-- The child primitive represents the child of a tree by index, the leaf of label zero past
its children. -/
theorem repC_prim_child :
    RepC (globals defs) 0 ds [] (Term.lam treeTy (Term.lam treeTy (call D.headD [treeTy]
      [leafT bnilT, call D.iter [list treeTy] [call D.lab [] [v 0],
        Term.lam (list treeTy) (call D.tail [treeTy] [v 0]), call D.children [] [v 1]]]))) X e
      (exp treeTy (exp treeTy treeTy)) R
      (KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow Kernel.tT Kernel.tT)))
      fun _ ↦ Kernel.Const.child := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.children) (d := lib[D.children]) rfl
  obtain ⟨ft, hft⟩ := compiled_language hF (k := D.tail) (d := lib[D.tail]) rfl
  obtain ⟨fh, hfh⟩ := compiled_language hF (k := D.headD) (d := lib[D.headD]) rfl
  obtain ⟨fi, hfi⟩ := compiled_language hF (k := D.iter) (d := lib[D.iter]) rfl
  have hn : Represents [] (unfoldTerm sig ds fn) Rep.unit RN fun _ ↦ 0 :=
    represents_change (rep_bnil hF hfn) id rankB (fun _ _ h ↦ h) (fun _ _ ↦ rn_of_rbits)
      fun _ ↦ rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_
    (repC_call₂ (τ' := [RoseTree (List Bit)]) (a := treeTy) rfl rfl hwf hfh rfl ?_ ?_
      (.cons ?_ .nil) rfl rfl (rep_headD hF hfh (Rep.rose RN))
      (repC_leaf ?_ (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ hn))
      (repC_call₃ (τ' := [List (RoseTree (List Bit))]) (a := list treeTy) rfl rfl hwf hfi rfl ?_ ?_
        (.cons ?_ .nil) rfl rfl (represents_iter (rep_iter hF hfi (Rep.list (Rep.rose RN))))
        (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
          (represents_lab (rep_lab hF hfl)) (repC_var0 ?_ ?_))
        (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := [RoseTree (List Bit)]) (a := list treeTy) rfl rfl hwf
          hft rfl ?_ ?_ (.cons ?_ .nil) rfl rfl (rep_tail hF hft (Rep.rose RN)) (repC_var0 ?_ ?_)))
        (repC_call₁ (τ' := []) (a := list treeTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil rfl
          rfl (represents_children (rep_children hF hwf hfc))
          (repC_varS ?_ ?_ (repC_var0 hX ?_))))))) ?hc
  case hc => exact fun _ ↦ funext fun t ↦ funext fun i ↦ (const_child t i).symm
  side_goals

/-- Each primitive's translation represents the primitive, at its type's translation. -/
theorem repC_primT {k : ℕ} {g : Kernel.Glob} {u : Term} (hg : Kernel.prims[k]? = some g)
    (hu : primT k = some u) :
    ∃ a, ty g.1 = some a ∧ RepC (globals defs) 0 ds [] u X e a R (KRel g.1) fun _ ↦ g.2 := by
  match k, hg, hu with
  | 0, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_label hF hwf hX⟩
  | 1, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_arity hF hwf hX⟩
  | 2, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_child hF hwf hX⟩
  | 3, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_node hF hwf hX⟩
  | 4, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_children hF hwf hX⟩
  | 5, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_add hF hwf hX⟩
  | 6, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_sub hF hwf hX⟩
  | 7, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_mul hF hwf hX⟩
  | 8, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_div hF hwf hX⟩
  | 9, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_mod hF hwf hX⟩
  | 10, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_eq hF hwf hX⟩
  | 11, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_lt hF hwf hX⟩
  | 12, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_equal hF hwf hX⟩
  | 13, hg, hu =>
    obtain rfl := Option.some.inj hg
    obtain rfl := Option.some.inj hu
    exact ⟨_, rfl, repC_prim_log2 hF hwf hX⟩
  | _ + 14, hg, _ => exact nomatch hg

/-- The numeral of a natural number represents it. -/
theorem repC_numeral (n : ℕ) :
    RepC (globals defs) 0 ds [] (numeral n) X e bitsTy R RN fun _ ↦ n := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨f1, hf1⟩ := compiled_language hF (k := D.b1) (d := lib[D.b1]) rfl
  have key : ∀ w : List Bool, RepC (globals defs) 0 ds []
      (w.foldr (fun b t ↦ if b then b1T t else b0T t) bnilT) X e bitsTy R RBits
      fun _ ↦ w.map fun b ↦ bif b then .inr () else .inl () :=
    List.rec (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl hX (rep_bnil hF hfn))
      fun b w ih ↦ by
        cases b
        · exact repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
            rfl rfl (rep_b0 hF hf0) ih
        · exact repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf1 rfl (by simp) (by simp) .nil
            rfl rfl (rep_b1 hF hf1) ih
  obtain ⟨f, hf, hr⟩ := key (Oitavem.unrank n)
  exact ⟨f, hf, represents_change hr id rankB (fun _ _ h ↦ h) (fun _ _ ↦ rn_of_rbits)
    fun _ ↦ rankB_ofNum n⟩

/-- A quoted tree's translation represents the tree. -/
theorem repC_quote : ∀ t : Kernel.Tree,
    RepC (globals defs) 0 ds [] (quoteT t) X e treeTy R (Rep.rose RN) fun _ ↦ t :=
  RoseTree.ind fun l cs ih ↦ by
    have hl : ∀ cs' : List Kernel.Tree, (∀ c ∈ cs', RepC (globals defs) 0 ds [] (quoteT c) X e
        treeTy R (Rep.rose RN) fun _ ↦ c) → RepC (globals defs) 0 ds []
        ((cs'.map quoteT).foldr (consT treeTy) (nilT treeTy)) X e (list treeTy) R
        (Rep.list (Rep.rose RN)) fun _ ↦ cs' :=
      List.rec (fun _ ↦ by
          refine repC_nil rfl ?_ (repC_star hX _) ?_ (Rep.rose RN)
          side_goals)
        fun c cs' ih' h ↦ by
          refine repC_cons rfl ?_ (repC_pair (h c List.mem_cons_self)
            (ih' fun c' hc' ↦ h c' (List.mem_cons_of_mem c hc'))) ?_
          side_goals
    rw [quoteT, RoseTree.elim_node]
    refine repC_lnode rfl ?_ (repC_pair (repC_numeral hF hwf hX l) (hl cs ih)) ?_
    side_goals

end Prims

/-! The constants. -/

/-- A tree fold into functions, at an argument, is the fold of the step's applications to it,
when each step at the argument applies a step to its children's values there. -/
theorem elim_apply_eq {β γ : Type} (G : ℕ → List (β → γ) → β → γ) (H : ℕ → List γ → γ) (b : β)
    (hG : ∀ l fs, G l fs b = H l (fs.map (· b))) :
    ∀ t : RoseTree ℕ, RoseTree.elim G t b = RoseTree.elim H t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [RoseTree.elim_node, RoseTree.elim_node, hG, List.map_map]
    exact congrArg _ (List.map_congr_left ih)

/-- The side goals of a representation at types of the kernel's translation: their typing, from
the hypotheses', and their values. -/
scoped macro (name := kSideGoals) "kside_goals" : tactic =>
  `(tactic| all_goals first
    | (simp only [Internal.isTy_exp, Internal.isTy_prod, Internal.isTy_list, Internal.isTy_one,
        Bool.and_self, Bool.and_true, *]; done)
    | (is_ty; done)
    | (obj_val; done))

section Consts

open Internal (repC_var repC_lam repC_app repC_pair repC_fst repC_snd repC_nil repC_lnode
  repC_star repC_listRec repC_roseRec repC_call₀ repC_call₁ repC_call₂ repC_call₃ compiled_language
  envRep_idt)

variable {defs defsF : List Defn} (hF : compileDefs (globals defsF) = some ds)
  (hwf : PartialHorn.DefnsWF sig ds) {X : Tree} {e : List (Tree × Tree)} {S A : Type}
  {R : S → A → Prop} (hX : ObjVal [] (unfoldTerm sig ds X) A) {T : Kernel.Tree} {a : Tree}
  (hT : ty T = some a)
include hF hwf hX hT

/-- Iteration at a type represents the kernel's iteration. -/
theorem repC_iterT :
    RepC (globals defs) 0 ds [] (iterT a) X e (exp (exp a a) (exp a (exp treeTy a))) R
      (KRel (Kernel.iterTy T)) fun _ ↦ Kernel.iterDen T := by
  obtain ⟨hi, ho, hv⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) T hT
  have hv' : ObjVal [] a (MTy T) := by rwa [unfoldTerm_of_opsBelow ds sig a ho] at hv
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  obtain ⟨fi, hfi⟩ := compiled_language hF (k := D.iter) (d := lib[D.iter]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_
    (repC_call₃ (τ' := [MTy T]) (a := a) rfl rfl hwf hfi rfl (by simp [hi]) (by simp [ho])
      (.cons hv' .nil) rfl rfl
      (represents_iter (rep_iter hF hfi (KRel T)))
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
        (represents_lab (rep_lab hF hfl)) (repC_var0 ?_ ?_))
      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 hX ?_)))
      (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))))) fun _ ↦ rfl
  kside_goals

/-- Case analysis of lists at two types represents the kernel's case analysis. -/
theorem repC_lcaseT {U : Kernel.Tree} {b : Tree} (hU : ty U = some b) :
    RepC (globals defs) 0 ds [] (lcaseT a b) X e
      (exp (list a) (exp b (exp (exp a (exp (list a) b)) b))) R
      (KRel (Kernel.lcaseTy T U)) fun _ ↦ Kernel.lcaseDen T U := by
  obtain ⟨hi, ho, hv⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) T hT
  obtain ⟨hi', ho', hu⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) U hU
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lcase) (d := lib[D.lcase]) rfl
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_
    (repC_call₃ (τ' := [MTy T, MTy U]) (a := b) rfl rfl hwf hfl rfl (by simp [hi, hi'])
      (by simp [ho, ho']) (.cons (objVal_ty hT) (.cons (objVal_ty hU) .nil)) rfl rfl
      (rep_lcase hF hfl (KRel T) (KRel U))
      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 hX ?_)))
      (repC_lam ?_ ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
      (repC_var0 ?_ ?_))))) ?hc
  case hc =>
    intro s
    funext (xs : List (Kernel.Ty.den T)) n c
    rcases xs with _ | ⟨x, xs⟩ <;> rfl
  kside_goals

omit hF hwf in
/-- The right fold of lists at two types represents the kernel's right fold. -/
theorem repC_foldrT {U : Kernel.Tree} {b : Tree} (hU : ty U = some b) :
    RepC (globals defs) 0 ds [] (foldrT a b) X e
      (exp (exp a (exp b b)) (exp b (exp (list a) b))) R
      (KRel (Kernel.foldrTy T U)) fun _ ↦ Kernel.foldrDen T U := by
  obtain ⟨hi, ho, hv⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) T hT
  obtain ⟨hi', ho', hu⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) U hU
  let RV := Rep.exp (Rep.prod (KRel (Kernel.tArrow T (Kernel.tArrow U U))) (KRel U)) (KRel U)
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_
    (repC_app (repC_listRec (repC_var0 ?_ ?_)
        (repC_lam ?_ ?_ ?_ (repC_snd (repC_var0 ?_ ?_) ?_ ?_))
        (repC_lam ?_ ?_ ?_ (repC_app (repC_app (repC_fst (repC_var0 ?_ ?_) ?_ ?_)
            (repC_varS ?_ ?_ (repC_var (Internal.envRep_listStep ?_ ?_ (KRel T) RV) rfl)) ?_ ?_)
          (repC_app (repC_varS ?_ ?_ (repC_var (Internal.envRep_listStep ?_ ?_ (KRel T) RV) rfl))
            (repC_var0 ?_ ?_) ?_ ?_) ?_ ?_)) ?_)
      (repC_pair (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 hX ?_)))
        (repC_varS ?_ ?_ (repC_var0 ?_ ?_))) ?_ ?_)))) ?hc
  case hc =>
    intro s
    funext g z (xs : List (Kernel.Ty.den T))
    refine congrFun (foldr_eq _ _ (fun xs p ↦ xs.foldr p.1 p.2) rfl ?_ xs) (g, z)
    exact fun _ _ ↦ rfl
  kside_goals

/-- The fold of trees at a type represents the kernel's fold of trees. -/
theorem repC_foldT :
    RepC (globals defs) 0 ds [] (foldT a) X e
      (exp (exp treeTy (exp (list a) a)) (exp treeTy a)) R
      (KRel (Kernel.foldTy T)) fun _ ↦ Kernel.foldDen T := by
  obtain ⟨hi, ho, hv⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) T hT
  have hF' : ty (Kernel.tArrow Kernel.tT (Kernel.tArrow (Kernel.tList T) T)) =
      some (exp treeTy (exp (list a) a)) := by simp [hT]
  obtain ⟨hFi, hFo, -⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) _ hF'
  obtain ⟨fm, hfm⟩ := compiled_language hF (k := D.mapApp) (d := lib[D.mapApp]) rfl
  let RF := KRel (Kernel.tArrow Kernel.tT (Kernel.tArrow (Kernel.tList T) T))
  let RP := Rep.prod RN (Rep.list (Rep.exp RF (KRel T)))
  refine repC_congr (repC_lam ?_ hX ?_ (repC_lam ?_ ?_ ?_ (repC_app (repC_roseRec ?_
      (repC_var0 ?_ ?_)
      (repC_lam ?_ ?_ ?_ (repC_app (repC_app (repC_var0 ?_ ?_)
          (repC_leaf ?_ (repC_fst (repC_varS ?_ ?_ (repC_var (envRep_idt ?_ RP) rfl)) ?_ ?_)) ?_ ?_)
        (repC_call₂ (τ' := [MTy (Kernel.tArrow Kernel.tT (Kernel.tArrow (Kernel.tList T) T)),
            MTy T]) (a := list a) rfl rfl hwf hfm rfl (by simp [hFi, hi]) (by simp [hFo, ho])
          (.cons (objVal_ty hF') (.cons (objVal_ty hT) .nil)) rfl rfl
          (rep_mapApp hF hfm RF (KRel T))
          (repC_snd (repC_varS ?_ ?_ (repC_var (envRep_idt ?_ RP) rfl)) ?_ ?_) (repC_var0 ?_ ?_))
        ?_ ?_)) ?_)
    (repC_varS ?_ ?_ (repC_var0 hX ?_)) ?_ ?_))) ?hc
  case hc =>
    intro s
    funext f (t : Kernel.Tree)
    refine elim_apply_eq _ (fun l rs ↦ f (Kernel.leaf l) rs) f ?_ t
    exact fun _ _ ↦ rfl
  kside_goals

end Consts

/-! The translation of terms, node by node. -/

/-- The translation of a node: the translation's step at the node's children. -/
theorem term_node (gt Γ : List Tree) (l : ℕ) (cs : List Kernel.Tree) :
    term gt Γ (RoseTree.node l cs) =
      termStep l (cs.map fun c ↦ (c, RoseTree.para termStep c)) gt Γ := by
  simp only [term, RoseTree.para_node]

/-- The children of a node, paired with their translations, when they are one child. -/
theorem map_tr_eq_one {cs : List Kernel.Tree} {x : Kernel.Tree} {s : Tr}
    (h : cs.map (fun c ↦ (c, RoseTree.para termStep c)) = [(x, s)]) :
    cs = [x] ∧ s = RoseTree.para termStep x := by
  obtain ⟨c, _, rfl, hc, hnil⟩ := List.map_eq_cons_iff.mp h
  obtain rfl := List.map_eq_nil_iff.mp hnil
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl⟩

/-- The children of a node, paired with their translations, when they are two children. -/
theorem map_tr_eq_two {cs : List Kernel.Tree} {x y : Kernel.Tree} {s t : Tr}
    (h : cs.map (fun c ↦ (c, RoseTree.para termStep c)) = [(x, s), (y, t)]) :
    cs = [x, y] ∧ s = RoseTree.para termStep x ∧ t = RoseTree.para termStep y := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl⟩ := map_tr_eq_one h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl⟩

/-- The children of a node, paired with their translations, when they are three children. -/
theorem map_tr_eq_three {cs : List Kernel.Tree} {x y z : Kernel.Tree} {s t u : Tr}
    (h : cs.map (fun c ↦ (c, RoseTree.para termStep c)) = [(x, s), (y, t), (z, u)]) :
    cs = [x, y, z] ∧ s = RoseTree.para termStep x ∧ t = RoseTree.para termStep y ∧
      u = RoseTree.para termStep z := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A variable of a context's type is one the kernel looks up. -/
theorem ctx_var_of_getElem (Γ : Kernel.Ctx) : ∀ (i : ℕ) (T : Kernel.Tree), Γ[i]? = some T →
    ∃ d, Γ.var i = some ⟨T, d⟩ :=
  List.rec (fun _ _ h ↦ nomatch h) (fun A Γ ih i T h ↦ by
    rcases i with _ | i
    · obtain rfl := Option.some.inj h
      exact ⟨Prod.fst, rfl⟩
    · obtain ⟨d, hd⟩ := ih i T h
      exact ⟨d ∘ Prod.snd, by simp only [Kernel.Ctx.var] at hd ⊢; rw [hd]; rfl⟩) Γ

/-- A node of two children is the kernel's node over the vector of them. -/
theorem node_two (l : ℕ) (x y : Kernel.Tree) : RoseTree.node l [x, y] = Kernel.node2 l x y :=
  RoseTree.node_eq_mk _ _ rfl _ fun i ↦ match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- The parts of a function type are its domain and codomain. -/
theorem eq_of_arrowParts {F A B : Kernel.Tree} (h : arrowParts F = some (A, B)) :
    F = Kernel.tArrow A B := by
  rw [arrowParts] at h
  split_ifs at h with hl
  split at h
  next x y hcs =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [← RoseTree.node_label_children F, hl, hcs, node_two]
    rfl
  next => exact nomatch h

/-- The parts of a product type are its factors. -/
theorem eq_of_prodParts {P A B : Kernel.Tree} (h : prodParts P = some (A, B)) :
    P = Kernel.tProd A B := by
  rw [prodParts] at h
  split_ifs at h with hl
  split at h
  next x y hcs =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [← RoseTree.node_label_children P, hl, hcs, node_two]
    rfl
  next => exact nomatch h

/-- The part of a list type is its elements' type. -/
theorem eq_of_listPart {L A : Kernel.Tree} (h : listPart L = some A) : L = Kernel.tList A := by
  rw [listPart] at h
  split_ifs at h with hl
  split at h
  next x hcs =>
    obtain rfl := Option.some.inj h
    rw [← RoseTree.node_label_children L, hl, hcs]
    exact RoseTree.node_eq_mk _ _ rfl _ fun i ↦ match i with | ⟨0, _⟩ => rfl
  next => exact nomatch h

/-! The fundamental lemma. -/

/-- The globals of a kernel program represented by the definitions after the translation's
library: each global's type has a translation, and its definition, of no parameters, compiles to
an arrow that represents its value. -/
def GlobRep (defs : List Defn) (ds : List PartialHorn.Defn) (G : List Kernel.Glob) : Prop :=
  ∀ n g, G[n]? = some g → ∃ a d fk, ty g.1 = some a ∧
    (globals defs).defs[lib.length + n]? = some (.language d) ∧ d.arity = 0 ∧ d.params = [] ∧
    PartialHorn.subst [] d.type = a ∧
    ds[lib.length + n]? = some ⟨List.replicate d.arity obj, arr, fk⟩ ∧
    Represents [] (unfoldTerm sig ds fk) Rep.unit (KRel g.1) fun _ ↦ g.2

section Fundamental

variable {defs defsF : List Defn} (hF : compileDefs (globals defsF) = some ds)
  (hwf : PartialHorn.DefnsWF sig ds) {G : List Kernel.Glob} (hG : GlobRep defs ds G)
include hF hwf hG

/-- The fundamental lemma: a kernel term's translation, in a represented context, has the type the
kernel infers, and represents the term's denotation. -/
theorem repC_term : ∀ (t : Kernel.Tree) (Γ : Kernel.Ctx) {X : Tree} {e : List (Tree × Tree)}
    {S A : Type} {R : S → A → Prop} {proj : S → Γ.den},
    CtxRep (globals defs) ds Γ X e R proj → ∀ {T : Kernel.Tree} {u : Term},
      term (G.map (·.1)) Γ t = some (T, u) → ∃ d a, Kernel.infer G Γ t = some ⟨T, d⟩ ∧
        ty T = some a ∧ RepC (globals defs) 0 ds [] u X e a R (KRel T) (d ∘ proj) :=
  RoseTree.ind fun l cs ih Γ X e S A R proj hΓ T u h ↦ by
    rw [term_node] at h
    unfold termStep at h
    rw [Kernel.infer_node]
    have hX := hΓ.1
    split at h
    · -- a variable
      rename_i n x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨T', hT', rfl, rfl⟩ := h
      obtain ⟨d, hd⟩ := ctx_var_of_getElem Γ _ T' hT'
      obtain ⟨a, ha, hr⟩ := hΓ.2 _ _ hd
      exact ⟨d, a, hd, ha, hr⟩
    · -- an abstraction
      rename_i A' x body b hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      split_ifs at h with hA
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨B, t⟩, hb, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl, rfl⟩ := h
      obtain ⟨d, b', hd, hb', hr⟩ := ih body (by simp) (A' :: Γ) (ctxRep_cons hΓ ha) hb
      obtain ⟨hia, -, hva⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) A' ha
      refine ⟨fun e x ↦ d (x, e), exp a b', ?_, by simp [ha, hb'], Internal.repC_lam hia hX hva hr⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, hA, ↓reduceIte]
      rw [show RoseTree.para Kernel.inferStep body G (A' :: Γ) = some ⟨B, d⟩ from hd]
      rfl
    · -- an application
      rename_i y f z x hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨F, tf⟩, hf, h⟩ := h
      simp only at h
      obtain ⟨⟨X', tx⟩, hx, h⟩ := h
      simp only at h
      obtain ⟨⟨A', B'⟩, hAB, h⟩ := h
      split_ifs at h with hXA
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hXA
      obtain rfl := eq_of_arrowParts hAB
      obtain ⟨df, af, hdf, haf, hrf⟩ := ih y (by simp) Γ hΓ hf
      obtain ⟨dx, ax, hdx, hax, hrx⟩ := ih z (by simp) Γ hΓ hx
      simp only [ty_tArrow, hax, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at haf
      obtain ⟨b, hb, rfl⟩ := haf
      refine ⟨fun e ↦ df e (dx e), b, ?_, hb, repC_congr (Internal.repC_app hrf hrx
        (objVal_ty' hax) (objVal_ty' hb)) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hdf,
        show RoseTree.para Kernel.inferStep z G Γ = _ from hdx]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show Kernel.Ty.arrow? (Kernel.tArrow X' B') = some ⟨X', B', rfl⟩ from rfl,
        Option.bind_some, dite_eq_left_of_eq_true (eq_self X')]
      rfl
    · -- the unit value
      rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨fun _ ↦ (), one, rfl, rfl, Internal.repC_star hX R⟩
    · -- a pair
      rename_i y a' z b' hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨A', ta⟩, ha, h⟩ := h
      simp only at h
      obtain ⟨⟨B', tb⟩, hb, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨da, aa, hda, haa, hra⟩ := ih y (by simp) Γ hΓ ha
      obtain ⟨db, ab, hdb, hab, hrb⟩ := ih z (by simp) Γ hΓ hb
      refine ⟨fun e ↦ (da e, db e), prod aa ab, ?_, by simp [haa, hab],
        repC_congr (Internal.repC_pair hra hrb) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hda,
        show RoseTree.para Kernel.inferStep z G Γ = _ from hdb]
      rfl
    · -- a first projection
      rename_i y p hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨P, tp⟩, hp, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨A', B'⟩, hAB, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain rfl := eq_of_prodParts hAB
      obtain ⟨dp, ap, hdp, hap, hrp⟩ := ih y (by simp) Γ hΓ hp
      simp only [ty_tProd, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hap
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hap
      refine ⟨fun e ↦ (dp e).1, a₁, ?_, ha₁, repC_congr (Internal.repC_fst hrp (objVal_ty' ha₁)
        (objVal_ty' ha₂)) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hdp]
      rfl
    · -- a second projection
      rename_i y p hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨P, tp⟩, hp, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨A', B'⟩, hAB, h⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain rfl := eq_of_prodParts hAB
      obtain ⟨dp, ap, hdp, hap, hrp⟩ := ih y (by simp) Γ hΓ hp
      simp only [ty_tProd, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hap
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hap
      refine ⟨fun e ↦ (dp e).2, a₂, ?_, ha₂, repC_congr (Internal.repC_snd hrp (objVal_ty' ha₁)
        (objVal_ty' ha₂)) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hdp]
      rfl
    · -- a quoted tree
      rename_i t' x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨fun _ ↦ t', treeTy, rfl, rfl, repC_quote hF hwf hX t'⟩
    · -- a conditional
      rename_i y c z a' w b' hcs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := map_tr_eq_three hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨C, tc⟩, hc, h⟩ := h
      simp only at h
      obtain ⟨⟨A', ta⟩, ha, h⟩ := h
      simp only at h
      obtain ⟨⟨B', tb⟩, hb, h⟩ := h
      split_ifs at h with hCB
      obtain ⟨rfl, rfl⟩ := hCB
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, haty, rfl, rfl⟩ := h
      obtain ⟨dc, ac, hdc, hac, hrc⟩ := ih y (by simp) Γ hΓ hc
      obtain ⟨da, aa, hda, haa, hra⟩ := ih z (by simp) Γ hΓ ha
      obtain ⟨db, ab, hdb, hab, hrb⟩ := ih w (by simp) Γ hΓ hb
      obtain rfl : aa = a := Option.some.inj (haa.symm.trans haty)
      obtain rfl : ab = aa := Option.some.inj (hab.symm.trans haty)
      obtain rfl : ac = treeTy := Option.some.inj (hac.symm.trans ty_tT)
      obtain ⟨hia, hoa, -⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) B' haty
      obtain ⟨fc, hfc⟩ := Internal.compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
      obtain ⟨fl, hfl⟩ := Internal.compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
      refine ⟨fun e ↦ if (dc e).label ≠ 0 then da e else db e, ab, ?_, haty,
        repC_congr (Internal.repC_call₃ (τ' := [MTy B']) (a := ab) rfl rfl hwf hfc rfl
          (by simp [hia]) (by simp [hoa]) (.cons (objVal_ty haty) .nil) rfl rfl
          (represents_cond (rep_cond hF hfc (KRel B')))
          (Internal.repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp)
            .nil rfl rfl (represents_lab (rep_lab hF hfl)) hrc) hra hrb) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hdc,
        show RoseTree.para Kernel.inferStep z G Γ = _ from hda,
        show RoseTree.para Kernel.inferStep w G Γ = _ from hdb]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rfl
    · -- the fold of trees
      rename_i A' x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl, rfl⟩ := h
      refine ⟨fun _ ↦ Kernel.foldDen A', _, ?_, by simp [Kernel.foldTy, ha],
        repC_foldT hF hwf hX ha⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, isTy_of_ty A' ha, ↓reduceIte]
      rfl
    · -- iteration
      rename_i A' x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl, rfl⟩ := h
      refine ⟨fun _ ↦ Kernel.iterDen A', _, ?_, by simp [Kernel.iterTy, ha],
        repC_iterT hF hwf hX ha⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, isTy_of_ty A' ha, ↓reduceIte]
      rfl
    · -- the empty list
      rename_i A' x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl, rfl⟩ := h
      obtain ⟨hia, -, hva⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) A' ha
      refine ⟨fun _ ↦ [], list a, ?_, by simp [ha],
        Internal.repC_nil rfl hia (Internal.repC_star hX _) hva (KRel A')⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, isTy_of_ty A' ha, ↓reduceIte]
      rfl
    · -- a list construction
      rename_i y x z xs hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨X', tx⟩, hx, h⟩ := h
      simp only at h
      obtain ⟨⟨L, txs⟩, hxs, h⟩ := h
      simp only at h
      obtain ⟨A', hL, h⟩ := h
      split_ifs at h with hXA
      subst hXA
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, rfl, rfl⟩ := h
      obtain rfl := eq_of_listPart hL
      obtain ⟨dx, ax, hdx, hax, hrx⟩ := ih y (by simp) Γ hΓ hx
      obtain ⟨dxs, axs, hdxs, haxs, hrxs⟩ := ih z (by simp) Γ hΓ hxs
      obtain rfl : ax = a := Option.some.inj (hax.symm.trans ha)
      obtain rfl : list ax = axs := by simpa [ha] using haxs
      obtain ⟨hia, -, hva⟩ := ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := ds) X' ha
      refine ⟨fun e ↦ dx e :: dxs e, list ax, ?_, by simp [ha], repC_congr
        (Internal.repC_cons rfl hia (Internal.repC_pair hrx hrxs) hva) fun _ ↦ rfl⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep]
      rw [show RoseTree.para Kernel.inferStep y G Γ = _ from hdx,
        show RoseTree.para Kernel.inferStep z G Γ = _ from hdxs]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [show Kernel.Ty.list? (Kernel.tList X') = some ⟨X', rfl⟩ from rfl, Option.bind_some,
        dite_eq_left_of_eq_true (eq_self X')]
      rfl
    · -- the right fold of lists
      rename_i A' x B' y hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
      refine ⟨fun _ ↦ Kernel.foldrDen A' B', _, ?_, by simp [Kernel.foldrTy, ha, hb],
        repC_foldrT hX ha hb⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, isTy_of_ty A' ha, isTy_of_ty B' hb,
        Bool.and_self, ↓reduceIte]
      rfl
    · -- a primitive
      rename_i k x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨g, hg, u', hu', rfl, rfl⟩ := h
      obtain ⟨a, ha, hr⟩ := repC_primT hF hwf hX hg hu'
      refine ⟨fun _ ↦ g.2, a, ?_, ha, hr⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, hg]
      rfl
    · -- a reference to a global
      rename_i n x hcs
      obtain ⟨rfl, rfl⟩ := map_tr_eq_one hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq, List.getElem?_map, Option.map_eq_some_iff] at h
      obtain ⟨T', ⟨g, hg, rfl⟩, rfl, rfl⟩ := h
      obtain ⟨a, d, fk, ha, hk, har, hpar, hty, hdk, hr⟩ := hG _ g hg
      refine ⟨fun _ ↦ g.2, a, ?_, ha, Internal.repC_call₀ rfl hk hwf hdk har hpar hty hX hr⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, hg]
      rfl
    · -- case analysis of lists
      rename_i A' x B' y hcs
      obtain ⟨rfl, rfl, rfl⟩ := map_tr_eq_two hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨a, ha, b, hb, rfl, rfl⟩ := h
      refine ⟨fun _ ↦ Kernel.lcaseDen A' B', _, ?_, by simp [Kernel.lcaseTy, ha, hb],
        repC_lcaseT hF hwf hX ha hb⟩
      simp only [List.map_cons, List.map_nil, Kernel.inferStep, isTy_of_ty A' ha, isTy_of_ty B' hb,
        Bool.and_self, ↓reduceIte]
      rfl
    · exact nomatch h

end Fundamental

end Geb.FreeTopos.Translation

end
