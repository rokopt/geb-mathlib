/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion

set_option doc.verso true in
/-!
# The soundness's conclusion at the type of trees and at a datatype

The conclusion of the soundness of a whole program of the datatype language's stage-1 compiler
relates each definition the typing gives a type to the type, by a relation that is a fold of
the type ({lit}`DatatypeRelation.DRel`). At the type of trees and at a datatype the relation
refers to no relation at another type: a value is related at the type of trees when it is a
tree's quotation, and at a datatype when it is the quotation of a member of the datatype, by
the context's markers. Of a definition of one of those types the conclusion therefore states a
fact about the evaluator alone: the evaluation of its term converges to a tree's quotation,
and, at a datatype, the tree is a member of it.

## Main statements

* {lit}`relAt_fst` — the relation's fold rebuilds the type.
* {lit}`dRel_tree`, {lit}`dRel_data` — the relation at the type of trees and at a datatype.
* {lit}`globRel_tree`, {lit}`globRel_data` — a definition of the type of trees evaluates to a
  tree's quotation, and a definition of a datatype's type to the quotation of a member.

## Tags

internal language, logical relation, datatypes, evaluator, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeMembers

open Geb
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (Env)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements (EvalFns Conv Level)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation (Ctx RelV relStep relBody labelIs
  DRel)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion (GlobRel)

/-- A function of the fuel that converges to a value of which a predicate holds converges to
one of which a predicate it implies holds. -/
theorem Conv.mono {just : Kernel.Tree → Kernel.Tree} {F : ℕ → Kernel.Tree}
    {P Q : Kernel.Tree → Prop} (h : Conv just F P) (hpq : ∀ w, P w → Q w) : Conv just F Q :=
  let ⟨n, w, hw, hp⟩ := h
  ⟨n, w, hw, hpq w hp⟩

/-- The case of a label that is the label named. -/
theorem labelIs_eq {l k : ℕ} (h : l = k) (P Q : Prop) : labelIs l k P Q = P := by
  unfold labelIs
  rw [ite_eq_left h, ite_eq_left Nat.one_ne_zero]

/-- The case of a label that is not the label named. -/
theorem labelIs_ne {l k : ℕ} (h : l ≠ k) (P Q : Prop) : labelIs l k P Q = Q := by
  unfold labelIs
  rw [ite_eq_right h, ite_eq_right fun h' ↦ h' rfl]

variable (f : EvalFns)

/-- The value of the relation's fold at a type: the type rebuilt, and the relation at it. -/
abbrev relAt (A : Kernel.Tree) : RelV := RoseTree.elim (fun l cs ↦ relStep f (l, cs)) A

/-- The trees of the fold's values at a list of types are the types. -/
theorem foldr_relAt : ∀ cs : List Kernel.Tree, (∀ c ∈ cs, (relAt f c).1 = c) →
    (cs.map (relAt f)).foldr (fun x r ↦ x.1 :: r) [] = cs :=
  List.rec (fun _ ↦ rfl) fun c cs ih h ↦ by
    rw [List.map_cons, List.foldr_cons, h c List.mem_cons_self,
      ih fun x hx ↦ h x (List.mem_cons_of_mem c hx)]

/-- The relation's fold rebuilds the type. -/
theorem relAt_fst : ∀ A : Kernel.Tree, (relAt f A).1 = A :=
  RoseTree.ind fun l cs ih ↦ by
    rw [relAt, RoseTree.elim_node]
    exact congrArg (RoseTree.node l) (foldr_relAt f cs ih)

/-- The relation at a node of a type is the node's relation of its children's values. -/
theorem dRel_node (l : ℕ) (ts : List Kernel.Tree) (R : Ctx) (w : Kernel.Tree) :
    DRel f (RoseTree.node l ts) R w = relBody f l (ts.map (relAt f)) R w := by
  rw [DRel, RoseTree.elim_node]
  rfl

/-- A value is related at the type of trees exactly when it is a tree's quotation. -/
theorem dRel_tree {ts : List Kernel.Tree} {R : Ctx} {w : Kernel.Tree} :
    DRel f (RoseTree.node Kernel.Label.tyTree ts) R w ↔ ∃ t, w = f.valQuote t := by
  rw [dRel_node, relBody, labelIs_eq rfl]

/-- A value is related at a datatype exactly when it is the quotation of a member of the
datatype its first child's atom names, by the context's markers. -/
theorem dRel_data {a : Kernel.Tree} {ts : List Kernel.Tree} {R : Ctx} {w : Kernel.Tree} :
    DRel f (RoseTree.node 5 (a :: ts)) R w ↔
      ∃ t, w = f.valQuote t ∧ (f.memberOf R.2 (RoseTree.node 1 a.children) t).label ≠ 0 := by
  rw [dRel_node, relBody, labelIs_ne (by decide), labelIs_ne (by decide),
    labelIs_ne (by decide), labelIs_ne (by decide), labelIs_ne (by decide), labelIs_eq rfl]
  change (∃ t, w = f.valQuote t ∧
    (f.memberOf R.2 (RoseTree.node 1 (relAt f a).1.children) t).label ≠ 0) ↔ _
  rw [relAt_fst]

variable {f}

/-- A definition the typing environment gives the type of trees evaluates to a tree's
quotation. -/
theorem globRel_tree {R : Ctx} {E : Env} {names : List Kernel.Tree} (h : GlobRel f R E names)
    {n : Kernel.Tree} (hn : (f.isSome (f.lookupName n (f.envDefs E))).label ≠ 0)
    {ts : List Kernel.Tree}
    (hA : f.get (f.lookupName n (f.envDefs E)) = RoseTree.node Kernel.Label.tyTree ts) :
    ∃ i, f.indexOf n names = f.just i ∧ ∃ d, f.nth R.1 i = f.just d ∧
      Conv f.just (fun k ↦ (Level f R.1 k).1 [] d) fun w ↦ ∃ t, w = f.valQuote t := by
  obtain ⟨i, hi, d, hd, hc⟩ := h n hn
  rw [hA] at hc
  exact ⟨i, hi, d, hd, Conv.mono hc fun _ hw ↦ (dRel_tree f).mp hw⟩

/-- A definition the typing environment gives a datatype's type evaluates to the quotation of
a member of the datatype, by the context's markers. -/
theorem globRel_data {R : Ctx} {E : Env} {names : List Kernel.Tree} (h : GlobRel f R E names)
    {n : Kernel.Tree} (hn : (f.isSome (f.lookupName n (f.envDefs E))).label ≠ 0)
    {a : Kernel.Tree} {ts : List Kernel.Tree}
    (hA : f.get (f.lookupName n (f.envDefs E)) = RoseTree.node 5 (a :: ts)) :
    ∃ i, f.indexOf n names = f.just i ∧ ∃ d, f.nth R.1 i = f.just d ∧
      Conv f.just (fun k ↦ (Level f R.1 k).1 [] d) fun w ↦ ∃ t, w = f.valQuote t ∧
        (f.memberOf R.2 (RoseTree.node 1 a.children) t).label ≠ 0 := by
  obtain ⟨i, hi, d, hd, hc⟩ := h n hn
  rw [hA] at hc
  exact ⟨i, hi, d, hd, Conv.mono hc fun _ hw ↦ (dRel_data f).mp hw⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeMembers

end
