/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.OneStep
public import GebTests.Prototypes.QuotientPRA.CommTree

set_option doc.verso true in
/-!
# Commutative binary trees as a presentation

The one-step equation of commutativity, {lit}`node x y = node y x`, as a presentation over
binary trees. Its classes of closed trees identify commuted trees, count leaves through the
value of classes, and correspond, under the isomorphism with the quotient W-type of the quotient
presheaf polynomial functor, to the classes of the corresponding W-type trees.

## Main definitions

* {lit}`commP` — the presentation of commutativity.
* {lit}`leafT`, {lit}`nodeT` — closed binary trees as terms of the free monad.

## Main statements

* {lit}`cls_nodeT_comm` — commuted trees have one class.
* {lit}`clsEquiv_leafT`, {lit}`clsEquiv_nodeT` — the isomorphism sends a tree's class to the
  class of the corresponding W-type tree.

## Tags

commutativity, equational presentation, quotient inductive type, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.OneStepTests

open PFunctor Geb.Definition.Presentation GebProto.QuotientPRA
  GebProto.QuotientPRA.Signature GebProto.QuotientPRA.Signature.CommTree

/-- Commutativity as a presentation. -/
abbrev commP : Presentation.{0, 0, 0} sig := ofEquations comm

/-- The leaf, as a closed term. -/
def leafT : sig.FreeM PEmpty := .liftBind Op.leaf fun x : PEmpty ↦ nomatch x

/-- The node on two closed terms. -/
def nodeT (x y : sig.FreeM PEmpty) : sig.FreeM PEmpty := .liftBind Op.node fun b : Bool ↦ cond b y x

/-- Commuted trees have one class. -/
theorem cls_nodeT_comm (x y : sig.FreeM PEmpty) : commP.cls (nodeT x y) = commP.cls (nodeT y x) :=
  (commP.cls_bind_lhs ⟨⟩ fun b : Bool ↦ cond b y x).trans
    (congrArg commP.cls (congrArg (FreeM.liftBind (P := sig) Op.node)
      (funext fun b ↦ by cases b <;> rfl)))

/-- A tree of three leaves. -/
def threeLeaves : sig.FreeM PEmpty := nodeT (nodeT leafT leafT) leafT

example : commP.lift count ((satisfies_ofEquations_iff comm count).mpr count_satisfies) PEmpty.elim
    (commP.cls threeLeaves) = 3 := rfl

/-- The class of a leaf goes to the class of the W-type leaf. -/
theorem clsEquiv_liftBind_leaf (k : PEmpty → sig.FreeM PEmpty) :
    clsEquiv comm (commP.cls (.liftBind Op.leaf k)) = quotientMk F leaf := by
  change opQ (P := sig) (eqns := comm) Op.leaf (fun g ↦ clsEquiv comm (commP.cls (k g))) = _
  exact (congrArg (opQ (P := sig) (eqns := comm) Op.leaf) (funext fun x : PEmpty ↦ nomatch x)).trans
    (opQ_mk (P := sig) (eqns := comm) Op.leaf fun g : PEmpty ↦ nomatch g)

/-- The class of the leaf goes to the class of the W-type leaf. -/
theorem clsEquiv_leafT : clsEquiv comm (commP.cls leafT) = quotientMk F leaf :=
  clsEquiv_liftBind_leaf _

/-- The class of a node goes to the class of the W-type node on the trees its arguments' classes
go to. -/
theorem clsEquiv_nodeT {x y : sig.FreeM PEmpty} {X Y : Term}
    (hx : clsEquiv comm (commP.cls x) = quotientMk F X)
    (hy : clsEquiv comm (commP.cls y) = quotientMk F Y) :
    clsEquiv comm (commP.cls (nodeT x y)) = quotientMk F (node X Y) := by
  change opQ (P := sig) (eqns := comm) Op.node
    (fun b ↦ clsEquiv comm (commP.cls (cond b y x))) = _
  refine (congrArg (opQ (P := sig) (eqns := comm) Op.node) (funext fun b ↦ ?_)).trans
    (opQ_mk Op.node fun b ↦ cond b Y X)
  cases b
  · exact hx
  · exact hy

example : clsEquiv comm (commP.cls threeLeaves) = quotientMk F (node (node leaf leaf) leaf) :=
  clsEquiv_nodeT (clsEquiv_nodeT clsEquiv_leafT clsEquiv_leafT) clsEquiv_leafT

end Geb.Definition.OneStepTests

end
