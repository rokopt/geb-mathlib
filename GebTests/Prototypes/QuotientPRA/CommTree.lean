/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA -- shake: keep

/-!
# Tests for quotient presheaf polynomial functors: commutative binary trees

Binary trees modulo commutativity of the binary operation, as the quotient W-type of
the signature with a nullary `leaf` and a binary `node` and the one-step
equation `node x y = node y x`. The tests compute the endpoints of the
equation's witnesses and of a congruence witness, identify commuted trees in the
quotient, count leaves through the eliminator into an algebra satisfying the
equation, and apply the obstruction to a reflexivity constructor of fixed shape.

## Tags

prototype, quotient inductive type, W-type, presheaf, commutativity
-/

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Signature.CommTree

/-- The operations: a nullary leaf and a binary node. -/
inductive Op
  | leaf
  | node

/-- The arguments of an operation. -/
def arity : Op → Type
  | .leaf => PEmpty
  | .node => Bool

/-- The signature of binary trees. -/
def sig : PFunctor.{0, 0} := ⟨Op, arity⟩

/-- Commutativity of the node: `node x y = node y x`, with the variables
`false ↦ x`, `true ↦ y`. -/
def comm : Equations sig where
  E := PUnit
  V _ := Bool
  lhs _ := ⟨.node, id⟩
  rhs _ := ⟨.node, (! ·)⟩

/-- The quotient presheaf polynomial functor of commutative binary trees. -/
abbrev F := qpra sig comm

/-- The terms. -/
abbrev Term := F.W.obj ⟨objOf .zero⟩

/-- The witnesses. -/
abbrev Wit := F.W.obj ⟨objOf .one⟩

/-- The leaf. -/
def leaf : Term :=
  PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.leaf) fun g ↦ nomatch g)

/-- The node on two trees. -/
def node (x y : Term) : Term :=
  PresheafPFunctor.W.mk
    (freeNode (P := sig) (eqns := comm) F.W (.inl Op.node) fun b ↦ cond b y x)

/-- The witness of commutativity at two trees. -/
def swap (x y : Term) : Wit :=
  PresheafPFunctor.W.mk
    (freeNode (P := sig) (eqns := comm) F.W (.inr (.inr (⟨⟩, false))) fun b ↦ cond b y x)

/-- The source of a commutativity witness is the node on the trees in order. -/
theorem src_swap (x y : Term) : src F.W ⟨⟨⟩⟩ (swap x y) = node x y :=
  src_mk_freeNode_eqn (P := sig) (eqns := comm) ⟨⟩ false _

/-- The target of a commutativity witness is the node on the trees exchanged: the
equation's right side reads its first argument from the second variable. -/
theorem tgt_swap (x y : Term) : tgt F.W ⟨⟨⟩⟩ (swap x y) = node y x :=
  (tgt_mk_freeNode_eqn (P := sig) (eqns := comm) ⟨⟩ false _).trans
    (congrArg (fun ts ↦
        PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.node) ts))
      (funext fun b ↦ by cases b <;> rfl : (fun b : Bool ↦ cond (!b) y x) = fun b ↦ cond b x y))

/-- Commuted trees have the same class in the quotient. -/
theorem node_comm (x y : Term) : quotientMk F (node x y) = quotientMk F (node y x) := by
  rw [← src_swap, ← tgt_swap]
  exact quotientMk_src F (swap x y)

/-- The congruence of the node at witnesses between the left and the right arguments. -/
def congNode (e₁ e₂ : Wit) : Wit :=
  PresheafPFunctor.W.mk
    (freeNode (P := sig) (eqns := comm) F.W (.inr (.inl Op.node)) fun b ↦ cond b e₂ e₁)

/-- The congruence of the leaf: the reflexivity witness at the leaf. -/
def congLeaf : Wit :=
  PresheafPFunctor.W.mk
    (freeNode (P := sig) (eqns := comm) F.W (.inr (.inl Op.leaf)) fun g ↦ nomatch g)

/-- The source of a node's congruence witness is the node on the arguments' sources. -/
theorem src_congNode (e₁ e₂ : Wit) :
    src F.W ⟨⟨⟩⟩ (congNode e₁ e₂) = node (src F.W ⟨⟨⟩⟩ e₁) (src F.W ⟨⟨⟩⟩ e₂) :=
  (endpoint_mk_freeNode_cong (P := sig) (eqns := comm) false Op.node _).trans
    (congrArg (fun ts ↦
        PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.node) ts))
      (funext fun b ↦ by cases b <;> rfl))

/-- The target of a node's congruence witness is the node on the arguments' targets. -/
theorem tgt_congNode (e₁ e₂ : Wit) :
    tgt F.W ⟨⟨⟩⟩ (congNode e₁ e₂) = node (tgt F.W ⟨⟨⟩⟩ e₁) (tgt F.W ⟨⟨⟩⟩ e₂) :=
  (endpoint_mk_freeNode_cong (P := sig) (eqns := comm) true Op.node _).trans
    (congrArg (fun ts ↦
        PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.node) ts))
      (funext fun b ↦ by cases b <;> rfl))

/-- Both endpoints of the leaf's congruence witness are the leaf. -/
theorem src_congLeaf : src F.W ⟨⟨⟩⟩ congLeaf = leaf :=
  (endpoint_mk_freeNode_cong (P := sig) (eqns := comm) false Op.leaf _).trans
    (congrArg (fun ts ↦
        PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.leaf) ts))
      (funext fun g ↦ nomatch g))

/-- Both endpoints of the leaf's congruence witness are the leaf. -/
theorem tgt_congLeaf : tgt F.W ⟨⟨⟩⟩ congLeaf = leaf :=
  (endpoint_mk_freeNode_cong (P := sig) (eqns := comm) true Op.leaf _).trans
    (congrArg (fun ts ↦
        PresheafPFunctor.W.mk (freeNode (P := sig) (eqns := comm) F.W (.inl Op.leaf) ts))
      (funext fun g ↦ nomatch g))

/-- Commuting a subtree identifies trees in the quotient, through a congruence witness
whose other argument is the leaf's reflexivity witness. -/
theorem node_comm_left (x y : Term) :
    quotientMk F (node (node x y) leaf) = quotientMk F (node (node y x) leaf) := by
  have h := quotientMk_src F (congNode (swap x y) congLeaf)
  rwa [src_congNode, tgt_congNode, src_swap, tgt_swap, src_congLeaf, tgt_congLeaf] at h

/-- The number of leaves, an algebra of the signature. -/
def count : sig.Obj ℕ → ℕ
  | ⟨Op.leaf, _⟩ => 1
  | ⟨Op.node, f⟩ => f false + f true

/-- Counting leaves satisfies commutativity. -/
theorem count_satisfies : Satisfies (eqns := comm) count :=
  fun _ ρ ↦ Nat.add_comm (ρ false) (ρ true)

/-- The number of leaves of a class of trees. -/
def leaves : NatTrans (quotient F) (constPsh ℕ) := lift count count_satisfies

/-- The number of leaves of the class of a tree. -/
def leavesOf (t : Term) : ℕ := leaves.app ⟨⟨⟨⟩⟩⟩ (quotientMk F t)

/-- A leaf has one leaf. -/
theorem leavesOf_leaf : leavesOf leaf = 1 :=
  lift_intro count count_satisfies Op.leaf _

/-- A node has the leaves of its arguments. -/
theorem leavesOf_node (x y : Term) : leavesOf (node x y) = leavesOf x + leavesOf y :=
  lift_intro count count_satisfies Op.node _

example : leavesOf (node (node leaf leaf) leaf) = 3 := by
  rw [leavesOf_node, leavesOf_node, leavesOf_leaf]

/-- The leaf and a node differ in root shape. -/
theorem head_leaf_ne_head_node :
    head F.wHereditaryNaturality leaf ≠ head F.wHereditaryNaturality (node leaf leaf) := by
  change (Sum.inl Op.leaf : Shape sig comm) ≠ Sum.inl Op.node
  exact fun h ↦ nomatch h

-- Reflexivity is not a witness constructor of fixed shape here.
example : ¬ ∃ (ρ : F.Shape (eqObj ⟨⟨⟩⟩)) (refl : Term → Wit),
    (∀ t, head F.wHereditaryNaturality (refl t) = ρ.1) ∧ ∀ t, src F.W ⟨⟨⟩⟩ (refl t) = t :=
  no_uniform_refl F.wHereditaryNaturality leaf (node leaf leaf) head_leaf_ne_head_node

/-- The enumeration of the booleans. Built here because mathlib's enumerations of `Fin`
depend on `Classical.choice`. -/
def boolEquivFin : Bool ≃ Fin 2 where
  toFun b := cond b 1 0
  invFun i := Fin.cases false (fun _ ↦ true) i
  left_inv b := by cases b <;> rfl
  right_inv i := Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i

/-- The arguments of each operation are finite. -/
instance (a : sig.A) : FinEnum (sig.B a) :=
  match a with
  | .leaf =>
    { card := 0
      equiv :=
        { toFun := fun x ↦ (nomatch x)
          invFun := fun i ↦ i.elim0
          left_inv := fun x ↦ (nomatch x)
          right_inv := fun i ↦ i.elim0 }
      decEq := fun x ↦ (nomatch x) }
  | .node => { card := 2, equiv := boolEquivFin, decEq := inferInstanceAs (DecidableEq Bool) }

/-- The variables of commutativity are finite. -/
instance (e : comm.E) : FinEnum (comm.V e) :=
  { card := 2, equiv := boolEquivFin, decEq := inferInstanceAs (DecidableEq Bool) }

-- The classes of trees are an algebra satisfying commutativity.
example : Satisfies (eqns := comm) fun x : sig.Obj (Cls sig comm) ↦ opQ x.1 x.2 :=
  satisfies_opQ

-- The node on classes is the class of the node on representatives.
example (x y : Term) :
    opQ (P := sig) (eqns := comm) Op.node (fun b : Bool ↦ quotientMk F (cond b y x)) =
      quotientMk F (node x y) :=
  opQ_mk (P := sig) (eqns := comm) Op.node fun b : Bool ↦ cond b y x

-- Counting leaves is the only morphism of algebras from the classes to the algebra of
-- leaf counts: the classes are the initial algebra satisfying commutativity.
example (h : Cls sig comm → ℕ) (hh : ∀ a f, h (opQ a f) = count ⟨a, fun b ↦ h (f b)⟩)
    (q : Cls sig comm) : h q = leaves.app ⟨⟨⟨⟩⟩⟩ q :=
  eq_lift count_satisfies h hh q

end GebProto.QuotientPRA.Signature.CommTree
