/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Initial
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Trees for scoped polynomial syntax

A scoped expression has an operation tree and a variable at each leaf. The context
of a leaf includes the variables bound along its path from the root. This gives a
representation without a compatibility proof, including arbitrarily nested operations.

The constructors form the initial algebra of {lit}`Id + H`, where
{lit}`H(M)(Γ) = Σ a, Π b, M(Γ ⊕ C(a,b))` is the context-extension operator. Equivalently,
this is the free {lit}`H`-algebra on the identity family, as in the binding-algebra
account of {cite}`FiorePlotkinTuri1999`, Section 2.

## Main definitions

* {lit}`Term` consists of an operation tree with variables in its extended leaf contexts.
* {lit}`Term.recOn` and {lit}`Term.fold` recurse through those contexts.
* {lit}`Scoped.equivTerm` represents compatible families by these trees.

## Main statements

* {lit}`Scoped.toScoped_toTerm` and {lit}`Scoped.toTerm_toScoped` prove both round trips.
* {lit}`Term.fold_node` computes a full expression from its extended-context children.

## Implementation notes

The shape uses an ordinary polynomial free monad whose directions are the child
positions. Its recursor supplies the dependent leaf labels and structural recursion;
no new recursive datatype is required. Binder variables occur in the labels, rather
than in the shape.
Contexts and binder arities belong to the universe over which scoped families quantify.
There is no finiteness assumption on the signature's arities.

## References

* {cite}`FiorePlotkinTuri1999`

## Tags

PHOAS, binding signature, context extension, initial algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

open PFunctor

universe uA uB u v

namespace Term

/-- The polynomial of operation positions and child positions, ignoring binder arities. -/
def shapeSignature (P : PProfunctor.{uA, uB, u}) : PFunctor.{uA, uB} :=
  ⟨P.A, fun a ↦ (P.B a).A⟩

/-- An operation tree with an unlabelled variable at each leaf. -/
abbrev Shape (P : PProfunctor.{uA, uB, u}) := (shapeSignature P).FreeM PUnit.{1}

/-- Leaf variables, each drawn from the context extended along its path. -/
def Labels {P : PProfunctor.{uA, uB, u}} (s : Shape P) : Type u → Type (max uB u) :=
  FreeM.rec (motive := fun _ ↦ Type u → Type (max uB u))
    (fun _ Γ ↦ ULift.{uB} Γ)
    (fun a _ ih Γ ↦ (b : (P.B a).A) → ih b (Γ ⊕ (P.B a).B b)) s

end Term

/-- Binding syntax represented by an operation tree and its extended-context leaf variables. -/
abbrev Term (P : PProfunctor.{uA, uB, u}) (Γ : Type u) :=
  (s : Term.Shape P) × Term.Labels s Γ

namespace Term

variable {P : PProfunctor.{uA, uB, u}} {Γ : Type u}

/-- A leaf labelled by an available variable. -/
def var (x : Γ) : P.Term Γ := ⟨.pure PUnit.unit, ULift.up x⟩

/-- A binding operation whose children are whole terms in their extended contexts. -/
def node (a : P.A) (k : (b : (P.B a).A) → P.Term (Γ ⊕ (P.B a).B b)) : P.Term Γ :=
  ⟨.liftBind a (fun b ↦ (k b).1), fun b ↦ (k b).2⟩

/-- Structural recursion with each child's context extended by its binder arity. -/
def recOn {motive : (Γ : Type u) → P.Term Γ → Sort v} (t : P.Term Γ)
    (onVar : ∀ Γ x, motive Γ (var x))
    (onNode : ∀ Γ a k, (∀ b, motive (Γ ⊕ (P.B a).B b) (k b)) → motive Γ (node a k)) :
    motive Γ t :=
  FreeM.rec (motive := fun s ↦ ∀ Γ (l : Labels s Γ), motive Γ ⟨s, l⟩)
    (fun _ Γ l ↦ onVar Γ l.down)
    (fun a k ih Γ l ↦ onNode Γ a (fun b ↦ ⟨k b, l b⟩) (fun b ↦ ih b _ (l b))) t.1 Γ t.2

/-- Interpret a tree using a variable map and extended-context operations. -/
def fold {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (t : P.Term Γ) : M Γ :=
  recOn (motive := fun Γ _ ↦ M Γ) t onVar (fun Γ a _ ih ↦ onNode Γ a ih)

/-- The tree fold interprets a context variable. -/
@[simp] theorem fold_var {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (x : Γ) : fold onVar onNode (var x) = onVar Γ x := rfl

/-- The tree fold interprets an operation after folding each extended-context child. -/
@[simp] theorem fold_node {M : Type u → Type v} (onVar : ∀ Γ, Γ → M Γ)
    (onNode : ∀ Γ a, ((b : (P.B a).A) → M (Γ ⊕ (P.B a).B b)) → M Γ)
    (a : P.A) (k : (b : (P.B a).A) → P.Term (Γ ⊕ (P.B a).B b)) :
    fold onVar onNode (node a k) = onNode Γ a (fun b ↦ fold onVar onNode (k b)) := rfl

/-- Interpret a tree as a compatible family of full pointwise free-monad expressions. -/
def toScoped (t : P.Term Γ) : P.Scoped.{uA, uB, u, u, u} Γ :=
  fold (fun _ ↦ Scoped.var) (fun _ ↦ Scoped.node) t

/-- Converting a leaf preserves its context variable. -/
@[simp] theorem toScoped_var (x : Γ) : (var (P := P) x).toScoped = Scoped.var x := rfl

/-- Converting an operation converts every extended-context child. -/
@[simp] theorem toScoped_node (a : P.A)
    (k : (b : (P.B a).A) → P.Term (Γ ⊕ (P.B a).B b)) :
    (node a k).toScoped = Scoped.node a (fun b ↦ (k b).toScoped) := rfl

end Term

namespace Scoped

variable {P : PProfunctor.{uA, uB, u}} {Γ : Type u}

/-- Extract the operation tree and extended-context variables of a scoped family. -/
def toTerm (t : P.Scoped.{uA, uB, u, u, u} Γ) : P.Term Γ :=
  fold (fun _ ↦ Term.var) (fun _ ↦ Term.node) t

/-- Extracting a tree and interpreting it recovers the original compatible family. -/
@[simp] theorem toScoped_toTerm (t : P.Scoped.{uA, uB, u, u, u} Γ) :
    t.toTerm.toScoped = t :=
  (fold_fusion (fun _ ↦ Term.var) (fun _ ↦ Term.node) (fun _ ↦ var) (fun _ ↦ node)
    (fun _ ↦ Term.toScoped) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) t).trans (fold_self t)

/-- Interpreting a tree and extracting its representation recovers the original tree. -/
@[simp] theorem toTerm_toScoped (t : P.Term Γ) : t.toScoped.toTerm = t := by
  refine Term.recOn (motive := fun Γ t ↦ toTerm t.toScoped = t) t ?_ ?_
  · intro Γ x
    rfl
  · intro Γ a k ih
    simp only [Term.toScoped_node, toTerm, fold_node]
    exact congrArg (Term.node a) (funext ih)

/-- Paranatural families into the pointwise free monad are full binding trees. -/
def equivTerm : P.Scoped.{uA, uB, u, u, u} Γ ≃ P.Term Γ where
  toFun := toTerm
  invFun := Term.toScoped
  left_inv := toScoped_toTerm
  right_inv := toTerm_toScoped

end Scoped

end Geb.PHOAS.PProfunctor
