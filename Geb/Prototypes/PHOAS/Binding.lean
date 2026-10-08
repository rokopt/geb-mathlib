/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Context extension and binding layers

The binding-signature operator is a sum of products of context extensions of a family.
It is the arbitrary-arity form of the operator in {cite}`FiorePlotkinTuri1999`, Section 2.
At the identity family it selects variables; at a family of terms its children are
whole terms in extended contexts.

## Main definitions

* {lit}`ContextExtension` precomposes a family with adjoining a type of bound variables.
* {lit}`BindingNode` is the operator {lit}`H(M)(Γ) = Σ a, Π b, M(Γ ⊕ C(a,b))`.
* {lit}`BindingLayer` adjoins the variable summand to that operator.

## References

* {cite}`FiorePlotkinTuri1999`

## Tags

PHOAS, binding signature, context extension, functor category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

universe uA uB u v

/-- A family evaluated after adjoining the bound variables to its context. -/
abbrev ContextExtension (M : Type u → Type v) (C Γ : Type u) := M (Γ ⊕ C)

/-- An operation with one extended-context child at each inner position. -/
abbrev BindingNode (P : PProfunctor.{uA, uB, u}) (M : Type u → Type v) (Γ : Type u) :=
  (a : P.A) × ((b : (P.B a).A) → ContextExtension M ((P.B a).B b) Γ)

/-- A context variable or a binding operation with extended-context children. -/
abbrev BindingLayer (P : PProfunctor.{uA, uB, u}) (M : Type u → Type v) (Γ : Type u) :=
  Γ ⊕ P.BindingNode M Γ

end Geb.PHOAS.PProfunctor
