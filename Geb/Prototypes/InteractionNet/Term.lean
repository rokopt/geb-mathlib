/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Cslib.Foundations.Data.PFunctor.Free
public import Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Terms of the interaction calculus

A term names a wire or an agent whose auxiliary ports carry terms. Its root is the agent's
principal port. The syntax is the free monad of the polynomial given by the agents and their
arities: substitution is that monad's binding operation. Equations connect roots, and a list
of equations together with an ordered interface represents a net.

These are the terms and equations of the interaction calculus, as presented in
{cite}`HassanMackieSato2015`, Section 3. The syntax permits arbitrary occurrences of names;
linearity is a condition on a whole configuration or rule, not on an isolated subtree.

## Main definitions

* {lit}`Term` — terms over agents with prescribed arities and a type of wire names.
* {lit}`Term.names` — the occurrences of wire names, in port order.
* {lit}`Term.subst` — simultaneous substitution at the wire names.
* {lit}`Equation` — two roots joined by a wire.

## Main statements

* {lit}`Term.subst_var`, {lit}`Term.subst_agent` — substitution's computation rules.
* {lit}`Term.names_subst` — substitution replaces each occurrence by its term's occurrences.

## References

* {cite}`HassanMackieSato2015`, Section 3.

## Tags

interaction net, interaction calculus, polynomial functor, free monad, substitution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν μ : Type}

/-- The polynomial of agents and their auxiliary ports. -/
abbrev signature (arity : α → ℕ) : PFunctor := ⟨α, fun a ↦ Fin (arity a)⟩

/-- A wire name or an agent over its auxiliary ports. -/
abbrev Term (arity : α → ℕ) (ν : Type) : Type := (signature arity).FreeM ν

namespace Term

variable {arity : α → ℕ}

/-- A wire named by {lit}`x`. -/
def var (x : ν) : Term arity ν := .pure x

/-- An agent, with one term at each auxiliary port. -/
def agent (a : α) (ts : Fin (arity a) → Term arity ν) : Term arity ν := .liftBind a ts

/-- All occurrences of names, in the order of the auxiliary ports. -/
def names : Term arity ν → List ν :=
  PFunctor.FreeM.rec (fun x ↦ [x]) (fun _ _ ns ↦ (List.ofFn ns).flatten)

/-- The names of a wire. -/
@[simp] theorem names_var (x : ν) : (var (arity := arity) x).names = [x] := rfl

/-- The names of an agent are those of its ports, concatenated in order. -/
@[simp] theorem names_agent (a : α) (ts : Fin (arity a) → Term arity ν) :
    (agent a ts).names = (List.ofFn fun i ↦ (ts i).names).flatten := rfl

/-- Simultaneous substitution of terms for wire names. -/
def subst (σ : ν → Term arity μ) (t : Term arity ν) : Term arity μ :=
  PFunctor.FreeM.bind t σ

/-- Substitution at a wire reads its replacement. -/
@[simp] theorem subst_var (σ : ν → Term arity μ) (x : ν) : (var x).subst σ = σ x := rfl

/-- Substitution preserves an agent and acts at its auxiliary ports. -/
@[simp] theorem subst_agent (σ : ν → Term arity μ) (a : α)
    (ts : Fin (arity a) → Term arity ν) :
    (agent a ts).subst σ = agent a (fun i ↦ (ts i).subst σ) := rfl

/-- Substitution replaces each occurrence by the occurrences of its replacement. -/
theorem names_subst (σ : ν → Term arity μ) (t : Term arity ν) :
    (t.subst σ).names = t.names.flatMap (fun x ↦ (σ x).names) :=
  PFunctor.FreeM.rec (fun _ ↦ by simp [subst, names, PFunctor.FreeM.bind])
    (fun a ts ih ↦ by
      change (List.ofFn fun i ↦ names (subst σ (ts i))).flatten =
        (List.ofFn fun i ↦ names (ts i)).flatten.flatMap (fun x ↦ (σ x).names)
      simp only [ih]
      simp [List.flatMap, List.map_flatten, List.flatten_flatten, List.map_ofFn,
        Function.comp_def]) t

end Term

/-- An equation joins the principal roots of its terms. -/
abbrev Equation (arity : α → ℕ) (ν : Type) : Type := Term arity ν × Term arity ν

end Geb.InteractionNet

end
