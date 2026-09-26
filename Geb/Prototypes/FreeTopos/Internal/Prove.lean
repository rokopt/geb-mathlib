/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A prover for the internal language

A prover, prototyped in Lean, that computes derivations the checker
{name}`Geb.FreeTopos.Internal.check` checks. It normalizes a term innermost first: it
normalizes the children, each in its own context, then applies at the root the first rule of a
list that applies, and normalizes the result. The rules are the language's equations and the
earlier theorems, whose instances it finds by matching their left sides. It proves an equation by
normalizing both sides to one term, and by induction on the innermost variable with a step it is
given, each premise by normalization; with the induction hypothesis, it normalizes the
hypothesis, cuts in the normal form, and rewrites the step by it. The prover is not trusted: a
derivation it computes is checked.

## Main definitions

* {lit}`NormRule` — a rule the normalizer applies at a term's root.
* {lit}`normalize` — the normal form of a term and its rewriting derivation.
* {lit}`byNorm`, {lit}`byNatInd`, {lit}`byListInd`, {lit}`byNatIndHyp`, {lit}`byListIndHyp` —
  the proofs of an equation.

## Tags

internal language, prover, normalization, induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

/-- A rule the normalizer applies at a term's root: one of the language's equations, the
equational theorem of an index at objects, whose instance is found by matching its left side, or
an equation among the hypotheses. -/
inductive NormRule where
  /-- A rule of the checker applied as it stands. -/
  | rule (r : Rule)
  /-- The unfolding of the definition of an index, and of no other. -/
  | delta (k : ℕ)
  /-- The equational theorem of an index at objects, from its left side to its right. -/
  | thm (j : ℕ) (θ : List Tree)
  /-- The equation among the hypotheses of an index, from its left side to its right. -/
  | hyp (i : ℕ)

/-- The matching of a pattern against a term, the pattern's variables below {lit}`m` bound in
the assignment: the extended assignment, or nothing when they do not match. -/
def matchTerm (p : Term) : Term → List (Option Term) → Option (List (Option Term)) :=
  RoseTree.para (fun l ps t σ ↦ match l with
    | .var i => match σ[i]? with
      | some none => some (σ.set i (some t))
      | some (some s) => if s = t then some σ else none
      | none => if t = Term.var i then some σ else none
    | l => if l = t.label ∧ ps.length = t.children.length then
        (ps.zip t.children).foldl (fun acc (q, u) ↦ acc.bind (q.2 u)) (some σ)
      else none) p

/-- The derivation of one rewriting after another, the identity left out. -/
def dTrans (d₁ d₂ : Deriv × Bool) : Deriv × Bool :=
  match d₁.2, d₂.2 with
  | false, _ => d₂
  | _, false => d₁
  | true, true => (RoseTree.node .trans [d₁.1, d₂.1], true)

/-- The identity derivation, marked as no rewriting. -/
def dRefl : Deriv × Bool := (RoseTree.node .refl [], false)

variable (G : Globals) (E : Array Thm) (n : ℕ)

/-- The first rule of a list that rewrites a term at its root: the result, and its derivation. -/
def rootRewrite (rs : List NormRule) (Γ : List Tree) (Φ : List Term) (t : Term) :
    Option (Term × Deriv) :=
  rs.foldl (fun acc r ↦ acc.orElse fun _ ↦ match r with
    | .rule l => (rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])
    | .delta k => match t.label with
      | .defn k' _ => if k = k' then
          (rootStep G E n Γ Φ .delta t).map fun t' ↦ (t', RoseTree.node .delta [])
        else none
      | _ => none
    | .thm j θ => do
      let a ← E[j]?
      let (l, _) ← eqParts a.concl
      let σ ← matchTerm (Term.osubst θ l) t (List.replicate a.ctx.length none)
      let σ ← σ.mapM id
      let l := Rule.thm j θ σ false
      (rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])
    | .hyp i => (rootStep G E n Γ Φ (.rwHyp i false) t).map fun t' ↦
        (t', RoseTree.node (.rwHyp i false) [])) none

/-- The normal form of a term in a context under hypotheses, by rules, innermost first, within
a depth of {lit}`fuel`, with its rewriting derivation, marked when it rewrites. -/
def normalize (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  fuel.rec (fun _ _ t ↦ some (t, dRefl)) fun _ rec Γ Φ t ↦ do
    let Γs ← childCtxs G n t.label t.children Γ Φ
    let cs ← (Γs.zip t.children).mapM fun ((Δ, Ψ), u) ↦ rec Δ Ψ u
    let t₁ := RoseTree.node t.label (cs.map Prod.fst)
    let d₁ : Deriv × Bool := if cs.any (·.2.2) then
        (RoseTree.node .cong (cs.map (·.2.1)), true)
      else dRefl
    match rootRewrite G E n rs Γ Φ t₁ with
    | some (t₂, dr) => do
      let (t₃, d₃) ← rec Γ Φ t₂
      pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
    | none => pure (t₁, d₁)

/-- The proof of an equation by normalizing both sides to one term. -/
def byNorm (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option Deriv := do
  let (v, d₁, _) ← normalize G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalize G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation in a context of a natural number variable by induction on it, with
the step {lit}`s`, each premise by normalization. -/
def byNatInd (kz ks : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) : Option Deriv := match Γ with
  | _ :: Γ' => do
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))
    let p₁ ← byNorm G E n rs fuel Γ Φ (natSuccAt ks t) (Term.subst s (atVar0 t))
    let p₂ ← byNorm G E n rs fuel Γ Φ (natSuccAt ks u) (Term.subst s (atVar0 u))
    pure (RoseTree.node (.natInd kz ks s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a list variable by induction on it, with the step
{lit}`s`, each premise by normalization. -/
def byListInd (kn kc : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) : Option Deriv := match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let p₁ ← byNorm G E n rs fuel (c :: a :: Γ') (Φ'.map weaken2) (listConsAt kc a t)
      (Term.subst s (atVar0 (weakenElem t)))
    let p₂ ← byNorm G E n rs fuel (c :: a :: Γ') (Φ'.map weaken2) (listConsAt kc a u)
      (Term.subst s (atVar0 (weakenElem u)))
    pure (RoseTree.node (.listInd kn kc s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a natural number variable by induction on it with
the induction hypothesis: each premise by normalization, the step's after the induction
hypothesis, normalized, is cut in as a hypothesis to rewrite by. -/
def byNatIndHyp (kz ks : ℕ) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Option Deriv := match Γ with
  | _ :: Γ' => do
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))
    let Φ₁ := Φ ++ [Term.eq t u]
    let (ψ, dψ, _) ← normalize G E n rs fuel Γ Φ₁ (Term.eq t u)
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Γ (Φ₁ ++ [ψ]) (natSuccAt ks t)
      (natSuccAt ks u)
    let ih := RoseTree.node (.convFrom (Term.eq t u)) [dψ, RoseTree.node (.hyp Φ.length) []]
    pure (RoseTree.node (.natIndHyp kz ks) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

/-- The proof of an equation in a context of a list variable by induction on it with the
induction hypothesis: each premise by normalization, the step's after the induction hypothesis,
normalized, is cut in as a hypothesis to rewrite by. -/
def byListIndHyp (kn kc : ℕ) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Option Deriv := match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let Δ := c :: a :: Γ'
    let Φ₁ := Φ'.map weaken2 ++ [weakenElem (Term.eq t u)]
    let (ψ, dψ, _) ← normalize G E n rs fuel Δ Φ₁ (weakenElem (Term.eq t u))
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Δ (Φ₁ ++ [ψ]) (listConsAt kc a t)
      (listConsAt kc a u)
    let ih := RoseTree.node (.convFrom (weakenElem (Term.eq t u)))
      [dψ, RoseTree.node (.hyp Φ'.length) []]
    pure (RoseTree.node (.listIndHyp kn kc) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

end Geb.FreeTopos.Internal

end
