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
normalizing both sides to one term, by induction on the innermost variable with a step it is
given, and by induction on a rose tree in the form of the uniqueness of its fold, each premise by
normalization; with the induction hypothesis, it normalizes the
hypothesis, cuts in the normal form, and rewrites the step by it. The prover is not trusted: a
derivation it computes is checked.

## Main definitions

* {lit}`NormRule` — a rule the normalizer applies at a term's root.
* {lit}`normalize` — the normal form of a term and its rewriting derivation.
* {lit}`byNorm`, {lit}`byNatInd`, {lit}`byListInd`, {lit}`byNatIndHyp`, {lit}`byListIndHyp`,
  {lit}`byRoseInd`, {lit}`byNormW` — the proofs of an equation.
* {lit}`whnf`, {lit}`normalizeW` — the weak head normal form, and the normal form reached
  through it.

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

/-- The matching of a pattern against a term under {lit}`d` binders, the pattern's variables
from {lit}`d` on bound in the assignment to terms that do not mention the binders' variables:
the extended assignment, or nothing when they do not match. A variable below {lit}`d` matches
itself; the start and the step of a fold, in contexts of their own, match only themselves. -/
def matchTerm (p : Term) : ℕ → Term → List (Option Term) → Option (List (Option Term)) :=
  RoseTree.para (fun l ps d t σ ↦ match l with
    | .var i => if i < d then (if t = Term.var i then some σ else none) else
      let t' := Term.rename t (· - d)
      if Term.rename t' (· + d) = t then match σ[i - d]? with
        | some none => some (σ.set (i - d) (some t'))
        | some (some s) => if s = t' then some σ else none
        | none => if t' = Term.var (i - d) then some σ else none
      else none
    | l => if l = t.label ∧ ps.length = t.children.length then
        match l, ps, t.children with
        | .lam _, [(_, q)], [u] => q (d + 1) u σ
        | .natRec, [(z, _), (s, _), (_, q)], [z', s', u] =>
          if z = z' ∧ s = s' then q d u σ else none
        | .listRec, [(z, _), (s, _), (_, q)], [z', s', u] =>
          if z = z' ∧ s = s' then q d u σ else none
        | .roseRec _, [(s, _), (_, q)], [s', u] => if s = s' then q d u σ else none
        | _, ps, us => (ps.zip us).foldl (fun acc (q, u) ↦ acc.bind (q.2 d u)) (some σ)
      else none) p

/-- The derivation of one rewriting after another, the identity left out. -/
def dTrans (d₁ d₂ : Deriv × Bool) : Deriv × Bool :=
  match d₁.2, d₂.2 with
  | false, _ => d₂
  | _, false => d₁
  | true, true => (RoseTree.node .trans [d₁.1, d₂.1], true)

/-- The identity derivation, marked as no rewriting. -/
def dRefl : Deriv × Bool := (RoseTree.node .refl [], false)

variable (G : Globals) (E : Array Entry) (n : ℕ)

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
      let a ← (E[j]?).bind Entry.language?
      let (l, _) ← eqParts a.concl
      let σ ← matchTerm (Term.osubst θ l) 0 t (List.replicate a.ctx.length none)
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

/-- The child of a node whose normalization can enable a rule at the node's root: the function
of an application, the pair of a component, and the datum of a fold. -/
def headChild : Label → List Term → Option ℕ
  | .app, [_, _] => some 0
  | .fst, [_] => some 0
  | .snd, [_] => some 0
  | .natRec, [_, _, _] => some 2
  | .listRec, [_, _, _] => some 2
  | .roseRec _, [_, _] => some 1
  | _, _ => none

/-- The weak head normal form of a term in a context under hypotheses, by rules, within a depth
of {lit}`fuel`, with its rewriting derivation, marked when it rewrites: the first rule that
rewrites the root, else the weak head normal form of the child it depends on and the first rule
that then rewrites the root, until none does. -/
def whnf (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  fuel.rec (fun _ _ t ↦ some (t, dRefl)) fun _ rec Γ Φ t ↦
    match rootRewrite G E n rs Γ Φ t with
    | some (t₁, dr) => do
      let (t₂, d₂) ← rec Γ Φ t₁
      pure (t₂, dTrans (dr, true) d₂)
    | none => match headChild t.label t.children with
      | none => some (t, dRefl)
      | some i => do
        let Γs ← childCtxs G n t.label t.children Γ Φ
        let (Δ, Ψ) ← Γs[i]?
        let c ← t.children[i]?
        let (c', dc, ch) ← rec Δ Ψ c
        if ch then
          let t₁ := RoseTree.node t.label (t.children.set i c')
          let d₁ : Deriv × Bool := (RoseTree.node .cong
            ((List.range t.children.length).map fun j ↦ if j = i then dc else dRefl.1), true)
          match rootRewrite G E n rs Γ Φ t₁ with
          | some (t₂, dr) => do
            let (t₃, d₃) ← rec Γ Φ t₂
            pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
          | none => pure (t₁, d₁)
        else some (t, dRefl)

/-- The normal form of a term in a context under hypotheses, by rules, within a depth of
{lit}`fuel`, with its rewriting derivation, marked when it rewrites: the weak head normal form
first, so that a fold whose datum computes selects its case before the cases are normalized,
then its children's normal forms, and a rule at the root. -/
def normalizeW (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  fuel.rec (fun _ _ t ↦ some (t, dRefl)) fun _ rec Γ Φ t ↦ do
    let (w, dw) ← whnf G E n rs fuel Γ Φ t
    let Γs ← childCtxs G n w.label w.children Γ Φ
    let cs ← (Γs.zip w.children).mapM fun ((Δ, Ψ), u) ↦ rec Δ Ψ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ : Deriv × Bool := if cs.any (·.2.2) then
        (RoseTree.node .cong (cs.map (·.2.1)), true)
      else dRefl
    match rootRewrite G E n rs Γ Φ t₁ with
    | some (t₂, dr) => do
      let (t₃, d₃) ← rec Γ Φ t₂
      pure (t₃, dTrans dw (dTrans d₁ (dTrans (dr, true) d₃)))
    | none => pure (t₁, dTrans dw d₁)

/-- The proof of an equation by normalizing both sides, weak head normal forms first, to one
term. -/
def byNormW (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option Deriv := do
  let (v, d₁, _) ← normalizeW G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalizeW G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation in a context of a rose tree alone by induction in the form of the
uniqueness of the fold, with the step {lit}`s` at the label and the list of the values at the
children, each premise by normalization. -/
def byRoseInd (kn kl kc : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (t u : Term) : Option Deriv := match Γ with
  | [r] => do
    let (a, _) ← roseParts r
    let C ← typeIn G n Γ t
    let p₁ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a t)
      (Term.subst s (atVar0 (roseMapAt kl kc C t)))
    let p₂ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a u)
      (Term.subst s (atVar0 (roseMapAt kl kc C u)))
    pure (RoseTree.node (.roseInd kn kl kc s) [p₁, p₂])
  | _ => none

end Geb.FreeTopos.Internal

end
