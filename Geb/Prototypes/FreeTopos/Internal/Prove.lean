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
list that applies, and normalizes the result; or weak head normal forms first, an argument used
more than once reduced before it is substituted, so that its value is computed once, and a case
analysis's branches reduced only once one is selected. The rules are the language's equations,
the earlier theorems, whose instances it finds by matching their left sides, and the hypotheses.
It proves an equation by normalizing both sides to one term, by induction on the innermost
variable with a step it is given, and by induction on a rose tree in the form of the uniqueness
of its fold, each premise by normalization; with the induction hypothesis, it normalizes the
hypothesis, cuts in the normal form, and rewrites the step by it. Proofs compose: an equation of
functions by extensionality, an equation by case analysis of a variable of a coproduct anywhere
in the context, and list induction whose premises other proofs prove. The prover is not
trusted: a derivation it computes is checked.

## Main definitions

* {lit}`NormRule` — a rule the normalizer applies at a term's root.
* {lit}`normalize` — the normal form of a term and its rewriting derivation.
* {lit}`byNorm`, {lit}`byNatInd`, {lit}`byListInd`, {lit}`byNatIndHyp`, {lit}`byListIndHyp`,
  {lit}`byRoseInd`, {lit}`byNormW` — the proofs of an equation.
* {lit}`byFunExt`, {lit}`bySplit`, {lit}`byListIndWith` — the proofs of an equation from proofs
  of others: of functions by extensionality, by case analysis of a variable of a coproduct
  anywhere in the context, and by list induction with each premise proved by a prover.
* {lit}`eval`, {lit}`whnf`, {lit}`normalizeW` — the reduction to a depth, sharing an argument's
  value among its uses, the weak head normal form, and the normal form reached through it.

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

/-- The child of a node other than an application whose normalization can enable a rule at the
node's root: the pair of a component, and the datum of a fold. -/
def headChild : Label → List Term → Option ℕ
  | .fst, [_] => some 0
  | .snd, [_] => some 0
  | .natRec, [_, _, _] => some 2
  | .listRec, [_, _, _] => some 2
  | .roseRec _, [_, _] => some 1
  | _, _ => none

/-- How far the evaluator reduces a term: to its weak head normal form; to its weak normal form,
every subterm reduced but those under an abstraction and a fold's start and step, which have
contexts of their own; or to its normal form. -/
inductive Depth where
  /-- The weak head normal form. -/
  | head
  /-- The weak normal form. -/
  | weak
  /-- The normal form. -/
  | full
deriving DecidableEq

/-- Whether the weak normal form leaves a node's child of an index in place: every child of an
abstraction, and the start and the step of a fold. -/
def keepsWeak (l : Label) (i : ℕ) : Bool := match l with
  | .lam _ => true
  | .natRec | .listRec => i < 2
  | .roseRec _ => i = 0
  | _ => false

/-- The uses of the variable of index {lit}`d` in a term, each under an abstraction counted
twice, since the abstraction may be applied more than once; a fold's start and step, in contexts
of their own, have none. -/
def uses : Term → ℕ → ℕ :=
  RoseTree.para fun l cs d ↦ match l, cs with
    | .var i, _ => if i = d then 1 else 0
    | .lam _, cs => 2 * (cs.map fun c ↦ c.2 (d + 1)).sum
    | .natRec, [_, _, (_, m)] | .listRec, [_, _, (_, m)] | .roseRec _, [_, (_, m)] => m d
    | _, cs => (cs.map fun c ↦ c.2 d).sum

/-- The derivation of a node's rewriting from its children's, marked when one rewrites. -/
def dCong (cs : List (Deriv × Bool)) : Deriv × Bool :=
  if cs.any (·.2) then (RoseTree.node .cong (cs.map (·.1)), true) else dRefl

/-- The reduction of a term in a context under hypotheses, by rules, to a depth, within a depth
of recursion of {lit}`fuel`, with its rewriting derivation, marked when it rewrites. The weak
head normal form of an application is that of its function, and then, before a rule at the root,
the weak normal form of its argument when the function is an abstraction whose variable
{lit}`uses` counts more than once, so that its value is computed once rather than at each use,
and its weak head normal form when the function is not an abstraction, so that a case analysis
receives its scrutinee; that of any other node is the first rule that rewrites the
root, the unfolding of a definition receiving its arguments unreduced, else the weak head normal
form of the child it depends on and the first rule that then rewrites the root. The branches of
a case analysis, abstractions, are reduced only once one is selected. The weak normal form then
reduces the children but those {lit}`keepsWeak` leaves, and the normal form every child, each in
its own context, and a rule at the root. The children the weak head and weak normal forms reduce
are in the node's context, which they therefore do not compute. -/
def eval (rs : List NormRule) (fuel : ℕ) :
    Depth → List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  fuel.rec (fun _ _ _ t ↦ some (t, dRefl)) fun _ rec depth Γ Φ t ↦ do
    -- the weak head normal form, then the root's rewriting and its weak head normal form
    let atRoot (t₁ : Term) (d₁ : Deriv × Bool) : Option (Term × Deriv × Bool) :=
      match rootRewrite G E n rs Γ Φ t₁ with
      | some (t₂, dr) => do
        let (t₃, d₃) ← rec .head Γ Φ t₂
        pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
      | none => pure (t₁, d₁)
    let (w, dw) ← match t.label, t.children with
      | .app, [f, u] => do
        let (f', df) ← rec .head Γ Φ f
        let (u', du) ← match f'.label, f'.children with
          | .lam _, [b] => if uses b 0 < 2 then some (u, dRefl) else rec .weak Γ Φ u
          | _, _ => rec .head Γ Φ u
        atRoot (Term.app f' u') (dCong [df, du])
      | l, cs => match rootRewrite G E n rs Γ Φ t with
        | some (t₁, dr) => do
          let (t₂, d₂) ← rec .head Γ Φ t₁
          pure (t₂, dTrans (dr, true) d₂)
        | none => match headChild l cs with
          | none => some (t, dRefl)
          | some i => do
            let c ← cs[i]?
            let (c', dc) ← rec .head Γ Φ c
            if dc.2 then
              atRoot (RoseTree.node l (cs.set i c'))
                (dCong ((List.range cs.length).map fun j ↦ if j = i then dc else dRefl))
            else some (t, dRefl)
    match depth with
    | .head => pure (w, dw)
    | .weak => do
      let cs ← w.children.zipIdx.mapM fun (u, i) ↦
        if keepsWeak w.label i then some (u, dRefl) else rec .weak Γ Φ u
      pure (RoseTree.node w.label (cs.map Prod.fst), dTrans dw (dCong (cs.map Prod.snd)))
    | .full => do
      let Γs ← childCtxs G n w.label w.children Γ Φ
      let cs ← (Γs.zip w.children).mapM fun ((Δ, Ψ), u) ↦ rec .full Δ Ψ u
      let t₁ := RoseTree.node w.label (cs.map Prod.fst)
      let d₁ := dCong (cs.map Prod.snd)
      match rootRewrite G E n rs Γ Φ t₁ with
      | some (t₂, dr) => do
        let (t₃, d₃) ← rec .full Γ Φ t₂
        pure (t₃, dTrans dw (dTrans d₁ (dTrans (dr, true) d₃)))
      | none => pure (t₁, dTrans dw d₁)

/-- The weak head normal form of a term, by {lit}`eval`. -/
def whnf (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  eval G E n rs fuel .head

/-- The normal form of a term reached through its weak head normal form, by {lit}`eval`: a fold
whose datum computes selects its case before the cases are normalized. -/
def normalizeW (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  eval G E n rs fuel .full

/-- The proof of an equation by normalizing both sides, weak head normal forms first, to one
term. -/
def byNormW (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option Deriv := do
  let (v, d₁, _) ← normalizeW G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalizeW G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- A prover of equations: a derivation of the equation of two terms in a context under
hypotheses. -/
abbrev Prover : Type := List Tree → List Term → Term → Term → Option Deriv

/-- The abstraction of a term over its variable of index {lit}`i`, of the type {lit}`c`: the
function whose application to that variable is the term. -/
def abstractVar (i : ℕ) (c : Tree) (t : Term) : Term :=
  Term.lam c (Term.subst (weaken1 t) fun j ↦ if j = i + 1 then Term.var 0 else Term.var j)

/-- The proof of an equation of functions by the proof, by {lit}`prove`, of the equation of
their applications to a new variable. -/
def byFunExt (prove : Prover) : Prover := fun Γ Φ f g ↦ do
  let (a, _) ← (typeIn G n Γ f).bind expParts
  let d ← prove (a :: Γ) (Φ.map weaken1) (Term.app (weaken1 f) (Term.var 0))
    (Term.app (weaken1 g) (Term.var 0))
  pure (RoseTree.node .funExt [d])

/-- The proof of an equation by case analysis on the variable of index {lit}`i`, of a coproduct
whose injections are the primitives of indices {lit}`kl` and {lit}`kr`, each case proved by
{lit}`prove`: the sides abstracted over the variable are equal functions, by extensionality and
the case analysis of the new, innermost variable, and the equation follows, cut in as a
hypothesis, by applying them to the variable. -/
def bySplit (kl kr i : ℕ) (prove : Prover) : Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let (a, b) ← coprodParts c
  let F := abstractVar i c t
  let H := abstractVar i c u
  let inj (k : ℕ) (s : Term) : Term := Term.app (weaken1 s) (Term.arr k [a, b] (Term.var 0))
  let q₀ ← prove (a :: Γ) (Φ.map weaken1) (inj kl F) (inj kl H)
  let q₁ ← prove (b :: Γ) (Φ.map weaken1) (inj kr F) (inj kr H)
  let pψ := RoseTree.node .funExt [RoseTree.node (.coprodInd kl kr) [q₀, q₁]]
  let dχ := RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []]
  let pχ := RoseTree.node .join [RoseTree.node .cong
    [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []], RoseTree.node .refl []]
  let χ := Term.eq (Term.app F (Term.var i)) (Term.app H (Term.var i))
  pure (RoseTree.node (.cut (Term.eq F H)) [pψ, RoseTree.node (.convFrom χ) [dχ, pχ]])

/-- The proof of an equation in a context of a list variable by induction on it with the
induction hypothesis, each premise by its prover: the empty list's, and the construction's
with the induction hypothesis the last of its hypotheses. -/
def byListIndWith (kn kc : ℕ) (p₀ p₁ : Prover) : Prover := fun Γ Φ t u ↦ match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let d₀ ← p₀ Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let d₁ ← p₁ (c :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem (Term.eq t u)])
      (listConsAt kc a t) (listConsAt kc a u)
    pure (RoseTree.node (.listIndHyp kn kc) [d₀, d₁])
  | [] => none

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
