/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.FreeTopos.Internal.Logic -- shake: keep; the docstrings' name roles

set_option doc.verso true in
/-!
# Provers of the internal language's equations

Proofs of an equation of the internal language, as certificates of the conversion checker
({name}`Geb.FreeTopos.Internal.convCheck`). A prover reduces a term by one of the prover's
reductions ({name}`Geb.FreeTopos.Internal.normalize`, {name}`Geb.FreeTopos.Internal.eval`) and,
where the reduction rewrites and the derivation it computes has more nodes than a bound
({lit}`stepBound`), names it in its certificate by the step of conversion that computes it, with
its rules, its fuel and its depth, in place of that derivation: the checker performs the
reduction again and neither is given nor checks its derivation. A derivation within the bound is
kept, the checker walking it along its rewritings sooner than it performs the reduction, which
traverses the whole term; the bound is above the derivations of the stored developments, whose
certificates so hold derivations. A step names a theorem whose matching was prepared as the theorem
({name}`Geb.FreeTopos.Internal.NormRule.unprepare`), which the checker prepares again, so that a
certificate holds no function. A prover proves an equation by normalizing both sides to one
term, by induction on the innermost variable with a step it is given, and by induction on a rose
tree in the form of the uniqueness of its fold, each premise by normalization; with the
induction hypothesis, it normalizes the hypothesis, cuts in the normal form, and rewrites the
step by it. Proofs compose: an equation of functions by extensionality, an equation by case
analysis of a variable of a coproduct anywhere in the context, and list induction whose premises
other proofs prove. A prover is not trusted: a certificate it computes is checked.

## Main definitions

* {lit}`cTrans`, {lit}`cRefl`, {lit}`cCong` — the certificates of one rewriting after another,
  of no rewriting and of a node's rewriting from its children's, each with its mark.
* {lit}`derivSize`, {lit}`stepBound` — the number of a derivation's nodes, and the number above
  which a reduction's derivation is replaced by its step.
* {lit}`stepped` — a reduction's result with the certificate of its rewriting, the step that
  names the reduction or the derivation it computes.
* {lit}`normalizeC`, {lit}`evalC`, {lit}`normalizeWC` — the prover's reductions, each result with
  the certificate of its rewriting.
* {lit}`Prover` — a prover of equations.
* {lit}`byNorm`, {lit}`byNatInd`, {lit}`byListInd`, {lit}`byNatIndHyp`, {lit}`byListIndHyp`,
  {lit}`byRoseInd`, {lit}`byNormW` — the proofs of an equation.
* {lit}`byFunExt`, {lit}`bySplit`, {lit}`byListIndWith`, {lit}`byRoseIndHyp` — the proofs of an
  equation from proofs of others: of functions by extensionality, by case analysis of a variable
  of a coproduct anywhere in the context, and by list induction and rose-tree induction with each
  premise proved by a prover.
* {lit}`Logic.cnd`, {lit}`Logic.trueIC`, {lit}`Logic.impIC`, {lit}`Logic.allIC` — a
  certificate's node of a rule of the language, and the proofs of truth, of an implication and of
  a universal quantification as certificates.

## Tags

internal language, prover, conversion, normalization, induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

/-- The certificate of one rewriting after another, the identity left out. -/
def cTrans (d₁ d₂ : ConvDeriv × Bool) : ConvDeriv × Bool :=
  match d₁.2, d₂.2 with
  | false, _ => d₂
  | _, false => d₁
  | true, true => (RoseTree.node .trans [d₁.1, d₂.1], true)

/-- The identity certificate, marked as no rewriting. -/
def cRefl : ConvDeriv × Bool := (RoseTree.node .refl [], false)

/-- The certificate of a node's rewriting from its children's, marked when one rewrites. -/
def cCong (cs : List (ConvDeriv × Bool)) : ConvDeriv × Bool :=
  if cs.any (·.2) then (RoseTree.node .cong (cs.map (·.1)), true) else cRefl

/-- The number of a derivation's nodes, counted as a tree: a node once for each path to it from
the root, which is the number of steps the checker's fold takes on it. -/
def derivSize : Deriv → ℕ := RoseTree.elim fun _ ns ↦ 1 + ns.sum

/-- The number of nodes above which a prover names a reduction by its step in place of the
derivation the reduction computes. The checker computes a step by performing the reduction, which
traverses the whole term and tries its rules at each node, and checks a derivation along its
rewritings alone, sooner than it performs the reduction. The bound is above the nodes of every
derivation the reductions of the stored developments compute, so that their certificates hold
derivations; a lower bound exchanges the size of the certificates for the time of their
checks. -/
def stepBound : ℕ := 4294967296

/-- A reduction's result with the certificate of its rewriting: the reduced term; where the
reduction rewrites, the step where the derivation it computes has more nodes than
{name}`Geb.FreeTopos.Internal.stepBound`, built where it is taken, and that derivation otherwise;
where it does not rewrite, the identity; and the mark. -/
def stepped (st : Unit → ConvDeriv) (x : Term × Deriv × Bool) : Term × ConvDeriv × Bool :=
  (x.1, if x.2.2 then (if stepBound < derivSize x.2.1 then st () else liftDeriv x.2.1)
    else RoseTree.node .refl [], x.2.2)

variable (G : Globals) (E : Array Entry) (n : ℕ)

/-- The normal form of a term in a context under hypotheses, by rules, innermost first, within a
depth of {lit}`fuel`, with the certificate of its rewriting
({name}`Geb.FreeTopos.Internal.stepped`), the step of conversion that names the normalization
or the derivation it computes, marked when it rewrites. -/
def normalizeC (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × ConvDeriv × Bool) := fun Γ Φ t ↦
  (normalize G E n rs fuel Γ Φ t).map
    (stepped fun _ ↦ RoseTree.node (.norm (rs.map NormRule.unprepare) fuel) [])

/-- The reduction of a term in a context under hypotheses, by rules, to a depth, within a depth
of recursion of {lit}`fuel`, with the certificate of its rewriting
({name}`Geb.FreeTopos.Internal.stepped`), the step of conversion that names the reduction or
the derivation it computes, marked when it rewrites. -/
def evalC (rs : List NormRule) (fuel : ℕ) :
    Depth → List Tree → List Term → Term → Option (Term × ConvDeriv × Bool) := fun dp Γ Φ t ↦
  (eval G E n rs fuel dp Γ Φ t).map
    (stepped fun _ ↦ RoseTree.node (.eval (rs.map NormRule.unprepare) fuel dp) [])

/-- The normal form of a term reached through its weak head normal form, with the certificate of
its rewriting. -/
def normalizeWC (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × ConvDeriv × Bool) :=
  evalC G E n rs fuel .full

/-- The proof of an equation by normalizing both sides to one term. -/
def byNorm (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option ConvDeriv := do
  let (v, d₁, _) ← normalizeC G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalizeC G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation in a context of a natural number variable by induction on it, with
the step {lit}`s`, each premise by normalization. -/
def byNatInd (kz ks : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) : Option ConvDeriv := match Γ with
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
    (Φ : List Term) (t u : Term) : Option ConvDeriv := match Γ with
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
    (t u : Term) : Option ConvDeriv := match Γ with
  | _ :: Γ' => do
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))
    let Φ₁ := Φ ++ [Term.eq t u]
    let (ψ, dψ, _) ← normalizeC G E n rs fuel Γ Φ₁ (Term.eq t u)
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Γ (Φ₁ ++ [ψ]) (natSuccAt ks t)
      (natSuccAt ks u)
    let ih := RoseTree.node (.convFrom (Term.eq t u)) [dψ, RoseTree.node (.hyp Φ.length) []]
    pure (RoseTree.node (.natIndHyp kz ks) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

/-- The proof of an equation in a context of a list variable by induction on it with the
induction hypothesis: each premise by normalization, the step's after the induction hypothesis,
normalized, is cut in as a hypothesis to rewrite by. -/
def byListIndHyp (kn kc : ℕ) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Option ConvDeriv := match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let Δ := c :: a :: Γ'
    let Φ₁ := Φ'.map weaken2 ++ [weakenElem (Term.eq t u)]
    let (ψ, dψ, _) ← normalizeC G E n rs fuel Δ Φ₁ (weakenElem (Term.eq t u))
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Δ (Φ₁ ++ [ψ]) (listConsAt kc a t)
      (listConsAt kc a u)
    let ih := RoseTree.node (.convFrom (weakenElem (Term.eq t u)))
      [dψ, RoseTree.node (.hyp Φ'.length) []]
    pure (RoseTree.node (.listIndHyp kn kc) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

/-- The proof of an equation by normalizing both sides, weak head normal forms first, to one
term. -/
def byNormW (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option ConvDeriv := do
  let (v, d₁, _) ← normalizeWC G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalizeWC G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- A prover of equations: a derivation of the equation of two terms in a context under
hypotheses. -/
abbrev Prover : Type := List Tree → List Term → Term → Term → Option ConvDeriv

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
    (t u : Term) : Option ConvDeriv := match Γ with
  | [r] => do
    let (a, _) ← roseParts r
    let C ← typeIn G n Γ t
    let p₁ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a t)
      (Term.subst s (atVar0 (roseMapAt kl kc C t)))
    let p₂ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a u)
      (Term.subst s (atVar0 (roseMapAt kl kc C u)))
    pure (RoseTree.node (.roseInd kn kl kc s) [p₁, p₂])
  | _ => none

/-- The proof of an equation under no hypotheses by induction on the innermost variable, of a
rose-tree type, with the induction hypothesis, the premise at a construction proved by {lit}`p`
under the hypothesis that the equation holds at each child. -/
def byRoseIndHyp (kn kl kc : ℕ) (p : Prover) : Prover := fun Γ Φ t u ↦ match Γ, Φ with
  | r :: Γ', [] => do
    let (a, _) ← roseParts r
    let d ← p (list r :: a :: Γ') [roseHyp kl kc (Term.eq t u)] (roseNodeAt kn r a t)
      (roseNodeAt kn r a u)
    pure (RoseTree.node (.roseIndHyp kn kl kc) [d])
  | _, _ => none

namespace Logic

/-- A certificate's node of a rule of the language. -/
def cnd (l : Rule) (cs : List ConvDeriv := []) : ConvDeriv := RoseTree.node (.base l) cs

/-- The proof of truth, as a certificate: its unfolding's sides are one term. -/
def trueIC : ConvDeriv := cnd .conv [cnd .delta, cnd .join [cnd .refl, cnd .refl]]

/-- The introduction of the implication of {lit}`q` by {lit}`p`, under {lit}`n` hypotheses, from
the certificate {lit}`d` of {lit}`q` under them and {lit}`p`, as
{name}`Geb.FreeTopos.Internal.Logic.impI` introduces it from a derivation. -/
def impIC (j n : ℕ) (p q : Term) (d : ConvDeriv) : ConvDeriv :=
  cnd .conv [cnd .delta, cnd .propExt [cnd (.apply (j + 2) [] [q, p]) [cnd (.hyp n)],
    cnd (.apply (j + 1) [] [q, p]) [cnd (.hyp n), d]]]

/-- The introduction of a universal quantification of an abstraction from the certificate
{lit}`d` of its body at a new variable, under truth, as
{name}`Geb.FreeTopos.Internal.Logic.allI` introduces it from a derivation. -/
def allIC (d : ConvDeriv) : ConvDeriv :=
  cnd .conv [cnd .delta, cnd .funExt [cnd .conv [cnd .cong [cnd .beta, cnd .beta],
    cnd .propExt [trueIC, d]]]]

end Logic

end Geb.FreeTopos.Internal

end
