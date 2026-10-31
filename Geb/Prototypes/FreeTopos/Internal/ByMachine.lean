/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.ConvDevelopment
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Derivations rewritten by steps of the environment machine

The translation of a derivation of the base checker to a certificate of the conversion checker
({name}`Geb.FreeTopos.Internal.convCheck`) in which each join of two rewritings that the
environment machine also joins ({name}`Geb.FreeTopos.Internal.machineReduce`) is the join of
two steps of the machine. The translation follows the formulas the base checker proves at a
derivation's nodes ({name}`Geb.FreeTopos.Internal.checkStep`). A join is translated where
its rewritings cite no theorem and no hypothesis, since the machine applies neither, by steps of
the machine that unfold every definition but those the rewritings' results apply: a normal form
that unfolds more is in general larger than the rewritings' result by the sharing the machine's
values hold and its terms do not. At each rule that proves a formula
from premises, the premises' contexts, hypotheses and formulas are those the base checker
computes, so that a join among the premises is translated at the equation it proves; every other
node, and every rewriting, is the base checker's rule as it stands. A theorem is translated where
the translation replaces a join and the conversion checker accepts the result, and a development
is translated theorem by theorem, each with the constants and the entries before it.

The translation is not trusted: what it produces is checked by the conversion checker, and a
theorem whose translation is not accepted keeps its derivation.

## Main definitions

* {lit}`liftDeriv` — a derivation as a certificate of the conversion checker.
* {lit}`joinByMachine` — the join of an equation's sides by two steps of the machine.
* {lit}`byMachine` — the translation of a derivation's proof of a formula.
* {lit}`Thm.byMachine`, {lit}`devByMachine` — the translation of a theorem and of a development.

## Tags

internal language, abstract machine, conversion, certificate, translation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

/-- A derivation as a certificate of the conversion checker, each node its rule. -/
def liftDeriv : Deriv → ConvDeriv := RoseTree.map ConvRule.base

/-- Whether a rule rewrites by a theorem or by a hypothesis. -/
def Rule.cites : Rule → Bool
  | .thm _ _ _ _ | .rwHyp _ _ => true
  | _ => false

/-- Whether a derivation rewrites by a theorem or by a hypothesis at some node. -/
def citesAny : Deriv → Bool := RoseTree.elim fun r cs ↦ r.cites || cs.any id

/-- The indices of the definitions a term applies. -/
def defnsIn : Term → List ℕ :=
  RoseTree.elim fun l cs ↦ (match l with | .defn k _ => [k] | _ => []) ++ cs.flatten

variable (G : Globals) (E : Array Entry) (n : ℕ) (fuel : ℕ)

/-- The step of the machine within the depth of recursion {lit}`fuel` unfolding every definition
of {lit}`G` but those of {lit}`except`, a rose-tree fold's list of its children's values built by
the first primitives of {lit}`G` that are the empty list and the construction of lists. -/
def machineStep (except : List ℕ) : ConvDeriv :=
  RoseTree.node (.machine fuel G.defs.length except
    (G.prims.findIdx fun p ↦ decide (p = nilPrim))
    (G.prims.findIdx fun p ↦ decide (p = consPrim))) []

/-- The join of an equation's sides, which the rewritings {lit}`d₁` and {lit}`d₂` join, by two
steps of the machine unfolding every definition but those the rewritings' results apply, where
the machine reduces the sides to one term. -/
def joinByMachine (Γ : List Tree) (Φ : List Term) (d₁ d₂ : Deriv) (t u : Term) :
    Option ConvDeriv := do
  let v₁ ← (check G E n d₁).1 Γ Φ t
  let v₂ ← (check G E n d₂).1 Γ Φ u
  let step := machineStep G fuel (defnsIn v₁ ++ defnsIn v₂).eraseDups
  let r := (convCheck G E n step).1 Γ Φ
  let w₁ ← r t
  let w₂ ← r u
  if w₁ = w₂ then some (RoseTree.node (.base .join) [step, step]) else none

/-- The translation of a derivation's proof of a formula in a context under hypotheses, where it
replaces a join; nothing where it replaces none. -/
abbrev Translation : Type := List Tree → List Term → Term → Option ConvDeriv

/-- One step of the translation, at a node of a rule from its children with their translations:
at a join whose rewritings cite no theorem and no hypothesis, which the machine does not apply,
the join by the machine of the equation's sides; at a rule that proves a formula from
premises, the node over the premises' translations at the formulas the base checker proves them
at, each premise the base checker's where its translation replaces nothing; at every other node
nothing. -/
def byMachineStep (l : Rule) (cs : List (Deriv × Translation)) : Translation := fun Γ Φ φ ↦
  let at' (ps : List (Option ConvDeriv)) : Option ConvDeriv :=
    if ps.any Option.isSome then
      some (RoseTree.node (.base l) ((ps.zip cs).map fun (p, c) ↦ p.getD (liftDeriv c.1)))
    else none
  match l, cs with
  | .join, [(d₁, _), (d₂, _)] =>
    if citesAny d₁ || citesAny d₂ then none
    else (eqParts φ).bind fun (t, u) ↦ joinByMachine G E n fuel Γ Φ d₁ d₂ t u
  | .natInd kz ks s, [(_, p₀), (_, p₁), (_, p₂)] => match eqParts φ, Γ with
    | some (t, u), _ :: Γ' => (lowerHyps G n Γ' Φ).bind fun Φ' ↦
      at' [p₀ Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
          (Term.subst u (instVar (Term.arr kz [] Term.star)))),
        p₁ Γ Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))),
        p₂ Γ Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))]
    | _, _ => none
  | .listInd kn kc s, [(_, p₀), (_, p₁), (_, p₂)] => match eqParts φ, Γ with
    | some (t, u), c :: Γ' => match listPart c, lowerHyps G n Γ' Φ with
      | some a, some Φ' =>
        at' [p₀ Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [a] Term.star)))
            (Term.subst u (instVar (Term.arr kn [a] Term.star)))),
          p₁ (c :: a :: Γ') (Φ'.map weaken2)
            (Term.eq (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t)))),
          p₂ (c :: a :: Γ') (Φ'.map weaken2)
            (Term.eq (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u))))]
      | _, _ => none
    | _, _ => none
  | .cut ψ, [(_, p), (_, q)] => at' [p Γ Φ ψ, q Γ (Φ ++ [ψ]) φ]
  | .conv, [(d, _), (_, p)] =>
    ((check G E n d).1 Γ Φ φ).bind fun φ' ↦ at' [none, p Γ Φ φ']
  | .convFrom ψ, [_, (_, p)] => at' [none, p Γ Φ ψ]
  | .propExt, [(_, p), (_, q)] =>
    (eqParts φ).bind fun (α, β) ↦ at' [p Γ (Φ ++ [α]) β, q Γ (Φ ++ [β]) α]
  | .funExt, [(_, p)] => (eqParts φ).bind fun (f, g) ↦
    ((typeIn G n Γ f).bind expParts).bind fun (a, _) ↦
      at' [p (a :: Γ) (Φ.map weaken1)
        (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))]
  | .apply j θ σ, ps => ((E[j]?).bind Entry.language?).bind fun a ↦
    if ps.length = a.hyps.length then
      at' ((ps.zip a.hyps).map fun ((_, p), h) ↦ p Γ Φ (instTerm θ σ h))
    else none
  | .natIndHyp kz ks, [(_, p₀), (_, p₁)] => match Γ with
    | _ :: Γ' => (lowerHyps G n Γ' Φ).bind fun Φ' ↦
      at' [p₀ Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))),
        p₁ Γ (Φ ++ [φ]) (natSuccAt ks φ)]
    | [] => none
  | .listIndHyp kn kc, [(_, p₀), (_, p₁)] => match Γ with
    | c :: Γ' => match listPart c, lowerHyps G n Γ' Φ with
      | some a, some Φ' =>
        at' [p₀ Γ' Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))),
          p₁ (c :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem φ]) (listConsAt kc a φ)]
      | _, _ => none
    | [] => none
  | .coprodInd kl kr, [(_, p₀), (_, p₁)] => match Γ with
    | c :: Γ' => (coprodParts c).bind fun (a, b) ↦
      at' [p₀ (a :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kl [a, b] (Term.var 0)))),
        p₁ (b :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kr [a, b] (Term.var 0))))]
    | [] => none
  | .quotInd kq θ, [(_, p₀)] => match Γ, G.prims[kq]? with
    | _ :: Γ', some p =>
      at' [p₀ (PartialHorn.subst θ p.dom :: Γ') Φ
        (Term.subst φ (atVar0 (Term.arr kq θ (Term.var 0))))]
    | _, _ => none
  | .roseInd kn kl kc s, [(_, p₁), (_, p₂)] => match eqParts φ, Γ with
    | some (t, u), [r] => match typeIn G n Γ t, roseParts r with
      | some C, some (a, _) =>
        at' [p₁ [list r, a] [] (Term.eq (roseNodeAt kn r a t)
            (Term.subst s (atVar0 (roseMapAt kl kc C t)))),
          p₂ [list r, a] [] (Term.eq (roseNodeAt kn r a u)
            (Term.subst s (atVar0 (roseMapAt kl kc C u))))]
      | _, _ => none
    | _, _ => none
  | .roseIndHyp kn kl kc, [(_, p₁)] => match Γ with
    | r :: Γ' => match roseParts r, lowerHyps G n Γ' Φ with
      | some (a, _), some Φ' =>
        at' [p₁ (list r :: a :: Γ') (Φ'.map weaken2 ++ [roseHyp kl kc φ]) (roseNodeAt kn r a φ)]
      | _, _ => none
    | [] => none
  | _, _ => none

/-- The translation of a derivation's proof of a formula, where it replaces a join. -/
def byMachine : Deriv → Translation := RoseTree.para (byMachineStep G E n fuel)

/-- The declaration of a theorem with its derivation translated: the theorem with its
translation where the translation replaces a join and the conversion checker accepts it with the
constants of {lit}`G` and the entries of {lit}`E`, and else with its derivation. -/
def Thm.byMachine (a : Thm) (d : Deriv) : ConvDecl :=
  match Internal.byMachine G E a.arity fuel d a.ctx a.hyps a.concl with
  | some c => if a.convChecks G E c then .conv a c else .base (.language a d)
  | none => .base (.language a d)

/-- The translation of a development, each theorem translated with the constants and the entries
the declarations before it leave, each other declaration as it stands. -/
def devByMachine (ds : List Decl) : List ConvDecl :=
  (ds.foldl (fun (st : Option (Globals × Array Entry) × List ConvDecl) d ↦
      (st.1.bind fun (G, E) ↦ d.step G E, (match st.1, d with
        | some (G, E), .language a der => Thm.byMachine G E fuel a der
        | _, d => .base d) :: st.2))
    (some (G, E), [])).2.reverse

end Geb.FreeTopos.Internal

end
