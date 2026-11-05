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
derivation's nodes ({name}`Geb.FreeTopos.Internal.checkStep`). A join whose rewritings cite no
theorem and no hypothesis is translated by steps of the machine that unfold every definition but
those the rewritings' results apply: a normal form that unfolds more is in general larger than the
rewritings' result by the sharing the machine's values hold and its terms do not. A join whose
rewritings cite them is translated by a step at each side that unfolds the definitions that side's
rewriting unfolds and rewrites by the theorems and hypotheses it cites, from their left sides to
their right, where the rewriting cites them so. Such a step applies a rule and unfolds a definition
wherever the normal form reaches it, where the rewriting does so at particular positions, so that
its normal form may be larger, as a term, than the rewriting's result. At each rule that proves a
formula from premises, the premises' contexts, hypotheses and formulas are those the base checker
computes, so that a join among the premises is translated at the equation it proves; every other
node, and every rewriting, is the base checker's rule as it stands. A theorem is translated where
the translation replaces a join and the conversion checker accepts the result, and a development
is translated theorem by theorem, each with the constants and the entries before it.

The translation is not trusted: what it produces is checked by the conversion checker, and a
theorem whose translation is not accepted keeps its derivation.

## Main definitions

* {lit}`liftDeriv` — a derivation as a certificate of the conversion checker.
* {lit}`joinByMachine` — the join of an equation's sides by two steps of the machine.
* {lit}`unfoldsIn`, {lit}`citedIn` — the definitions a rewriting unfolds, the rules it cites.
* {lit}`joinByMachineAs` — the join by a step at each side taking it as its rewriting takes it.
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
the first primitives of {lit}`G` that are the empty list and the construction of lists, and its
normal form rewritten by no rule. -/
def machineStep (except : List ℕ) : ConvDeriv :=
  RoseTree.node (.machine fuel G.defs.length except
    (G.prims.findIdx fun p ↦ decide (p = nilPrim))
    (G.prims.findIdx fun p ↦ decide (p = consPrim)) []) []

/-- The join of an equation's sides, which the rewritings {lit}`d₁` and {lit}`d₂` join, by two
steps of the machine unfolding every definition but those the rewritings' results apply, where
the machine reduces the sides to one term. -/
def joinByMachine (Γ : List Tree) (Φ : List Term) (d₁ d₂ : Deriv) (t u : Term) :
    Option ConvDeriv := do
  let v₁ ← (check G E n d₁).1 Γ Φ t
  let v₂ ← (check G E n d₂).1 Γ Φ u
  let step := machineStep G fuel (defnsIn v₁ ++ defnsIn v₂).eraseDups
  let r := (convCheck G E [] n step).1 Γ Φ
  let w₁ ← r t
  let w₂ ← r u
  if w₁ = w₂ then some (RoseTree.node (.base .join) [step, step]) else none

/-- The indices of the definitions a rewriting unfolds, of a term in a context under hypotheses. -/
abbrev Unfolds : Type := List Tree → List Term → Term → List ℕ

/-- One step of the collection of the definitions a rewriting unfolds, at a node of a rule from
its children with their collections: at the unfolding of a definition its index, at one
rewriting after another the definitions the first unfolds and those the second unfolds of the
first's result, at the rewriting of each child of a node those each child's rewriting unfolds,
and at every other node none. -/
def unfoldsStep (l : Rule) (cs : List (Deriv × Unfolds)) : Unfolds := fun Γ Φ t ↦
  match l, cs with
  | .delta, [] => match t.label with
    | .defn k _ => [k]
    | _ => []
  | .trans, [(d₁, u₁), (_, u₂)] => u₁ Γ Φ t ++ (((check G E n d₁).1 Γ Φ t).map (u₂ Γ Φ)).getD []
  | .cong, cs => match congCtxs G n t.label t.children Γ Φ (cs.map Prod.fst) with
    | some Γs => ((cs.zip (Γs.zip t.children)).map fun ((_, u), (Δ, Ψ), v) ↦ u Δ Ψ v).flatten
    | none => []
  | _, _ => []

/-- The indices of the definitions a derivation's rewriting unfolds. -/
def unfoldsIn : Deriv → Unfolds := RoseTree.para (unfoldsStep G E n)

/-- The theorems, at their objects, and the hypotheses a derivation rewrites by, as rules of the
prover, each from its left side to its right; nothing where it rewrites by one from its right
side to its left. -/
def citedIn : Deriv → Option (List NormRule) :=
  RoseTree.elim fun r cs ↦ do
    let ps ← cs.mapM id
    match r with
    | .thm j θ _ false => pure (.thm j θ :: ps.flatten)
    | .rwHyp i false => pure (.hyp i :: ps.flatten)
    | .thm _ _ _ true | .rwHyp _ true => none
    | _ => pure ps.flatten

/-- The step of the machine within the depth of recursion {lit}`fuel` taking a term as the
rewriting {lit}`d` takes it, in a context under hypotheses: it unfolds the definitions the
rewriting unfolds and no other, and rewrites by the theorems and hypotheses the rewriting
cites. -/
def machineStepAs (Γ : List Tree) (Φ : List Term) (d : Deriv) (t : Term) : Option ConvDeriv := do
  let rs ← citedIn d
  let ks := unfoldsIn G E n d Γ Φ t
  pure (RoseTree.node (.machine fuel G.defs.length
    ((List.range G.defs.length).filter fun j ↦ !ks.contains j)
    (G.prims.findIdx fun p ↦ decide (p = nilPrim))
    (G.prims.findIdx fun p ↦ decide (p = consPrim)) rs) [])

/-- The join of an equation's sides, which the rewritings {lit}`d₁` and {lit}`d₂` join, by a step
of the machine at each side taking it as its rewriting takes it, where the two reduce the sides to
one term. -/
def joinByMachineAs (Γ : List Tree) (Φ : List Term) (d₁ d₂ : Deriv) (t u : Term) :
    Option ConvDeriv := do
  let s₁ ← machineStepAs G E n fuel Γ Φ d₁ t
  let s₂ ← machineStepAs G E n fuel Γ Φ d₂ u
  let w₁ ← (convCheck G E [] n s₁).1 Γ Φ t
  let w₂ ← (convCheck G E [] n s₂).1 Γ Φ u
  if w₁ = w₂ then some (RoseTree.node (.base .join) [s₁, s₂]) else none

/-- The translation of a derivation's proof of a formula in a context under hypotheses, where it
replaces a join; nothing where it replaces none. -/
abbrev Translation : Type := List Tree → List Term → Term → Option ConvDeriv

/-- One step of the translation, at a node of a rule from its children with their translations:
at a join whose rewritings cite a theorem or a hypothesis, the join by a step at each side; at any
other join, the join by the machine of the equation's
sides; at a rule that proves a formula from premises, the node over the premises' translations at
the formulas the base checker proves them at, each premise the base checker's where its translation
replaces nothing; at every other node nothing. -/
def byMachineStep (l : Rule) (cs : List (Deriv × Translation)) : Translation := fun Γ Φ φ ↦
  let at' (ps : List (Option ConvDeriv)) : Option ConvDeriv :=
    if ps.any Option.isSome then
      some (RoseTree.node (.base l) ((ps.zip cs).map fun (p, c) ↦ p.getD (liftDeriv c.1)))
    else none
  match l, cs with
  | .join, [(d₁, _), (d₂, _)] =>
    (eqParts φ).bind fun (t, u) ↦ if citesAny d₁ || citesAny d₂ then
      joinByMachineAs G E n fuel Γ Φ d₁ d₂ t u
    else joinByMachine G E n fuel Γ Φ d₁ d₂ t u
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
  | some c => if a.convChecks G E [] c then .conv a c else .base (.language a d)
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
