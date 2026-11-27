/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Provers
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Proofs by reduction

Proofs of an equation of the internal language by reducing its sides with the evaluator
({name}`Geb.FreeTopos.Internal.evalC`) to a depth: to one normal form, or to normal forms whose
equation another prover proves; and by normalization through weak head normal forms with the
hypotheses as rewriting rules. Each is a certificate of the conversion checker, a reduction
named by the step of conversion that computes it. The tactics of the modules beside this one
compose them.

## Main definitions

* {lit}`byMode`, {lit}`byWeak` — the proof by reducing both sides to one normal form, at a depth
  and at the weak normal form.
* {lit}`byNF` — the proof of an equation by the proof of the equation of its sides' normal forms.
* {lit}`normH` — the proof by normalization with the hypotheses as rewriting rules.
* {lit}`apps` — the application of a term to arguments.

## Tags

internal language, prover, tactic, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Internal (Term NormRule Entry ConvDeriv)
open scoped FinEnum

/-- The application of a term to arguments, the first first. -/
def apps (f : Term) (xs : List Term) : Term := xs.foldl Term.app f

/-- The proof of an equation by reducing both sides to one normal form, to a depth. -/
def byMode (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) : Internal.Prover := fun Γ Φ t u ↦ do
  let (v, d₁, _) ← Internal.evalC G E n rs 4096 m Γ Φ t
  let (v', d₂, _) ← Internal.evalC G E n rs 4096 m Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation by reducing both sides to one weak normal form. -/
def byWeak (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) :
    Internal.Prover := byMode .weak G E n rs

/-- Prove an equation by a join of two environment-machine steps, testing the proposed
certificate with the conversion checker. The machine unfolds definitions below the bound except
those listed and rewrites by the named rules. -/
def byMachine (G : Internal.Globals) (E : Array Entry) (n fuel bound : ℕ) (except : List ℕ)
    (kl kc : ℕ) (rs : List NormRule) : Internal.Prover := fun Γ Φ t u ↦
  let step := RoseTree.node (.machine fuel bound except kl kc (rs.map NormRule.unprepare)) []
  let cert : ConvDeriv := RoseTree.node .join [step, step]
  if (Internal.convCheck G E [] n cert).2 Γ Φ (Term.eq t u) then some cert else none

/-- The proof of an equation by rewriting its sides to their normal forms at a depth and proving
the rewritten equation by {lit}`p`. -/
def byNF (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (m : Internal.Depth) (p : Internal.Prover) : Internal.Prover := fun Γ Φ t u ↦ do
  let (t', dt, _) ← Internal.evalC G E n rs 4096 m Γ Φ t
  let (u', du, _) ← Internal.evalC G E n rs 4096 m Γ Φ u
  let q ← p Γ Φ t' u'
  pure (RoseTree.node .conv [RoseTree.node .cong [dt, du], q])

/-- The proof by normalization, weak head normal forms first, with the hypotheses as rewriting
rules before the rules given. -/
def normH (G : Internal.Globals) (E : Array Entry) (rs : List NormRule) : Internal.Prover :=
  fun Γ Φ t u ↦ Internal.byNormW G E 0 ((List.range Φ.length).map NormRule.hyp ++ rs) 1024 Γ Φ t u

end Geb.FreeTopos.Tactics

end
