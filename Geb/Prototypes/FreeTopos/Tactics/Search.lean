/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Tactics.Hypotheses
public import Geb.Prototypes.FreeTopos.Tactics.Induction
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Proof search

Tactics that choose their steps from the terms: the subterms outside binders and folds' starts
and steps, the variable a normal form is stuck on, and the arguments at which a hypothesis
equating abstractions matches; and the proof by the instances of the hypotheses found so, or else
by case analysis of a variable the sides are stuck on, each case the same way, to a depth.

## Main definitions

* {lit}`openSubterms`, {lit}`stuckVar`, {lit}`stuckVarC`, {lit}`appsOf`, {lit}`condParts` — the
  subterms, the variable they are stuck on, and the applications and conditionals among them.
* {lit}`matchesWith`, {lit}`matchesOf` — the arguments at which a pattern matches.
* {lit}`byInstsOnce`, {lit}`byInsts`, {lit}`byAuto` — the proof by the instances of hypotheses,
  and by case analysis of stuck variables.

## Tags

internal language, prover, tactic, proof search
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Geb.FreeTopos.Translation
open Internal (Term NormRule Entry Deriv)
open scoped FinEnum

/-- The subterms of a term outside its binders and its folds' starts and steps, each with its
context's extension, none. -/
def openSubterms : Term → List Term := RoseTree.para fun l cs ↦
  RoseTree.node l (cs.map (·.1)) :: match l with
    | .lam _ => []
    | .natRec | .listRec => (cs.drop 2).flatMap (·.2)
    | .roseRec _ => (cs.drop 1).flatMap (·.2)
    | _ => cs.flatMap (·.2)

/-- The variable a weak normal form is stuck on: the datum of a fold, or the scrutinee of a case
analysis, the primitive of index five, that is a variable, the first in preorder. -/
def stuckVar (skip : ℕ → Bool) (t : Term) : Option ℕ :=
  let subs := openSubterms t
  -- a case analysis's scrutinee first, then a fold's datum
  (subs.findSome? fun u ↦ match u.label, u.children with
    | .app, [f, m] => match f.label, m.label with
      | .arr 5 _, .var i => if skip i then none else some i
      | _, _ => none
    | _, _ => none).orElse fun _ ↦ subs.findSome? fun u ↦ match u.label, u.children with
    | .natRec, [_, _, m] | .listRec, [_, _, m] | .roseRec _, [_, m] => match m.label with
      | .var i => if skip i then none else some i
      | _ => none
    | _, _ => none

/-- Whether a term mentions the variable of an index. -/
def mentions (t : Term) (i : ℕ) : Bool := Internal.uses t i > 0

/-- The arguments at which a matching of the body of an abstraction of {lit}`k` variables matches
the subterms of a term, its other variables those of the context. -/
def matchesWith (m : ℕ → Term → List (Option Term) → Option (List (Option Term))) (k : ℕ)
    (t : Term) : List (List Term) :=
  let width := k + 64
  let σ₀ : List (Option Term) := (List.range width).map fun j ↦
    if j < k then none else some (v (j - k))
  ((openSubterms t).filterMap fun u ↦ do
    let σ ← m 0 u σ₀
    let σ ← (σ.take k).mapM id
    pure σ.reverse).eraseDups

/-- The arguments at which the body of an abstraction of {lit}`k` variables matches the subterms
of a term, the body folded into its matching once rather than at each subterm. -/
def matchesOf (body : Term) (k : ℕ) (t : Term) : List (List Term) :=
  matchesWith (RoseTree.para Internal.matchStep body) k t

/-- The proof of an equation by weak reduction with the instances of the hypotheses that are
equations of abstractions of one variable, at the arguments at which the left side's body, in
weak normal form, matches the sides' weak normal forms, each cut in. -/
def byInstsOnce (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) (hs : ℕ) (next : List NormRule → Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
  let (t', _, _) ← Internal.eval G E n rs 4096 m Γ Φ t
  let (u', _, _) ← Internal.eval G E n rs 4096 m Γ Φ u
  if t' = u' then byMode m G E n rs Γ Φ t u else
  let found := (List.range (min hs Φ.length)).filterMap fun h ↦ do
    let (F, _) ← Internal.eqParts (← Φ[h]?)
    match F.label, F.children with
    | .lam a, [b] =>
      let (bw, _, _) ← Internal.eval G E n rs 4096 m (a :: Γ) (Φ.map Internal.weaken1) b
      let αs := (matchesOf bw 1 t' ++ matchesOf bw 1 u').eraseDups
      if αs.isEmpty then none else some (h, αs)
    | _, _ => none
  let go := found.foldr (fun (h, αs) (k : List NormRule → Internal.Prover) extra ↦
      withInsts G E n rs h αs (fun ex ↦ k (extra ++ ex)) (m := m)) next
  if found.isEmpty then none else go [] Γ Φ t u

/-- The proof of an equation by {lit}`byInstsOnce` repeated, each round's instances rewriting
before the next looks for more, three rounds. -/
def byInsts (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) (hs : ℕ) : Internal.Prover :=
  let last (extra : List NormRule) : Internal.Prover := byMode m G E n (extra ++ rs)
  let round (next : List NormRule → Internal.Prover) (extra : List NormRule) : Internal.Prover :=
    fun Γ Φ t u ↦ (byMode m G E n (extra ++ rs) Γ Φ t u).orElse fun _ ↦
      byInstsOnce m G E n (extra ++ rs) hs (fun ex ↦ next (extra ++ ex)) Γ Φ t u
  round (round (round last)) []

/-- The proof of an equation by {lit}`byInsts` with the hypotheses it starts with, or else by
case analysis of a variable its normal forms are stuck on, a list or a coproduct, preferring the
scrutinee of a case analysis to the datum of a fold and a variable those hypotheses do not
mention, each case the same way, to a depth. -/
def byAuto (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) (d : ℕ)
    (m : Internal.Depth := .weak) : Internal.Prover := fun Γ₀ Φ₀ t₀ u₀ ↦
  let hs := Φ₀.length
  (d.rec (byInsts m G E n rs hs) fun _ rec Γ Φ t u ↦
  (byInsts m G E n rs hs Γ Φ t u).orElse fun _ ↦ do
    let (t', _, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', _, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    let skip (i : ℕ) : Bool := (Φ.take hs).any (mentions · i)
    let i ← ((stuckVar skip t').orElse fun _ ↦ stuckVar skip u').orElse fun _ ↦
      (stuckVar (fun _ ↦ false) t').orElse fun _ ↦ stuckVar (fun _ ↦ false) u'
    let c ← Γ[i]?
    match Internal.listPart c, Internal.coprodParts c with
    | some _, _ => byListSplit G n i rec rec Γ Φ t u
    | none, some _ => bySplit2 3 4 i rec rec Γ Φ t u
    | none, none => none : Internal.Prover) Γ₀ Φ₀ t₀ u₀

/-- The type, test, first branch and second branch of a conditional of the library. -/
def condParts (w : Term) : Option (Tree × Term × Term × Term) := match w.label, w.children with
  | .defn k [a], [d, y, c] => if k = D.cond then some (a, c, y, d) else none
  | _, _ => none

/-- The variable a weak normal form is stuck on, including the test of a folded conditional. -/
def stuckVarC (skip : ℕ → Bool) (t : Term) : Option ℕ :=
  ((openSubterms t).findSome? fun u ↦ match condParts u with
    | some (_, c, _, _) => match c.label with
      | .var i => if skip i then none else some i
      | _ => none
    | none => none).orElse fun _ ↦ stuckVar skip t

/-- The applications of the definition of index {lit}`k` to two arguments among a term's
subterms outside binders and folds' starts and steps. -/
def appsOf (k : ℕ) (t : Term) : List Term :=
  (openSubterms t).filter fun u ↦ match u.label, u.children with
    | .app, [f, _] => match f.label, f.children with
      | .app, [g, _] => g.label = .defn k []
      | _, _ => false
    | _, _ => false

end Geb.FreeTopos.Tactics

end
