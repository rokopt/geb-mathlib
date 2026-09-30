/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Tactics.Reduction
public import Geb.Prototypes.FreeTopos.Translation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Proofs by induction and case analysis

Induction and case analysis on the variables of an equation's context — lists, bitstrings, rose
trees and coproducts — each case by a prover, built from
{name}`Geb.FreeTopos.Internal.byListIndWith`, {name}`Geb.FreeTopos.Internal.bySplit` and
extensionality. The case analysis of a variable other than the innermost abstracts the sides over
it, proves the abstractions equal by extensionality and the case analysis of a new variable, and
applies them to the variable.

## Main definitions

* {lit}`funExts` — a prover under new variables of a statement's arguments.
* {lit}`byListIndWeak`, {lit}`byRoseIndWith` — induction on a list and on a rose tree in the form
  of the uniqueness of the fold.
* {lit}`byListSplit`, {lit}`bySplit2`, {lit}`byListCases` — the case analysis of a list or a
  coproduct variable.
* {lit}`bitsInd`, {lit}`bitsCases`, {lit}`byBits`, {lit}`byLength3` — induction and case analysis
  on bitstrings, and the case analysis of a list to a length.

## Tags

internal language, prover, tactic, induction, case analysis
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Geb.FreeTopos.Translation
open Internal (Term NormRule Entry Deriv)
open scoped FinEnum

/-- A prover under {lit}`k` new variables of the statement's arguments, by extensionality. -/
def funExts (k : ℕ) (G : Internal.Globals) (p : Internal.Prover) : Internal.Prover :=
  (List.replicate k ()).foldr (fun _ q ↦ Internal.byFunExt G 0 q) p

/-- The proof of an equation in a context of a list variable by induction on it in the form of
the uniqueness of its fold, with the step {lit}`s`, each premise by weak reduction. -/
def byListIndWeak (G : Internal.Globals) (E : Array Entry) (n : ℕ) (s : Term)
    (rs : List NormRule) : Internal.Prover := fun Γ Φ t u ↦ match Γ with
  | c :: Γ' => do
    let a ← Internal.listPart c
    let Φ' ← Internal.lowerHyps G n Γ' Φ
    let z := Internal.instVar (Term.arr 0 [a] Term.star)
    let p₀ ← byWeak G E n rs Γ' Φ' (Term.subst t z) (Term.subst u z)
    let p₁ ← byWeak G E n rs (c :: a :: Γ') (Φ'.map Internal.weaken2) (Internal.listConsAt 1 a t)
      (Term.subst s (Internal.atVar0 (Internal.weakenElem t)))
    let p₂ ← byWeak G E n rs (c :: a :: Γ') (Φ'.map Internal.weaken2) (Internal.listConsAt 1 a u)
      (Term.subst s (Internal.atVar0 (Internal.weakenElem u)))
    pure (RoseTree.node (.listInd 0 1 s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a rose tree alone by induction on it in the form of
the uniqueness of its fold, with the step {lit}`s`, each premise by {lit}`p`. -/
def byRoseIndWith (G : Internal.Globals) (n : ℕ) (s : Term) (p : Internal.Prover) :
    Internal.Prover := fun Γ _ t u ↦ match Γ with
  | [r] => do
    let (a, _) ← Internal.roseParts r
    let C ← Internal.typeIn G n Γ t
    let p₁ ← p [list r, a] [] (Internal.roseNodeAt 2 r a t)
      (Term.subst s (Internal.atVar0 (Internal.roseMapAt 0 1 C t)))
    let p₂ ← p [list r, a] [] (Internal.roseNodeAt 2 r a u)
      (Term.subst s (Internal.atVar0 (Internal.roseMapAt 0 1 C u)))
    pure (RoseTree.node (.roseInd 2 0 1 s) [p₁, p₂])
  | _ => none

/-- The proof of an equation by case analysis of the list variable of index {lit}`i`: the sides
abstracted over it are equal functions, by extensionality and list induction on the new variable,
each case by its prover, and the equation follows by applying them to the variable. -/
def byListSplit (G : Internal.Globals) (n i : ℕ) (p₀ p₁ : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let c ← Γ[i]?
    let F := Internal.abstractVar i c t
    let H := Internal.abstractVar i c u
    let q ← Internal.byListIndWith G n 0 1 p₀ p₁ (c :: Γ) (Φ.map Internal.weaken1)
      (Term.app (Internal.weaken1 F) (v 0)) (Term.app (Internal.weaken1 H) (v 0))
    let χ := Term.eq (Term.app F (v i)) (Term.app H (v i))
    pure (RoseTree.node (.cut (Term.eq F H)) [RoseTree.node .funExt [q],
      RoseTree.node (.convFrom χ) [RoseTree.node .cong [RoseTree.node .beta [],
        RoseTree.node .beta []], RoseTree.node .join [RoseTree.node .cong
          [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []],
          RoseTree.node .refl []]]])

/-- The proof of an equation by case analysis of the variable of index {lit}`i`, of a
coproduct whose injections are the primitives of indices {lit}`kl` and {lit}`kr`, the first case
by {lit}`p₀` and the second by {lit}`p₁`, as {name}`Geb.FreeTopos.Internal.bySplit` proves it. -/
def bySplit2 (kl kr i : ℕ) (p₀ p₁ : Internal.Prover) : Internal.Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let (a, b) ← Internal.coprodParts c
  let F := Internal.abstractVar i c t
  let H := Internal.abstractVar i c u
  let inj (k : ℕ) (s : Term) : Term := Term.app (Internal.weaken1 s) (Term.arr k [a, b] (v 0))
  let q₀ ← p₀ (a :: Γ) (Φ.map Internal.weaken1) (inj kl F) (inj kl H)
  let q₁ ← p₁ (b :: Γ) (Φ.map Internal.weaken1) (inj kr F) (inj kr H)
  let χ := Term.eq (Term.app F (v i)) (Term.app H (v i))
  pure (RoseTree.node (.cut (Term.eq F H)) [RoseTree.node .funExt
    [RoseTree.node (.coprodInd kl kr) [q₀, q₁]], RoseTree.node (.convFrom χ)
      [RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []],
        RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp Φ.length false) [],
          RoseTree.node .refl []], RoseTree.node .refl []]]])

/-- The proof of an equation by case analysis of its innermost variable, a list: empty, or an
element before a list, each case by {lit}`p`. -/
def byListCases (G : Internal.Globals) (n : ℕ) (p : Internal.Prover) : Internal.Prover :=
  Internal.byListIndWith G n 0 1 p p

/-- The proof by induction on a bitstring, the empty one by {lit}`p₀` and a construction by case
analysis of its bit, each case by {lit}`p₁`. -/
def bitsInd (G : Internal.Globals) (n : ℕ) (p₀ p₁ : Internal.Prover) : Internal.Prover :=
  Internal.byListIndWith G n 0 1 p₀ (Internal.bySplit 3 4 1 p₁)

/-- The proof of an equation by case analysis of its innermost variable, a bitstring: empty, or
a bit before a bitstring, the bit's two cases, each by {lit}`p`. -/
def bitsCases (G : Internal.Globals) (n : ℕ) (p : Internal.Prover) : Internal.Prover :=
  bitsInd G n p p

/-- The proof of an equation by case analysis on the bitstring variable of index {lit}`i`, to
{lit}`d` bits, each case by {lit}`p`. -/
def byBits (G : Internal.Globals) (p : Internal.Prover) : ℕ → ℕ → Internal.Prover :=
  fun d ↦ d.rec (fun _ ↦ p) fun _ rec i ↦
    byListSplit G 0 i p (bySplit2 3 4 1 (rec 1) (rec 1))

/-- The proof of an equation in a context whose list variable of index {lit}`i` is split to three
elements, each shorter or longer list by {lit}`q` and the three elements' case by {lit}`p`. -/
def byLength3 (G : Internal.Globals) (i : ℕ) (p q : Internal.Prover) : Internal.Prover :=
  byListSplit G 0 i q (byListSplit G 0 0 q (byListSplit G 0 0 q (byListSplit G 0 0 p q)))

end Geb.FreeTopos.Tactics

end
