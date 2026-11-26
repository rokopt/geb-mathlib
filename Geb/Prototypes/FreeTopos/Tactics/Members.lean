/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Tactics.Trees
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The case analysis of a member of a datatype

A datatype of the datatype language is the trees its recognizer accepts, and a statement about
its members takes the hypothesis that a tree is one: an equation that reduces, at a tree of a
label and children, by the recognizer's tests of the label, of the number of the children and of
the children. The tactics here prove an equation under such a hypothesis by cases on the
constructor of the member. The hypothesis is reverted, so that the goal carries it through the
case analysis of the tree, of the bits of its label and of its list of children; at each case it
is introduced again and reduced. At a label of no constructor, and at a number of children other
than a constructor's, it reduces to the equation of a tree of empty label with one of a label
that is not empty, from which every equation follows. At a list of more children than a
constructor of a fixed number of fields has, the recognizer's comparison of the list's length is
stuck on the length of the list's unknown tail; the tactic generalizes that length to a bitstring
and decides the comparison at each case of the bitstring's lowest bits.

## Main definitions

* {lit}`byRevert` — the proof of an equation from its implication by a hypothesis.
* {lit}`byLabelClash` — the proof of any equation from a hypothesis that equates a tree of empty
  label with a tree of a label that is not empty.
* {lit}`stuckLength` — the length on which the successors of a term are stuck.
* {lit}`withMember`, {lit}`refuteMember`, {lit}`refuteLonger` — the hypothesis introduced again
  and reduced, and the cases it refutes.
* {lit}`byFixed`, {lit}`byRest` — the cases of the children of a constructor of a fixed number of
  fields, and of one whose last field takes the remaining children.
* {lit}`byLabels` — the case analysis of a label to a number of bits, each label by its prover.
* {lit}`byMemberCases` — the case analysis of a member of a datatype.

## Tags

internal language, prover, tactic, datatype, recognizer, case analysis
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Geb.FreeTopos.Translation
open Internal (Term NormRule Entry ConvDeriv)
open scoped FinEnum

/-- The proof of an equation from its implication by the hypothesis of index {lit}`h`: the
implication of the equation by the hypothesis equals truth, by {lit}`p`, so that it holds, and
the equation follows from it and the hypothesis. A case analysis of a variable that the
hypothesis mentions, made by {lit}`p`, so reaches the hypothesis as it reaches the equation. The
connectives are the definitions from the index {lit}`o`, their rules the theorems from
{lit}`logicBase`. -/
def byRevert (o logicBase h : ℕ) (p : Internal.Prover) : Internal.Prover := fun Γ Φ t u ↦ do
  let ψ ← Φ[h]?
  let q := Term.eq t u
  let χ := Internal.Logic.imp o ψ q
  let tt := Internal.Logic.tt o
  let d ← p Γ Φ χ tt
  pure (RoseTree.node (.apply (logicBase + 4) [] [q, ψ])
    [RoseTree.node (.cut (Term.eq χ tt)) [d, RoseTree.node .conv
      [RoseTree.node (.rwHyp Φ.length false) [], Internal.Logic.trueIC]],
      RoseTree.node (.hyp h) []])

/-- The function of a tree and two values of the type {lit}`a` that is the conditional on the
tree's label between the two values: the second where the label is not empty and the first where
it is, or the reverse where {lit}`s` holds. -/
def labelPick (a : Tree) (s : Bool) : Term :=
  Term.lam treeTy (Term.lam a (Term.lam a (condT a (call D.lab [] [v 2])
    (v (if s then 1 else 0)) (v (if s then 0 else 1)))))

/-- The proof of an equation from the hypothesis of index {lit}`h`, the equation of two trees of
which the conditional on the label selects different branches: {name}`labelPick` at the first
tree is the function giving the first of two values, and at the second tree the function giving
the second, each by extensionality and reduction, so that the equation's sides are the values of
{name}`labelPick` at the two trees, which the hypothesis equates. The first tree's label is
empty and the second's is not where {lit}`s` does not hold, and the reverse where it does. -/
def labelClashWith (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (h : ℕ) (s : Bool) : Internal.Prover := fun Γ Φ t u ↦ do
  let a ← Internal.typeIn G n Γ t
  let (l₀, l₁) ← Internal.eqParts (← Φ[h]?)
  let P := labelPick a s
  let K₀ := Term.lam a (Term.lam a (v 1))
  let K₁ := Term.lam a (Term.lam a (v 0))
  let ext : Internal.Prover := Internal.byFunExt G n (Internal.byFunExt G n (byWeak G E n rs))
  let ψ₀ := Term.eq (Term.app P l₀) K₀
  let ψ₁ := Term.eq (Term.app P l₁) K₁
  let d₀ ← ext Γ Φ (Term.app P l₀) K₀
  let d₁ ← ext Γ (Φ ++ [ψ₀]) (Term.app P l₁) K₁
  let refl : ConvDeriv := RoseTree.node .refl []
  let beta : ConvDeriv := RoseTree.node .beta []
  let at2 (l : Term) : Term := Term.app (Term.app (Term.app P l) t) u
  let side (k : ℕ) : ConvDeriv := RoseTree.node .trans
    [RoseTree.node .cong [RoseTree.node .cong [RoseTree.node (.rwHyp k false) [], refl], refl],
      RoseTree.node .trans [RoseTree.node .cong [beta, refl], beta]]
  let dχ := RoseTree.node .join [RoseTree.node .cong [RoseTree.node .cong
    [RoseTree.node .cong [refl, RoseTree.node (.rwHyp h false) []], refl], refl], refl]
  pure (RoseTree.node (.cut ψ₀) [d₀, RoseTree.node (.cut ψ₁) [d₁,
    RoseTree.node (.convFrom (Term.eq (at2 l₀) (at2 l₁)))
      [RoseTree.node .cong [side Φ.length, side (Φ.length + 1)], dχ]]])

/-- The proof of an equation from the hypothesis of index {lit}`h`, the equation of a tree of
empty label with a tree of a label that is not empty, in either order. -/
def byLabelClash (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) (h : ℕ) :
    Internal.Prover := fun Γ Φ t u ↦
  (labelClashWith G E n rs h false Γ Φ t u).orElse fun _ ↦ labelClashWith G E n rs h true Γ Φ t u

/-- The argument of an application of the library's successor that is not itself one. -/
def succArg (u : Term) : Option Term := match u.label, u.children with
  | .defn k _, [a] => if k = D.succ then match a.label with
      | .defn k' _ => if k' = D.succ then none else some a
      | _ => some a
    else none
  | _, _ => none

/-- The term on which the successors of a term are stuck, the first in preorder outside binders
and folds' starts and steps: in the normal form of a recognizer's test at a list of children with
an unknown tail, the successor kept folded, the length of that tail. -/
def stuckLength (t : Term) : Option Term := (openSubterms t).findSome? succArg

/-- The proof of an equation whose sides reduce, at their heads, to an implication of an equation
and to truth, as {name}`byImpI` proves it: the implication's antecedent is introduced and then
cut in in normal form, by the rules {lit}`rs`, and the conclusion's sides are proved by {lit}`k`
under the hypotheses, the last of them that normal form. -/
def withMember (G : Internal.Globals) (E : Array Entry) (n o logicBase : ℕ) (rs : List NormRule)
    (k : Internal.Prover) : Internal.Prover :=
  byImpI G E o logicBase fun Γ Φ t u ↦
    withWeakHyps G E n rs [Φ.length - 1] (fun _ ↦ k) (m := .full) Γ Φ t u

/-- The proof of an equation whose sides reduce to an implication of an equation and to truth,
where the antecedent's normal form equates a tree of empty label with a tree of a label that is
not empty: a hypothesis of membership at a tree that is no member. -/
def refuteMember (G : Internal.Globals) (E : Array Entry) (n o logicBase : ℕ)
    (rs : List NormRule) : Internal.Prover :=
  withMember G E n o logicBase rs fun Γ Φ t u ↦ byLabelClash G E n rs (Φ.length - 1) Γ Φ t u

/-- The proof of an equation whose sides reduce to an implication of an equation and to truth,
where the antecedent is a hypothesis of membership at a tree of more children than its
constructor has fields. The antecedent's normal form by the rules {lit}`rsS`, which keep the
successor folded, holds the comparison of the successors of a length with a numeral
({name}`stuckLength`). That normal form is reverted, the length generalized to a bitstring and
the bitstring split to {lit}`e` bits, at each case of which the antecedent is refuted
({name}`refuteMember`). -/
def refuteLonger (G : Internal.Globals) (E : Array Entry) (n o logicBase : ℕ)
    (rs rsS : List NormRule) (e : ℕ) : Internal.Prover :=
  withMember G E n o logicBase rsS fun Γ Φ t u ↦ do
    let s ← (Φ[Φ.length - 1]?).bind stuckLength
    byRevert o logicBase (Φ.length - 1)
      (byGeneralize bitsTy s (byBits G (refuteMember G E n o logicBase rs) e 0)) Γ Φ t u

/-- The proof of an equation by case analysis of the list variable of index {lit}`i` to {lit}`a`
elements: each shorter list by {lit}`short`, and the list of {lit}`a` elements before a list,
that list the variable of the index it is given, by {lit}`last`. -/
def byChildren (G : Internal.Globals) (short : Internal.Prover) (last : ℕ → Internal.Prover) :
    ℕ → ℕ → Internal.Prover :=
  fun a ↦ a.rec last fun _ rec i ↦ byListSplit G 0 i short (rec 0)

/-- The cases of the children of a constructor of {lit}`a` fields, at the list of children of
index {lit}`i`: fewer children and more refute the hypothesis of membership, the latter with the
length split to {lit}`e` bits, and at {lit}`a` children the hypothesis is introduced in normal
form and the equation proved by {lit}`p`. -/
def byFixed (G : Internal.Globals) (E : Array Entry) (n o logicBase : ℕ) (rs rsS : List NormRule)
    (a e : ℕ) (p : Internal.Prover) : ℕ → Internal.Prover :=
  byChildren G (refuteMember G E n o logicBase rs)
    (fun i ↦ byListSplit G 0 i (withMember G E n o logicBase rs p)
      (refuteLonger G E n o logicBase rs rsS e)) a

/-- The cases of the children of a constructor of {lit}`a` fields before a last field that takes
the remaining children, at the list of children of index {lit}`i`: fewer children refute the
hypothesis of membership, and at {lit}`a` children before a list the hypothesis is introduced in
normal form and the equation proved by {lit}`p`. -/
def byRest (G : Internal.Globals) (E : Array Entry) (n o logicBase : ℕ) (rs : List NormRule)
    (a : ℕ) (p : Internal.Prover) : ℕ → Internal.Prover :=
  byChildren G (refuteMember G E n o logicBase rs) (fun _ ↦ withMember G E n o logicBase rs p) a

/-- The proof of an equation by case analysis of the bitstring variable of index {lit}`pos` to
{lit}`d` bits, a label: at the bitstring of each label of fewer bits by the prover {lit}`p` gives
the label, and at each of {lit}`d` bits before a bitstring by {lit}`q`. The label of the bits
taken so far is one less than {lit}`acc`, the weight of the next bit is {lit}`w`, and {lit}`p` is
also given {lit}`c`, the index of a variable of the context the case analysis starts in, three
more at each bit taken. -/
def byLabels (G : Internal.Globals) (p : ℕ → ℕ → Internal.Prover) (q : Internal.Prover) :
    ℕ → ℕ → ℕ → ℕ → ℕ → Internal.Prover :=
  fun d ↦ d.rec (fun _ _ _ _ ↦ q) fun _ rec pos acc w c ↦
    byListSplit G 0 pos (p (acc - 1) c)
      (bySplit2 3 4 1 (rec 1 (acc + w) (2 * w) (c + 3)) (rec 1 (acc + 2 * w) (2 * w) (c + 3)))

/-- The proof of an equation by cases on the constructor of the tree variable of index {lit}`i`,
under the hypothesis of index {lit}`h` that it is a member of a datatype. The hypothesis is
reverted ({name}`byRevert`), the tree split into its label and its list of children
({name}`byTreeSplit`, Lambek's lemma the entry of index {lit}`lk`) and the label into {lit}`d`
bits ({name}`byLabels`). At the label of a constructor the equation's implication by the
hypothesis is proved by the prover {lit}`clause` gives the label and the index of the list of
children ({name}`byFixed`, {name}`byRest`), and at any other label by {lit}`q`
({name}`refuteMember`). -/
def byMemberCases (G : Internal.Globals) (o logicBase lk h i d : ℕ)
    (clause : ℕ → ℕ → Internal.Prover) (q : Internal.Prover) : Internal.Prover :=
  byRevert o logicBase h (byTreeSplit lk i (byLabels G clause q d 1 1 1 0))

end Geb.FreeTopos.Tactics

end
