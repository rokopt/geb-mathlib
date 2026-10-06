/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Tactics.Search
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Proofs about trees

Tactics for the translation's type of trees ({name}`Geb.FreeTopos.Translation.treeTy`): the
unfolding of a tree to its label and children, the case analysis of a tree variable by Lambek's
lemma, proof search that also splits trees and folded conditionals' tests, the abstraction of a
term's occurrences and the generalization over them, and the rewriting under a conditional's mask
by an absorption lemma.

## Main definitions

* {lit}`unnodeTy`, {lit}`unnodeU` — the unfolding of a tree.
* {lit}`byTreeSplit` — the case analysis of a tree variable.
* {lit}`byAutoT`, {lit}`byAutoC` — proof search that splits trees, and conditionals' tests.
* {lit}`abstractTerm`, {lit}`byGeneralize` — the abstraction of a term's occurrences, and the
  generalization over them.
* {lit}`maskRwD`, {lit}`maskRw`, {lit}`maskSub`, {lit}`byMaskSubs` — the rewriting under a mask.

## Tags

internal language, prover, tactic, rose tree, Lambek's lemma
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Geb.FreeTopos.Translation
open Internal (Term NormRule Entry Deriv)
open scoped FinEnum

/-- The type the unfolding of trees folds into: the pair of a label and the list of the
children. -/
def unnodeTy : Tree := prod bitsTy (list treeTy)

/-- The step of the unfolding of trees, the library's. -/
def unnodeStep : Term := match lib[D.unnode]? with
  | some d => d.body.children.headD Term.star
  | none => Term.star

/-- The unfolding of a tree. -/
def unnodeU (t : Term) : Term := Term.roseRec unnodeTy unnodeStep t

/-- The rewriting of a term in which a tree rebuilt from the unfolding of its variable of index
{lit}`i` stands for the variable, back to the term: at each occurrence of the variable, the pair
of the unfolding's components is the unfolding, and the tree rebuilt from it is the variable,
Lambek's lemma of index {lit}`lk`. A rose-tree fold's step, in a context of its own, does not
mention it. -/
def occRewrite (lk i : ℕ) : Term → ℕ → Deriv := RoseTree.para fun l cs d ↦
  let refl : Deriv := RoseTree.node .refl []
  let j := i + d
  match l with
  | .var k =>
    if k = j then RoseTree.node .trans [RoseTree.node .cong [RoseTree.node .pairEta []],
      RoseTree.node (.thm lk [] [Term.var j] false) []]
    else refl
  | .lam _ => RoseTree.node .cong (cs.map fun (_, r) ↦ r (d + 1))
  | .natRec => RoseTree.node .cong (cs.zipIdx.map fun ((_, r), k) ↦
      r (if k = 1 then d + 1 else d))
  | .listRec => RoseTree.node .cong (cs.zipIdx.map fun ((_, r), k) ↦
      r (if k = 1 then d + 2 else d))
  | .roseRec _ => RoseTree.node .cong (cs.zipIdx.map fun ((_, r), k) ↦
      if k = 1 then r d else refl)
  | _ =>
    if cs.all fun (c, _) ↦ Internal.uses c j = 0 then refl
    else RoseTree.node .cong (cs.map fun (_, r) ↦ r d)

/-- The proof of an equation by case analysis on the tree variable of index {lit}`i`: the sides
at a tree of a new label and new children are proved by {lit}`p`, so that, by extensionality,
their abstractions over the label and the children are equal functions; applied to the
components of the variable's unfolding, they are the sides at the tree rebuilt from it, which
is the variable by Lambek's lemma, the entry of index {lit}`lk`. -/
def byTreeSplit (lk i : ℕ) (p : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let c ← Γ[i]?
    if c ≠ treeTy then none else
    let F := Internal.abstractVar i c t
    let H := Internal.abstractVar i c u
    let N₀ := nodeT (Term.pair (v 1) (v 0))
    let A := Term.app (Internal.weaken2 F) N₀
    let B := Term.app (Internal.weaken2 H) N₀
    let q ← p (list treeTy :: bitsTy :: Γ) (Φ.map Internal.weaken2) A B
    let Fl := Term.lam bitsTy (Term.lam (list treeTy) A)
    let Hl := Term.lam bitsTy (Term.lam (list treeTy) B)
    let beta : Deriv := RoseTree.node .beta []
    let refl : Deriv := RoseTree.node .refl []
    let betaBoth : Deriv := RoseTree.node .cong [beta, beta]
    let dG := RoseTree.node .funExt [RoseTree.node .conv [betaBoth,
      RoseTree.node .funExt [RoseTree.node .conv [betaBoth, q]]]]
    let U := unnodeU (v i)
    let applied (L : Term) : Term := Term.app (Term.app L (Term.fst U)) (Term.snd U)
    let χ := Term.eq (applied Fl) (applied Hl)
    let side (w : Term) : Deriv := RoseTree.node .trans [RoseTree.node .cong [beta, refl],
      RoseTree.node .trans [beta, RoseTree.node .trans [beta, occRewrite lk i w 0]]]
    let dχ := RoseTree.node .join [RoseTree.node .cong [RoseTree.node .cong
      [RoseTree.node (.rwHyp Φ.length false) [], refl], refl], refl]
    pure (RoseTree.node (.cut (Term.eq Fl Hl))
      [dG, RoseTree.node (.convFrom χ) [RoseTree.node .cong [side t, side u], dχ]])

/-- The proof of an equation by case analysis of the variable of index {lit}`i`, a list, a
coproduct or a tree, each case by {lit}`rec`; Lambek's lemma is the entry of index {lit}`lk`. -/
def splitStuck (G : Internal.Globals) (n lk i : ℕ) (rec : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let c ← Γ[i]?
    match Internal.listPart c, Internal.coprodParts c with
    | some _, _ => byListSplit G n i rec rec Γ Φ t u
    | none, some _ => bySplit2 3 4 i rec rec Γ Φ t u
    | none, none => if c = treeTy then byTreeSplit lk i rec Γ Φ t u else none

/-- The proof of an equation by reducing both sides to one normal form, with the instances of the
hypotheses it starts with where there are any, or else by case analysis of a variable the normal
forms are stuck on, a list, a coproduct or a tree, each case the same way, to a depth; Lambek's
lemma is the entry of index {lit}`lk`. Each goal's sides are reduced once. -/
def byAutoT (G : Internal.Globals) (E : Array Entry) (n lk : ℕ) (rs : List NormRule) (d : ℕ)
    (m : Internal.Depth := .weak) : Internal.Prover := fun Γ₀ Φ₀ t₀ u₀ ↦
  let hs := Φ₀.length
  let direct : Internal.Prover := fun Γ Φ t u ↦ do
    let (t', dt, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', du, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    if t' = u' then some (RoseTree.node .join [dt, du]) else none
  let solve : Internal.Prover := fun Γ Φ t u ↦ (direct Γ Φ t u).orElse fun _ ↦
    if hs = 0 then none else byInsts m G E n rs hs Γ Φ t u
  (d.rec solve fun _ rec Γ Φ t u ↦ do
    let (t', dt, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', du, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    if t' = u' then some (RoseTree.node .join [dt, du]) else
    (if hs = 0 then none else byInsts m G E n rs hs Γ Φ t u).orElse fun _ ↦ do
    let skip (i : ℕ) : Bool := (Φ.take hs).any (mentions · i)
    let i ← ((stuckVar skip t').orElse fun _ ↦ stuckVar skip u').orElse fun _ ↦
      (stuckVar (fun _ ↦ false) t').orElse fun _ ↦ stuckVar (fun _ ↦ false) u'
    splitStuck G n lk i rec Γ Φ t u : Internal.Prover) Γ₀ Φ₀ t₀ u₀

/-- The proof of an equation by reducing both sides to one normal form, or else by case analysis
of a variable the normal forms are stuck on, a folded conditional's test among them, each case
the same way, to a depth. -/
def byAutoC (G : Internal.Globals) (E : Array Entry) (n lk : ℕ) (rs : List NormRule) (d : ℕ) :
    Internal.Prover :=
  d.rec (byWeak G E n rs) fun _ rec Γ Φ t u ↦ (byWeak G E n rs Γ Φ t u).orElse fun _ ↦ do
    let (t', _, _) ← Internal.eval G E n rs 4096 .weak Γ Φ t
    let (u', _, _) ← Internal.eval G E n rs 4096 .weak Γ Φ u
    let i ← (stuckVarC (fun _ ↦ false) t').orElse fun _ ↦ stuckVarC (fun _ ↦ false) u'
    splitStuck G n lk i rec Γ Φ t u

/-- The abstraction, over a new variable of the type {lit}`b`, of a term's occurrences of the
term {lit}`x`: the function whose application to {lit}`x` is the term. A rose-tree fold's step,
in a context of its own, is left in place. -/
def abstractTerm (b : Tree) (x y : Term) : Term :=
  let xw := Internal.weaken1 x
  let go : Term → ℕ → Term := RoseTree.para fun l cs d ↦
    if RoseTree.node l (cs.map (·.1)) = Term.rename xw (· + d) then Term.var d else
    match l with
    | .lam _ => RoseTree.node l (cs.map fun (_, r) ↦ r (d + 1))
    | .natRec => RoseTree.node l (cs.zipIdx.map fun ((_, r), k) ↦
        r (if k = 1 then d + 1 else d))
    | .listRec => RoseTree.node l (cs.zipIdx.map fun ((_, r), k) ↦
        r (if k = 1 then d + 2 else d))
    | .roseRec _ => RoseTree.node l (cs.zipIdx.map fun ((c, r), k) ↦
        if k = 1 then r d else c)
    | _ => RoseTree.node l (cs.map fun (_, r) ↦ r d)
  Term.lam b (go (Internal.weaken1 y) 0)

/-- The proof that a conditional of the type {lit}`a` on the test {lit}`c`, between {lit}`y` and
{lit}`d`, is the conditional between {lit}`y` with {lit}`x'` for {lit}`x` and {lit}`d`: by the
absorption lemma of index {lit}`ab`, the occurrences of {lit}`x`, of the type {lit}`b`, are the
conditional on the same test between {lit}`x` and {lit}`z`, which {lit}`dM` rewrites to the
conditional between {lit}`x'` and {lit}`z`, which absorption removes. -/
def maskRwD (a b : Tree) (ab : ℕ) (dM : Deriv) (c d x x' z y : Term) : Deriv :=
  let F := abstractTerm b x y
  let refl : Deriv := RoseTree.node .refl []
  let beta : Deriv := RoseTree.node .beta []
  let χ := Term.eq (condT a c (Term.app F x) d) (condT a c (Term.app F x') d)
  let dχ := RoseTree.node .join [RoseTree.node .trans
    [RoseTree.node (.thm ab [a, b] [c, d, x, z, F] true) [],
      RoseTree.node .trans [RoseTree.node .cong [refl, RoseTree.node .cong [refl, dM], refl],
        RoseTree.node (.thm ab [a, b] [c, d, x', z, F] false) []]], refl]
  RoseTree.node (.convFrom χ) [RoseTree.node .cong
    [RoseTree.node .cong [refl, beta, refl], RoseTree.node .cong [refl, beta, refl]], dχ]

/-- The proof that a conditional of the type {lit}`a` on the test {lit}`c`, between {lit}`y` and
{lit}`d`, is the conditional between {lit}`y` with {lit}`x'` for {lit}`x` and {lit}`d`, by
{name}`maskRwD`, the rewriting the masked lemma of index {lit}`j` at the objects {lit}`θ` and the
terms {lit}`σ`. -/
def maskRw (a b : Tree) (ab j : ℕ) (θ : List Tree) (σ : List Term) (c d x x' z y : Term) :
    Deriv :=
  maskRwD a b ab (RoseTree.node (.thm j θ σ false) []) c d x x' z y

/-- The rewriting of the conditional subterm {lit}`S`, of the type {lit}`a` on the test {lit}`c`
between {lit}`y` and {lit}`d`, by the hypothesis of index {lit}`i`, where its first term is a
conditional on the same test whose first branch {lit}`y` mentions: the subterm, its rewriting and
the derivation of their equation, as {lit}`maskSub` describes. -/
def maskAt (ab cs : ℕ) (Φ : List Term) (a : Tree) (c y d S : Term) (i : ℕ) :
    Option (Term × Term × Deriv) := do
  let (L, R) ← Internal.eqParts (← Φ[i]?)
  let (b, c', x, z) ← condParts L
  if c' ≠ c then none else
  let (x', dM) ← match condParts R with
    | some (_, c'', x', z') =>
      if c'' = c ∧ z' = z then some (x', RoseTree.node (.rwHyp i false) []) else none
    | none =>
      if R = z then some (R, RoseTree.node .trans [RoseTree.node (.rwHyp i false) [],
        RoseTree.node (.thm cs [b] [c, R] true) []]) else none
  if x = x' then none else
  let F := abstractTerm b x y
  let body ← F.children.head?
  if Internal.uses body 0 = 0 then none else
  let S' := condT a c (Term.subst body (Internal.instVar x')) d
  pure (S, S', maskRwD a b ab dM c d x x' z y)

/-- The rewriting of the first conditional subterm of a term whose test is that of one of the
hypotheses, the latest first, and whose first branch mentions that hypothesis's first term: the
subterm, its rewriting and the derivation of their equation, by the absorption lemma of index
{lit}`ab` and the condition lemma of index {lit}`cs`. A hypothesis equates a conditional with a
conditional on its test with another first branch and the same second, or with a term that is
its second branch, which the condition lemma makes the conditional between it and itself. -/
def maskSub (ab cs : ℕ) (Φ : List Term) (w : Term) : Option (Term × Term × Deriv) :=
  (openSubterms w).findSome? fun S ↦ do
    let (a, c, y, d) ← condParts S
    (List.range Φ.length).reverse.findSome? (maskAt ab cs Φ a c y d S)

/-- The proof of an equation by rewriting under masks by the hypotheses, as
{lit}`maskSub` finds them in either side, up to {lit}`n` times, each rewriting cut in and added as
a rule for the later rounds' reductions, and then by {lit}`p` with the rules added. -/
def byMaskSubs (G : Internal.Globals) (E : Array Entry) (ab cs : ℕ) (rs : List NormRule) :
    ℕ → (List NormRule → Internal.Prover) → Internal.Prover :=
  fun n ↦ (n.rec (fun extra p ↦ p extra) fun _ rec extra p ↦
    byNF G E 0 (extra ++ rs) .weak fun Γ Φ t u ↦
      match (maskSub ab cs Φ t).orElse fun _ ↦ maskSub ab cs Φ u with
      | none => p extra Γ Φ t u
      | some (S, S', dS) =>
        match rec (.hyp Φ.length :: extra) p Γ (Φ ++ [Term.eq S S']) t u with
        | some q => some (RoseTree.node (.cut (Term.eq S S')) [dS, q])
        | none => none :
    List NormRule → (List NormRule → Internal.Prover) → Internal.Prover) []

/-- The proof of an equation by generalizing the term {lit}`c`, of the type {lit}`a`: the sides
abstracted over its occurrences are equal functions, by extensionality and {lit}`p` at a new,
innermost variable, and the equation follows, cut in as a hypothesis, by applying them to the
term. -/
def byGeneralize (a : Tree) (c : Term) (p : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let F := abstractTerm a c t
    let H := abstractTerm a c u
    let q ← p (a :: Γ) (Φ.map Internal.weaken1) (Term.app (Internal.weaken1 F) (v 0))
      (Term.app (Internal.weaken1 H) (v 0))
    let refl : Deriv := RoseTree.node .refl []
    let dχ := RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []]
    let pχ := RoseTree.node .join [RoseTree.node .cong
      [RoseTree.node (.rwHyp Φ.length false) [], refl], refl]
    let χ := Term.eq (Term.app F c) (Term.app H c)
    pure (RoseTree.node (.cut (Term.eq F H)) [RoseTree.node .funExt [q],
      RoseTree.node (.convFrom χ) [dχ, pχ]])

end Geb.FreeTopos.Tactics

end
