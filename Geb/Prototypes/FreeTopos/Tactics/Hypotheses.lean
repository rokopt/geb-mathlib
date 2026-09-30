/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Tactics.Reduction
public import Geb.Prototypes.FreeTopos.Translation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Proofs with hypotheses

Tactics that bring hypotheses into a proof: an equation among the hypotheses cut in in normal form
and used as a rewriting rule, the induction hypothesis among them; the instances of a hypothesis
that equates functions, at arguments; the hypotheses at the children of an induction on rose
trees; the case analysis of a list variable that a hypothesis mentions, the hypothesis reverted;
and the introduction and elimination of implications equal to truth, the connectives' definitions
and their rules at given indices ({name}`Geb.FreeTopos.Internal.Logic.impI`).

## Main definitions

* {lit}`withWeakHyps`, {lit}`withInsts`, {lit}`withChildHyps` — hypotheses and their instances
  as rewriting rules.
* {lit}`byListIndHypWeak`, {lit}`byBitsIndHyp` — induction with the induction hypothesis as a
  rewriting rule.
* {lit}`revertCase` — the case analysis of a list variable that a hypothesis mentions.
* {lit}`byImpI`, {lit}`withImpElim` — the introduction and the elimination of implications.
* {lit}`bySuccPred` — the rewriting of a successor's predecessor backward by a theorem.

## Tags

internal language, prover, tactic, hypothesis, implication
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Tactics

open Geb.PartialHorn (Tree)
open Geb.FreeTopos.Translation
open Internal (Term NormRule Entry Deriv)
open scoped FinEnum

/-- The proof of an equation with the hypotheses of the given indices, equations, cut in in weak
normal form and used as rewriting rules before those given to {lit}`k`. -/
def withWeakHyps (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (is : List ℕ) (k : List NormRule → Internal.Prover) (m : Internal.Depth := .weak) :
    Internal.Prover := fun Γ Φ t u ↦
  (is.foldr (fun i (acc : List Term → List NormRule → Option Deriv) Φ₁ extra ↦ do
      let (a, b) ← Internal.eqParts (← Φ₁[i]?)
      let (a', da, _) ← Internal.eval G E n rs 4096 m Γ Φ₁ a
      let (b', db, _) ← Internal.eval G E n rs 4096 m Γ Φ₁ b
      let ψ := Term.eq a' b'
      let rest ← acc (Φ₁ ++ [ψ]) (extra ++ [.hyp Φ₁.length])
      pure (RoseTree.node (.cut ψ) [RoseTree.node (.convFrom (Term.eq a b))
        [RoseTree.node .cong [da, db], RoseTree.node (.hyp i) []], rest]))
    (fun Φ₁ extra ↦ k extra Γ Φ₁ t u)) Φ []

/-- The proof of an equation in a context of a list variable by induction on it with the induction
hypothesis, each case by weak reduction, the construction's with the hypothesis in weak normal
form as a rewriting rule. -/
def byListIndHypWeak (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) :
    Internal.Prover :=
  Internal.byListIndWith G n 0 1 (byWeak G E n rs) fun Γ Φ t u ↦
    withWeakHyps G E n rs [Φ.length - 1] (fun extra ↦ byWeak G E n (extra ++ rs)) (m := .weak)
      Γ Φ t u

/-- The proof of an equation in a context of a list variable by induction on it with the induction
hypothesis, the construction's case by case analysis of its bit, each case by reduction to a
depth, the construction's with the hypothesis in normal form as a rewriting rule. -/
def byBitsIndHyp (G : Internal.Globals) (E : Array Entry) (rs : List NormRule)
    (m : Internal.Depth) : Internal.Prover :=
  Internal.byListIndWith G 0 0 1 (byMode m G E 0 rs)
    (Internal.bySplit 3 4 1 fun Γ Φ t u ↦ withWeakHyps G E 0 rs [Φ.length - 1]
      (fun extra ↦ byMode m G E 0 (extra ++ rs)) (m := m) Γ Φ t u)

/-- A derivation rewriting the function of an application to arguments by the hypothesis of
index {lit}`i`. -/
def rwFun (i : ℕ) : ℕ → Deriv :=
  Nat.rec (RoseTree.node (.rwHyp i false) []) fun _ d ↦
    RoseTree.node .cong [d, RoseTree.node .refl []]

/-- The proof of an equation with the instances of the hypothesis of index {lit}`h`, an
equation of functions, at the lists of arguments {lit}`αs`, each cut in and then in weak normal
form, as rewriting rules before those given to {lit}`k`. -/
def withInsts (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) (h : ℕ)
    (αs : List (List Term)) (k : List NormRule → Internal.Prover) (m : Internal.Depth := .weak) :
    Internal.Prover :=
  fun Γ Φ t u ↦ do
    let (F, H) ← Internal.eqParts (← Φ[h]?)
    let insts := αs.map fun α ↦ Term.eq (apps F α) (apps H α)
    let rest ← withWeakHyps G E n rs ((List.range αs.length).map (Φ.length + ·)) k (m := m) Γ
      (Φ ++ insts) t u
    pure ((αs.zip insts).foldr (fun (α, q) r ↦ RoseTree.node (.cut q)
      [RoseTree.node .join [rwFun h α.length, RoseTree.node .refl []], r]) rest)

/-- The induction hypothesis at the children: for the hypothesis of index {lit}`h`, that the
two lists of formulas its sides fold from the list of children are equal, the formula at each
child among the first {lit}`k`, cut in, then its instance at each list of arguments of
{lit}`args` of that child, cut in, and {lit}`k'` proving the goal with the instances' indices. -/
def withChildHyps (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (h : ℕ) (kids : List ℕ) (args : ℕ → List (List Term)) (k' : List ℕ → Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let (L₀, R₀) ← Internal.eqParts (← Φ[h]?)
  let tt : Term := Term.eq Term.star Term.star
  let nthOf (X : Term) (p : ℕ) : Term :=
    call D.headD [omega] [tt, p.rec X fun _ Y ↦ call D.tail [omega] [Y]]
  (kids.foldr (fun p (acc : List Term → List ℕ → Option Deriv) Φ₁ insts ↦ do
      let A := nthOf L₀ p
      let B := nthOf R₀ p
      let (A', dA, _) ← Internal.eval G E n rs 4096 .weak Γ Φ₁ A
      let (B', dB, _) ← Internal.eval G E n rs 4096 .weak Γ Φ₁ B
      let (_, dAh, _) ← Internal.eval G E n [.hyp h] 4096 .weak Γ Φ₁ A
      let (F, H) ← Internal.eqParts A'
      let i₁ := Φ₁.length
      let i₂ := i₁ + 1
      let αs := args p
      let Φ₂ := Φ₁ ++ [Term.eq A' B', A'] ++ αs.map fun α ↦ Term.eq (apps F α) (apps H α)
      let rest ← acc Φ₂ (insts ++ (List.range αs.length).map (i₂ + 1 + ·))
      let instDs := αs.map fun α ↦ RoseTree.node .join [rwFun i₂ α.length, RoseTree.node .refl []]
      let body := (αs.zip instDs).foldr (fun (α, d) r ↦
        RoseTree.node (.cut (Term.eq (apps F α) (apps H α))) [d, r]) rest
      pure (RoseTree.node (.cut (Term.eq A' B')) [RoseTree.node (.convFrom (Term.eq A B))
        [RoseTree.node .cong [dA, dB], RoseTree.node .join [dAh, RoseTree.node .refl []]],
        RoseTree.node (.cut A') [RoseTree.node .conv [RoseTree.node (.rwHyp i₁ false) [],
          RoseTree.node .join [RoseTree.node .refl [], RoseTree.node .refl []]], body]]))
    (fun Φ₁ insts ↦ k' insts Γ Φ₁ t u)) Φ []

/-- The proof of an equation by case analysis of the list variable of index {lit}`i`, the
hypothesis of index {lit}`h`, which mentions it, reverted: the implication of the equation by the
hypothesis, abstracted over the variable, equals the constant truth, by extensionality and list
induction on the new variable, the hypothesis introduced again in each case and each case's
equation proved by its prover under it, the last hypothesis; the equation follows from the
implication at the variable and the hypothesis. The connectives are the definitions from the
index {lit}`o`, their rules the theorems from {lit}`logicBase`. -/
def revertCase (G : Internal.Globals) (n o logicBase i h : ℕ) (pNil pCons : Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let a ← Internal.listPart c
  let ψ ← Φ[h]?
  let q := Term.eq t u
  let imp (p r : Term) : Term := Internal.Logic.imp o p r
  let tt := Internal.Logic.tt o
  let Fχ := Internal.abstractVar i c (imp ψ q)
  let sub (x : Term) : Term :=
    Term.subst (Internal.weaken1 x) fun j ↦ if j = i + 1 then v 0 else v j
  let ψ₁ := sub ψ
  let q₁ := sub q
  let Φ₁ := Φ.map Internal.weaken1 ++ [tt]
  let Φ' ← Internal.lowerHyps G n Γ Φ₁
  -- the empty list
  let z := Internal.instVar (Term.arr 0 [a] Term.star)
  let ψ₀ := Term.subst ψ₁ z
  let q₀ := Term.subst q₁ z
  let (t₀, u₀) ← Internal.eqParts q₀
  let d₀ ← pNil Γ (Φ' ++ [ψ₀]) t₀ u₀
  -- a construction
  let Φc := Φ'.map Internal.weaken2 ++ [Internal.weakenElem (imp ψ₁ q₁)]
  let ψc := Internal.listConsAt 1 a ψ₁
  let qc := Internal.listConsAt 1 a q₁
  let (tc, uc) ← Internal.eqParts qc
  let dc ← pCons (c :: a :: Γ) (Φc ++ [ψc]) tc uc
  let dχ₁ := RoseTree.node (.listIndHyp 0 1) [Internal.Logic.impI logicBase Φ'.length ψ₀ q₀ d₀,
    Internal.Logic.impI logicBase Φc.length ψc qc dc]
  let dFun := RoseTree.node .funExt [RoseTree.node .conv [RoseTree.node .cong
    [RoseTree.node .beta [], RoseTree.node .beta []],
    RoseTree.node .propExt [Internal.Logic.trueI, dχ₁]]]
  let dχ := RoseTree.node (.cut (Term.eq Fχ (Term.lam c tt))) [dFun,
    RoseTree.node (.convFrom (Term.app Fχ (v i))) [RoseTree.node .beta [],
      RoseTree.node .conv [RoseTree.node .trans [RoseTree.node .cong
        [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []],
        RoseTree.node .beta []], Internal.Logic.trueI]]]
  pure (RoseTree.node (.apply (logicBase + 4) [] [q, ψ]) [dχ, RoseTree.node (.hyp h) []])

/-- The proof of an equation whose sides reduce, at their heads, to an implication of an
equation and to truth, the connectives' definitions from the index {lit}`o`: the implication is
introduced, its conclusion's sides proved by {lit}`p` under the hypotheses, truth and the
antecedent. -/
def byImpI (G : Internal.Globals) (E : Array Entry) (o logicBase : ℕ) (p : Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let (t', dt, _) ← Internal.eval G E 0 [.rule .beta] 4096 .head Γ Φ t
  let (u', du, _) ← Internal.eval G E 0 [.rule .beta] 4096 .head Γ Φ u
  match t'.label, t'.children, u'.label with
  | .defn k _, [q, a], .defn k' _ =>
    if k = o + 2 ∧ k' = o then do
      let (l, r) ← Internal.eqParts q
      let d ← p Γ (Φ ++ [Internal.Logic.tt o, a]) l r
      pure (Internal.Logic.nd .conv [Internal.Logic.nd .cong [dt, du],
        Internal.Logic.nd .propExt [Internal.Logic.trueI,
          Internal.Logic.impI logicBase (Φ.length + 1) a q d]])
    else none
  | _, _, _ => none

/-- The proof of an equation with the conclusion of each hypothesis of the given indices, an
implication equal to truth whose antecedent is the hypothesis of index {lit}`h`, cut in by modus
ponens and used as a rewriting rule before those given to {lit}`k`; the connectives' definitions
from the index {lit}`o`. -/
def withImpElim (o logicBase h : ℕ) (is : List ℕ) (k : List NormRule → Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦
  (is.foldr (fun i (acc : List Term → List NormRule → Option Deriv) Φ₁ extra ↦ do
      let (l, _) ← Internal.eqParts (← Φ₁[i]?)
      match l.label, l.children with
      | .defn k' _, [q, a] =>
        if k' = o + 2 then do
          let rest ← acc (Φ₁ ++ [q]) (extra ++ [.hyp Φ₁.length])
          let dImp := Internal.Logic.nd .conv
            [Internal.Logic.nd (.rwHyp i false), Internal.Logic.trueI]
          pure (Internal.Logic.nd (.cut q) [Internal.Logic.nd (.apply (logicBase + 4) [] [q, a])
            [dImp, Internal.Logic.nd (.hyp h)], rest])
        else none
      | _, _ => none)
    (fun Φ₁ extra ↦ k extra Γ Φ₁ t u)) Φ []

/-- The index of a hypothesis rule's hypothesis. -/
def hypIndex : NormRule → Option ℕ
  | .hyp i => some i
  | _ => none

/-- The proof of an equation of two applications to a bit before a bitstring, the last two
variables, by the proof, by {lit}`p`, of the equation at the successor of the bitstring's
predecessor, into which the theorem of index {lit}`j` rewrites it backwards. -/
def bySuccPred (E : Array Entry) (j : ℕ) (p : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
  let some (Entry.language b) := E[j]? | none
  let (l, _) ← Internal.eqParts b.concl
  let σ := [v 1, v 0]
  let back : Deriv := RoseTree.node (.thm j [] σ true) []
  let rw (s : Term) : Option (Term × Deriv) := match s.label, s.children with
    | .app, [f, _] => some (Term.app f (Internal.instTerm [] σ l),
        RoseTree.node .cong [RoseTree.node .refl [], back])
    | _, _ => none
  let (t', dt) ← rw t
  let (u', du) ← rw u
  let q ← p Γ Φ t' u'
  pure (RoseTree.node .conv [RoseTree.node .cong [dt, du], q])

end Geb.FreeTopos.Tactics

end
