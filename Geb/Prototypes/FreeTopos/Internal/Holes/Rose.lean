/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes.Conditional

set_option doc.verso true in
/-!
# Conditional rose-tree uniqueness

A rose-tree induction hypothesis states that a list of propositions consists of truths.
List induction turns this into equality of the corresponding lists of values. The resulting
lemma permits uniqueness proofs to use closed assumptions about their two algebra equations.

## Main definitions

* {lit}`tails` — the fold retaining the rebuilt list and its tail.
* {lit}`rebuild` — the equation that the first component rebuilds the input list.

## Tags

internal language, proof hole, rose tree, list induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.ProofHoles.Rose

open PartialHorn (Tree)

open scoped FinEnum

/-- A base-rule node of a conversion certificate. -/
def nd (r : Rule) (cs : List ConvDeriv := []) : ConvDeriv := RoseTree.node (.base r) cs

/-- A normalization step using the supplied rules. -/
def norm (rs : List NormRule) : ConvDeriv := RoseTree.node (.norm rs 64) []

/-- An equation whose sides have the same normal form. -/
def join (rs : List NormRule) : ConvDeriv := nd .join [norm rs, norm rs]

/-- A fold retaining the rebuilt list and its tail. -/
def tails (kl kc : ℕ) (xs : Term) : Term :=
  let nil := Term.arr kl [omega] Term.star
  Term.listRec (Term.pair nil nil)
    (Term.pair (Term.arr kc [omega] (Term.pair (Term.var 1) (Term.fst (Term.var 0))))
      (Term.fst (Term.var 0))) xs

/-- The first component of the tail fold rebuilds its input. -/
def rebuild (n kl kc : ℕ) : Thm :=
  ⟨n, [list omega], [], Term.eq (Term.fst (tails kl kc (Term.var 0))) (Term.var 0)⟩

/-- The rebuilding equation by uniqueness of list folds. -/
def rebuildProof (kl kc : ℕ) : ConvDeriv :=
  nd (.listInd kl kc (Term.arr kc [omega] (Term.pair (Term.var 1) (Term.var 0))))
    [join [.rule (.listNil kl), .rule .fstPair],
      join [.rule (.listCons kc), .rule .fstPair], join []]

/-- Specialize a closed one-variable lemma at a term. -/
def specialize (o j : ℕ) (Φ : List Term) (a : Thm) (t : Term) : Option ConvDeriv := do
  let d ← hypothesis Φ (condition o a)
  pure (← specializeAt o j t (condition o a, d)).2

/-- The list-valued consequence of a rose-tree induction hypothesis. -/
def mapEquation (o n kl kc : ℕ) (r C : Tree) (t u : Term) : Thm :=
  ⟨n, [list r], [], Logic.imp o (roseHyp kl kc (Term.eq t u))
    (Term.eq (roseMapAt kl kc C t) (roseMapAt kl kc C u))⟩

/-- Eliminate an implication from supplied proofs of the implication and its antecedent. -/
def impElim (j : ℕ) (p q : Term) (c d : ConvDeriv) : ConvDeriv :=
  nd (.apply (j + 4) [] [q, p]) [c, d]

/-- Apply a destructor to the two sides of an equation cited as a hypothesis. Its argument is
rewritten before computing the destructor, so both sides become the same term. -/
def destructorEquation (i : ℕ) : ConvDeriv := nd .join [norm [.hyp i], nd .refl]

/-- List induction transfers equality of proposition lists to equality of value lists. The
rebuilding equation must be among the closed assumptions. -/
def mapProof (o j n kl kc : ℕ) (r C : Tree) (t u : Term) (Φ : List Term) :
    Option ConvDeriv := do
  let a := mapEquation o n kl kc r C t u
  let h := roseHyp kl kc (Term.eq t u)
  let q := Term.eq (roseMapAt kl kc C t) (roseMapAt kl kc C u)
  let k := Φ.length
  let hcons := listConsAt kc r h
  let qcons := listConsAt kc r q
  let htail := weakenElem h
  let qtail := weakenElem q
  let φ := Term.subst (Term.eq t u) (atVar0 (Term.var 1))
  let truth := Term.eq Term.star Term.star
  let (ml, mr) ← eqParts htail
  let lhs := Term.arr kc [omega] (Term.pair φ ml)
  let rhs := Term.arr kc [omega] (Term.pair truth mr)
  let hc := Term.eq lhs rhs
  let head (xs : Term) := Term.listRec truth (Term.var 1) xs
  let tail (xs : Term) := Term.snd (tails kl kc xs)
  let hhead := Term.eq (head lhs) (head rhs)
  let htail' := Term.eq (tail lhs) (tail rhs)
  let rl := Term.eq (Term.fst (tails kl kc ml)) ml
  let rr := Term.eq (Term.fst (tails kl kc mr)) mr
  let stepΦ := Φ ++ [weakenElem a.concl, hcons, hc]
  let dl ← specialize o j stepΦ (rebuild n kl kc) ml
  let dr ← specialize o j (stepΦ ++ [rl]) (rebuild n kl kc) mr
  let cons := nd (.listCons kc)
  let headProof := nd (.convFrom hhead)
    [nd .cong [cons, cons], destructorEquation (k + 2)]
  let tailStep (i : ℕ) := nd .trans [nd .cong [cons],
    nd .trans [nd .sndPair, nd (.rwHyp i false)]]
  let tailProof := nd (.convFrom htail')
    [nd .cong [tailStep (k + 3), tailStep (k + 4)], destructorEquation (k + 2)]
  let valueHead := nd .conv [nd (.rwHyp (k + 5) false), join []]
  let valueTail := impElim j htail qtail (nd (.hyp k)) (nd (.hyp (k + 6)))
  let cuts := [(hc, nd (.convFrom hcons)
      [nd .cong [cons, cons], nd (.hyp (k + 1))]),
    (rl, dl), (rr, dr), (Term.eq φ truth, headProof), (htail, tailProof),
    (φ, valueHead), (qtail, valueTail)]
  let step := impIntro j (k + 1) hcons qcons
    (cuts.foldr (fun (p, c) d ↦ nd (.cut p) [c, d])
      (nd .join [nd .trans [cons, nd .cong [nd .cong
        [nd (.rwHyp (k + 7) false), nd (.rwHyp (k + 8) false)]]], cons]))
  let nil := Term.arr kl [r] Term.star
  let base := impIntro j k (Term.subst h (instVar nil)) (Term.subst q (instVar nil))
    (nd .join [nd (.listNil kl), nd (.listNil kl)])
  pure (nd (.listIndHyp kl kc) [base, step])

end Geb.FreeTopos.Internal.ProofHoles.Rose

end
