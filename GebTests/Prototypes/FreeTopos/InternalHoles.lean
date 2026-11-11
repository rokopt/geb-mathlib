/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes
public import GebTests.Prototypes.FreeTopos.InternalConversion -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalConversion -- shake: keep

set_option doc.verso true in
/-!
# Checking and filling proof holes

Open sketches report their sequents and cannot finish as certificates. Checking respects object
parameters, contexts, hypotheses and conclusions, including those introduced by proof rules.
Fillings may be closed or introduce further obligations; completed sketches are checked again
by the conversion checker.

## Main definitions

* {lit}`reflexive` — an equation in a context of a natural number.
* {lit}`byRefl` — a closed proof of a reflexive equation.

## Tags

internal language, proof hole, context, filling, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalHoles

open Geb Geb.FreeTopos Geb.FreeTopos.Internal
open ProofHoles
open GebTests.Prototypes.FreeTopos.Internal (G zeroT)

/-- A reflexive equation in a context of a natural number. -/
def reflexive : Thm := ⟨0, [nat], [], Term.eq (Term.var 0) (Term.var 0)⟩

/-- A closed proof of a reflexive equation by identity rewriting of both sides. -/
def byRefl : Sketch ℕ := node (.base .join) [node (.base .refl) [], node (.base .refl) []]

-- An open proof reports its hole but cannot finish; a closed proof produces a certificate.
#guard checks G #[] [] (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)
#guard (check G #[] [] (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).map
  (List.map Prod.fst) == some [0]
#guard (finish G #[] [] (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).isNone
#guard (finish G #[] [] (fun _ : ℕ ↦ reflexive) reflexive byRefl).any
  (reflexive.convChecks G #[] [])

-- Changing any part of the declared sequent rejects the occurrence.
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive) { reflexive with arity := 1 } (.pure 0)
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive) { reflexive with ctx := [one] } (.pure 0)
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive)
  { reflexive with hyps := [reflexive.concl] } (.pure 0)
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive)
  { reflexive with concl := Term.eq Term.star Term.star } (.pure 0)
#guard !checks G #[] [] (fun _ : ℕ ↦ { reflexive with concl := Term.var 8 })
  reflexive (.pure 0)
#guard !checks G #[] [] (fun _ : ℕ ↦ { reflexive with concl := Term.var 8 })
  { reflexive with concl := Term.var 8 } (.pure 0)
#guard (fill G #[] [] (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)
  (fun _ : ℕ ↦ reflexive) (fun _ ↦ .pure 7)).any fun d ↦ holes d == [7]

-- Holes are proofs, not rewritings, and malformed rule arities do not become proofs.
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base .join) [.pure 0, .pure 1])
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base .join) [node (.base .refl) []])
#guard (fill G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base .join) [.pure 0, .pure 1]) (fun _ : ℕ ↦ reflexive) (fun _ ↦ byRefl)).isNone

/-- The first premise of a cut and its continuation, which may use the cut formula. -/
def cutGoals (h : ℕ) : Thm :=
  if h = 0 then reflexive else { reflexive with hyps := [reflexive.concl] }

/-- A cut suspending both premises in their different hypothesis contexts. -/
def cutSketch : Sketch ℕ := node (.base (.cut reflexive.concl)) [.pure 0, .pure 1]

#guard checks G #[] [] cutGoals reflexive cutSketch
#guard (check G #[] [] cutGoals reflexive cutSketch).map (List.map Prod.fst) == some [0, 1]
-- Reusing an identity at these different sequents is rejected.
#guard !checks G #[] [] cutGoals reflexive
  (node (.base (.cut reflexive.concl)) [.pure 0, .pure 0])
#guard (fill G #[] [] cutGoals reflexive cutSketch cutGoals
  (fun _ ↦ node (.base (.hyp 0)) [])).isNone
#guard (fill G #[] [] cutGoals reflexive cutSketch cutGoals
  (fun h ↦ if h = 0 then byRefl else node (.base (.hyp 0)) [])).any fun d ↦
    (finish G #[] [] cutGoals reflexive d).any (reflexive.convChecks G #[] [])

-- A filling can introduce a new identity, which remains an obligation until the next filling.
#guard (fill G #[] [] cutGoals reflexive cutSketch cutGoals
  (fun h ↦ if h = 0 then byRefl else .pure 2)).any fun d ↦
    holes d == [2] && (finish G #[] [] cutGoals reflexive d).isNone &&
      (fill G #[] [] cutGoals reflexive d cutGoals
        (fun _ ↦ node (.base (.hyp 0)) [])).any fun d' ↦
          (finish G #[] [] cutGoals reflexive d').any (reflexive.convChecks G #[] [])

-- Repeated occurrences at the same sequent share their declaration and filling.
#guard (check G #[] [] (fun _ : ℕ ↦ cutGoals 1)
  { reflexive with concl := Term.eq reflexive.concl reflexive.concl }
  (node (.base .propExt) [.pure 0, .pure 0])).map (List.map Prod.fst) == some [0, 0]
#guard (fill G #[] [] (fun _ : ℕ ↦ cutGoals 1)
  { reflexive with concl := Term.eq reflexive.concl reflexive.concl }
  (node (.base .propExt) [.pure 0, .pure 0]) cutGoals
  (fun _ ↦ node (.base (.hyp 0)) [])).any fun d ↦ holes d |>.isEmpty

/-- Extensional equality of the identity function with itself. -/
def functionGoal : Thm :=
  ⟨0, [], [], Term.eq (Term.lam nat (Term.var 0)) (Term.lam nat (Term.var 0))⟩

/-- The extensionality premise is in the context extended by the function's argument. -/
def extensionalityGoal : Thm :=
  ⟨0, [nat], [], Term.eq (Term.app (Term.lam nat (Term.var 0)) (Term.var 0))
    (Term.app (Term.lam nat (Term.var 0)) (Term.var 0))⟩

#guard checks G #[] [] (fun _ : ℕ ↦ extensionalityGoal) functionGoal
  (node (.base .funExt) [.pure 0])
#guard !checks G #[] [] (fun _ : ℕ ↦ functionGoal) functionGoal
  (node (.base .funExt) [.pure 0])
#guard (fill G #[] [] (fun _ : ℕ ↦ extensionalityGoal) functionGoal
  (node (.base .funExt) [.pure 0]) (fun _ : ℕ ↦ extensionalityGoal) (fun _ ↦ byRefl)).any fun d ↦
    (finish G #[] [] (fun _ ↦ extensionalityGoal) functionGoal d).any
      (functionGoal.convChecks G #[] [])

/-- Natural-number induction's base and step, the latter with its induction hypothesis. -/
def inductionGoals (h : ℕ) : Thm :=
  if h = 0 then ⟨0, [], [], Term.eq zeroT zeroT⟩
  else { reflexive with hyps := [reflexive.concl], concl := natSuccAt 3 reflexive.concl }

#guard checks G #[] [] inductionGoals reflexive (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1])
#guard !checks G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1])
#guard (fill G #[] [] inductionGoals reflexive
  (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1]) inductionGoals (fun _ ↦ byRefl)).any fun d ↦
    (finish G #[] [] inductionGoals reflexive d).any (reflexive.convChecks G #[] [])

-- Entering a binder shifts the surrounding hypotheses as well as the variables in the goal.
#guard
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let a : Thm := ⟨0, [exp nat nat, exp nat nat], [φ], φ⟩
  let h : Thm := ⟨0, nat :: a.ctx, [weaken1 φ],
    Term.eq (Term.app (Term.var 1) (Term.var 0)) (Term.app (Term.var 2) (Term.var 0))⟩
  let d : Sketch ℕ := node (.base .funExt) [.pure 0]
  checks G #[] [] (fun _ ↦ h) a d &&
    !checks G #[] [] (fun _ ↦ { h with hyps := a.hyps }) a d &&
      (fill G #[] [] (fun _ ↦ h) a d (fun _ : ℕ ↦ h)
        (fun _ ↦ ofDeriv (InternalConversion.byMachine [.hyp 0]))).any fun d' ↦
          (finish G #[] [] (fun _ ↦ h) a d').any (a.convChecks G #[] [])

-- A conversion step ignores its premises; the sketch still reports and validates their holes.
#guard checks G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base .join) [node (.norm [] 8) [.pure 0], node (.base .refl) []])
#guard (finish G #[] [] (fun _ : ℕ ↦ reflexive) reflexive
  (node (.base .join) [node (.norm [] 8) [.pure 0], node (.base .refl) []])).isNone
#guard !checks G #[] [] (fun _ : ℕ ↦ { reflexive with concl := Term.var 8 }) reflexive
  (node (.base .join) [node (.norm [] 8) [.pure 0], node (.base .refl) []])

-- Existing conversion proofs embed, finish, and check in the original checker.
#guard (InternalConversion.steps 0).all fun step ↦
  (InternalDerivation.theorems[0]?).any fun (a, _) ↦
    (finish G #[] [] (fun _ : ℕ ↦ reflexive) a
      (ofDeriv (InternalConversion.byConv step))).any (a.convChecks G #[] [])
#guard (finish G InternalConversion.entries [] (fun _ : ℕ ↦ reflexive)
  InternalConversion.lamThm (ofDeriv (InternalConversion.byMachine [.hyp 0]))).any
    (InternalConversion.lamThm.convChecks G InternalConversion.entries [])
#guard (finish G InternalConversion.entries [] (fun _ : ℕ ↦ reflexive)
  InternalConversion.instanceThm (ofDeriv (RoseTree.node (.applyMatch 1 [Internal.A]) []))).any
    (InternalConversion.instanceThm.convChecks G InternalConversion.entries [])
#guard (finish G InternalConversion.entries [] (fun _ : ℕ ↦ reflexive)
  InternalConversion.instanceThm (ofDeriv (RoseTree.node (.applyMatch 0 [Internal.A]) []))).isNone

end GebTests.Prototypes.FreeTopos.InternalHoles

end
