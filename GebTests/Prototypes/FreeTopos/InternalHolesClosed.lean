/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes.Closed
public meta import Geb.Prototypes.FreeTopos.Internal.Holes.Closed -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalHolesConditional -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalHolesConditional -- shake: keep

set_option doc.verso true in
/-!
# Closed certificates of proof sketches

The translation closes every local sequent before using it as a lemma. The resulting
conditional certificate is checked in the original environment with no term variables and no
hypotheses.

## Main definitions

* {lit}`certifies` — translate and replay the fully closed conditional certificate.

## Tags

internal language, proof hole, conditional certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalHolesClosed

open Geb Geb.FreeTopos Geb.FreeTopos.Internal
open ProofHoles InternalHoles
open InternalLogic (GL)
open InternalHolesConditional (entries)

/-- Translate and replay the fully closed conditional certificate. -/
def certifies (goals : ℕ → Thm) (a : Thm) (d : Sketch ℕ) (G : Globals := GL) : Bool :=
  (Closed.certify G entries [] 2 0 goals a d).any fun c ↦
    let b := Closed.conditional 2 goals a d
    b.ctx.isEmpty && b.hyps.isEmpty && b.convChecks G entries [] c

#guard certifies (fun _ ↦ reflexive) reflexive (.pure 0)
#guard certifies cutGoals reflexive cutSketch
#guard certifies (fun _ ↦ extensionalityGoal) functionGoal (node (.base .funExt) [.pure 0])
#guard certifies inductionGoals reflexive (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1])
#guard certifies (fun _ ↦ reflexive) reflexive byRefl

-- Closed claims survive the two bound variables and induction hypothesis of a list step.
#guard
  let a : Thm := ⟨1, [list (x 0)], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let goals (h : ℕ) : Thm := if h = 0 then
      ⟨1, [], [], Term.subst a.concl (instVar (Term.arr 0 [x 0] Term.star))⟩
    else ⟨1, [list (x 0), x 0], [weakenElem a.concl], listConsAt 1 (x 0) a.concl⟩
  certifies goals a (node (.base (.listIndHyp 0 1)) [.pure 0, .pure 1])

#guard
  let a := InternalRoseTrees.eqUnderTree
  let h : Thm := ⟨1, [list (lrose (x 0)), x 0, x 0, x 0],
    [Term.eq (Term.var 2) (Term.var 3), roseHyp 0 1 a.concl],
    roseNodeAt 5 (lrose (x 0)) (x 0) a.concl⟩
  certifies (fun _ ↦ h) a (node (.base (.roseIndHyp 5 0 1)) [.pure 0]) InternalRoseTrees.GR

-- Conversion rules cite the same local hypothesis after closed lemmas are introduced.
#guard
  let a : Thm := ⟨0, [nat, nat], [Term.eq (Term.var 0) (Term.var 1)],
    Term.eq (Term.var 0) (Term.var 1)⟩
  let steps : List ConvRule := [.base (.rwHyp 0 false), .norm [.hyp 0] 8,
    .norm [.rule (.rwHyp 0 false)] 8, .eval [.hyp 0] 8 .full,
    .machine 8 0 [] 0 1 [.hyp 0]]
  steps.all fun s ↦ certifies (fun _ ↦ a) a
    (node (.base (.cut a.concl)) [.pure 0,
      node (.base .join) [node s [], node (.base .refl) []]])

-- Declarations, logic offsets and unfinished conclusions are still checked.
#guard (Closed.certify GL entries [] 2 0 (fun _ : ℕ ↦ { reflexive with ctx := [] })
  reflexive (.pure 0)).isNone
#guard (Closed.certify GL #[] [] 2 0 (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).isNone
#guard (Closed.certify GL entries [] 20 0 (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).isNone
#guard
  let a : Thm := ⟨0, [omega], [], Term.var 0⟩
  (Closed.certify GL entries [] 2 0 (fun _ : ℕ ↦ a) a (.pure 0)).any fun c ↦
    (Closed.conditional 2 (fun _ ↦ a) a (.pure 0)).convChecks GL entries [] c &&
      !a.convChecks GL entries [] c

-- The derived list lemmas replay under the same closed assumptions used by the translator.
#guard
  let a := Rose.rebuild 0 0 1
  a.convChecks InternalRoseTrees.GR entries [] (Rose.rebuildProof 0 1)

#guard
  let a := Rose.rebuild 0 0 1
  let C := [condition 2 a]
  let m := Rose.mapEquation 2 0 0 1 rose rose (Term.var 0) (Term.var 0)
  (Rose.mapProof 2 0 0 0 1 rose rose (Term.var 0) (Term.var 0)
    (Closed.bodyAssumptions 2 C m)).any fun c ↦
      (⟨0, [], C, condition 2 m⟩ : Thm).convChecks InternalRoseTrees.GR entries []
        (Closed.close 2 0 C m c)

#guard
  let a : Thm := ⟨0, [rose], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let s := Term.arr 4 [] (Term.pair (Term.var 1) (Term.var 0))
  let h : Thm := ⟨0, [list rose, nat], [],
    Term.eq (roseNodeAt 4 rose nat (Term.var 0))
      (Term.subst s (atVar0 (roseMapAt 0 1 rose (Term.var 0))))⟩
  let d : Sketch ℕ := node (.base (.roseInd 4 0 1 s)) [.pure 0, .pure 0]
  checks InternalRoseTrees.GR entries [] (fun _ ↦ h) a d &&
    certifies (fun _ ↦ h) a d InternalRoseTrees.GR

#guard
  let rb := Rose.rebuild 1 0 1
  let C := [condition 2 rb]
  let t := InternalRoseTrees.rebuildRose
  let m := Rose.mapEquation 2 1 0 1 (lrose (x 0)) (lrose (x 0)) t (Term.var 0)
  (Rose.mapProof 2 0 1 0 1 (lrose (x 0)) (lrose (x 0)) t (Term.var 0)
    (Closed.bodyAssumptions 2 C m)).any fun c ↦
      (⟨1, [], C, condition 2 m⟩ : Thm).convChecks InternalRoseTrees.GR entries []
        (Closed.close 2 0 C m c)

-- Both orientations of uniqueness, with a parameterized label and both premises open.
#guard
  InternalRoseTrees.theorems[1]?.any fun (a, _) ↦
    (eqParts a.concl).any fun (t, u) ↦ [a, { a with concl := Term.eq u t }].all fun a ↦
      let s := Term.arr 5 [x 0] (Term.pair (Term.var 1) (Term.var 0))
      let r := ConvRule.base (.roseInd 5 0 1 s)
      ((Closed.premises InternalRoseTrees.GR entries [] a r
        [Rose.nd .refl, Rose.nd .refl]).bind fun (_, ps) ↦ do
          let [.proof b, .proof c] := ps | none
          let goals (h : ℕ) := if h = 0 then b else c
          let d : Sketch ℕ := node r [.pure 0, .pure 1]
          pure (certifies goals a d InternalRoseTrees.GR &&
            certifies goals { a with hyps := [a.concl] } d InternalRoseTrees.GR)).getD false

-- A compiled certificate is transported after the surrounding cut adds the hole condition.
#guard
  let b : Thm := { reflexive with hyps := [reflexive.concl] }
  let E := entries.push (.language b)
  let s := b.seq GL
  let c := (⟨s.ctx, s.hyps⟩ : PartialHorn.Scope).cite entries.size
  let d : Sketch ℕ := node (.base (.cut reflexive.concl))
    [.pure 0, node (.base (.certSeq c)) []]
  b.convChecks GL entries [] (Rose.nd (.hyp 0)) &&
    (Closed.certify GL E [] 2 0 (fun _ ↦ reflexive) reflexive d).any
      ((Closed.conditional 2 (fun _ ↦ reflexive) reflexive d).convChecks GL E [])

end GebTests.Prototypes.FreeTopos.InternalHolesClosed

end
