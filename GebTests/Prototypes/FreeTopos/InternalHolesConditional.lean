/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes.Conditional
public meta import Geb.Prototypes.FreeTopos.Internal.Holes.Conditional -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalHoles -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalHoles -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalRoseTrees -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalRoseTrees -- shake: keep

set_option doc.verso true in
/-!
# Conversion certificates for conditional proofs

An open sketch yields a certificate of its obligations implying its conclusion. Obligations
close over their own variables and hypotheses, including those introduced by extensionality,
cut and induction. The result is checked by the conversion checker in the original environment.

## Main definitions

* {lit}`entries` — the checked logical introduction and elimination theorems.
* {lit}`certifies` — translation succeeds and the ordinary conversion checker accepts its result.

## Tags

internal language, proof hole, conditional certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalHolesConditional

open Geb Geb.FreeTopos Geb.FreeTopos.Internal
open ProofHoles
open InternalHoles
open InternalLogic (GL)

/-- The logical theorems, whose certificates are checked before use. -/
def entries : Array Entry := ((Logic.theorems 2 0).map fun (a, _) ↦ Entry.language a).toArray

#guard checkThms GL ((Logic.theorems 2 0).map fun (a, d) ↦ Decl.language a d) #[]

/-- Translation succeeds and its explicit conditional conclusion checks with no hypotheses. -/
def certifies (goals : ℕ → Thm) (a : Thm) (d : Sketch ℕ) (G : Globals := GL) : Bool :=
  (certify G entries [] 2 0 goals a d).any fun c ↦
    let b := conditional 2 goals a d
    b.hyps.isEmpty && b.convChecks G entries [] c

#guard certifies (fun _ ↦ reflexive) reflexive (.pure 0)
#guard certifies cutGoals reflexive cutSketch
#guard (fill GL entries [] cutGoals reflexive cutSketch cutGoals
  (fun h ↦ if h = 0 then byRefl else .pure 1)).any fun d ↦
    holes d == [1] && certifies cutGoals reflexive d
#guard certifies (fun _ ↦ extensionalityGoal) functionGoal (node (.base .funExt) [.pure 0])
#guard certifies inductionGoals reflexive (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1])

-- Differently typed variables are closed in context order; object parameters stay parameters.
#guard
  let a : Thm := ⟨1, [nat, omega, x 0], [Term.var 1], Term.eq (Term.var 0) (Term.var 0)⟩
  certifies (fun _ ↦ a) a (.pure 0)

-- The result's conclusion contains the hole's context and hypotheses, in their original order.
#guard
  let p := Term.var 0
  let q := Term.var 1
  let a : Thm := ⟨0, [omega, omega], [q, p], p⟩
  condition 2 a == Logic.all 2 omega (Term.lam omega
    (Logic.all 2 omega (Term.lam omega (Logic.imp 2 q (Logic.imp 2 p p))))) &&
    (conditional 2 (fun _ : ℕ ↦ a) a (.pure 0)).concl ==
      Logic.imp 2 (condition 2 a) (Logic.imp 2 q (Logic.imp 2 p p)) &&
    certifies (fun _ ↦ a) a (.pure 0)

-- A condition does not prove the unresolved goal without that condition.
#guard
  let a : Thm := ⟨0, [omega], [], Term.var 0⟩
  (certify GL entries [] 2 0 (fun _ : ℕ ↦ a) a (.pure 0)).any fun c ↦
    (conditional 2 (fun _ ↦ a) a (.pure 0)).convChecks GL entries [] c &&
      !a.convChecks GL entries [] c

-- Repeated identities remain repeated conditions and can cite their first occurrence.
#guard certifies (fun _ ↦ cutGoals 1)
  { reflexive with concl := Term.eq reflexive.concl reflexive.concl }
  (node (.base .propExt) [.pure 0, .pure 0])

-- A cut after a hole must move its local hypothesis reference past all conditions.
#guard certifies (fun _ ↦ reflexive) reflexive
  (node (.base (.cut reflexive.concl)) [.pure 0, node (.base (.hyp 0)) []])

-- Conditions are closed terms, so weakening under a binder does not capture their variables.
#guard
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let a : Thm := ⟨0, [exp nat nat, exp nat nat], [φ], φ⟩
  let h : Thm := ⟨0, nat :: a.ctx, [weaken1 φ],
    Term.eq (Term.app (Term.var 1) (Term.var 0)) (Term.app (Term.var 2) (Term.var 0))⟩
  certifies (fun _ ↦ h) a (node (.base .funExt) [.pure 0])

-- Wrong declarations and missing logical theorems fail without emitting a certificate.
#guard (certify GL entries [] 2 0 (fun _ : ℕ ↦ { reflexive with ctx := [] })
  reflexive (.pure 0)).isNone
#guard (certify GL #[] [] 2 0 (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).isNone
#guard (certify GL entries [] 20 0 (fun _ : ℕ ↦ reflexive) reflexive (.pure 0)).isNone

-- Rewriting rules embedded in conversion steps must also move their hypothesis indices.
#guard
  let a : Thm := ⟨0, [nat, nat], [Term.eq (Term.var 0) (Term.var 1)],
    Term.eq (Term.var 0) (Term.var 1)⟩
  let steps : List ConvRule := [.base (.rwHyp 0 false), .norm [.hyp 0] 8,
    .norm [.rule (.rwHyp 0 false)] 8, .eval [.hyp 0] 8 .full,
    .machine 8 0 [] 0 1 [.hyp 0]]
  steps.all fun s ↦ certifies (fun _ ↦ a) a
    (node (.base (.cut a.concl)) [.pure 0,
      node (.base .join) [node s [], node (.base .refl) []]])

-- Holes in ignored conversion premises are still conditions, but need no discharge there.
#guard certifies (fun _ ↦ reflexive) reflexive
  (node (.base .join) [node (.norm [] 8) [.pure 0], node (.base .refl) []])

-- The list-induction step closes over two variables and its induction hypothesis.
#guard
  let a : Thm := ⟨1, [list (x 0)], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let goals (h : ℕ) : Thm := if h = 0 then
      ⟨1, [], [], Term.subst a.concl (instVar (Term.arr 0 [x 0] Term.star))⟩
    else ⟨1, [list (x 0), x 0], [weakenElem a.concl], listConsAt 1 (x 0) a.concl⟩
  certifies goals a (node (.base (.listIndHyp 0 1)) [.pure 0, .pure 1])

-- Rose-tree induction with its induction hypothesis preserves the closed conditions.
#guard
  let a := InternalRoseTrees.eqUnderTree
  let h : Thm := ⟨1, [list (lrose (x 0)), x 0, x 0, x 0],
    [Term.eq (Term.var 2) (Term.var 3), roseHyp 0 1 a.concl],
    roseNodeAt 5 (lrose (x 0)) (x 0) a.concl⟩
  certifies (fun _ ↦ h) a (node (.base (.roseIndHyp 5 0 1)) [.pure 0]) InternalRoseTrees.GR

-- An existing closed rose-tree uniqueness proof keeps its premises' empty hypotheses.
#guard
  InternalRoseTrees.theorems[0]?.any fun (b, _) ↦
  InternalRoseTrees.theorems[1]?.any fun (a, d) ↦
  let E := entries.push (.language b)
  let d := RoseTree.map (fun r ↦ match r with
    | .thm 0 θ σ flip => Rule.thm entries.size θ σ flip
    | r => r) d
  let s : Sketch ℕ := node (.base (.cut a.concl)) [.pure 0,
    ofDeriv (RoseTree.map ConvRule.base d)]
  (certify InternalRoseTrees.GR E [] 2 0 (fun _ ↦ a) a s).any
    ((conditional 2 (fun _ ↦ a) a s).convChecks InternalRoseTrees.GR E [])

-- The partial translator cannot carry a condition into a uniqueness premise with no hypotheses.
#guard
  let a : Thm := ⟨0, [rose], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let s := Term.arr 4 [] (Term.pair (Term.var 1) (Term.var 0))
  let h : Thm := ⟨0, [list rose, nat], [],
    Term.eq (roseNodeAt 4 rose nat (Term.var 0))
      (Term.subst s (atVar0 (roseMapAt 0 1 rose (Term.var 0))))⟩
  let d : Sketch ℕ := node (.base (.roseInd 4 0 1 s)) [.pure 0, .pure 0]
  checks InternalRoseTrees.GR entries [] (fun _ ↦ h) a d &&
    (certify InternalRoseTrees.GR entries [] 2 0 (fun _ ↦ h) a d).isNone

-- Embedded sequent certificates are tied to the compiled original hypotheses. Rechecking
-- rejects their use after the prefix changes that sequent.
#guard
  let b : Thm := { reflexive with hyps := [reflexive.concl] }
  let E := entries.push (.language b)
  let s := b.seq GL
  let c := (⟨s.ctx, s.hyps⟩ : PartialHorn.Scope).cite entries.size
  let d : Sketch ℕ := node (.base (.cut reflexive.concl))
    [.pure 0, node (.base (.certSeq c)) []]
  b.convChecks GL entries [] (RoseTree.node (.base (.hyp 0)) []) &&
    checks GL E [] (fun _ ↦ reflexive) reflexive d &&
      (certify GL E [] 2 0 (fun _ ↦ reflexive) reflexive d).isNone

end GebTests.Prototypes.FreeTopos.InternalHolesConditional

end
