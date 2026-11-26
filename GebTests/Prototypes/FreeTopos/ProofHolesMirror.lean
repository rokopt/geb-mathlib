/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic.ProofHoles
public meta import GebMirror.Metalogic.ProofHoles -- shake: keep
public import GebTests.Prototypes.FreeTopos.Agreement.ProofHoles
public meta import GebTests.Prototypes.FreeTopos.Agreement.ProofHoles -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalHolesConditional
public meta import GebTests.Prototypes.FreeTopos.InternalHolesConditional -- shake: keep

set_option doc.verso true in
/-!
# Proof sketches checked in Geb

The emitted checker takes a tree for each hole identity and a function assigning each
identity its sequent. These comparisons use natural-number identities and the same
sketches, environments and logic offsets in both implementations. The closed conditional
certificates returned by Geb are replayed at the theorem constructed by the Lean reference.

## Main definitions

* {lit}`encSketch` — encode a hole or a conversion rule with its premises.
* {lit}`reportAgrees` — compare every occurrence and its full sequent.
* {lit}`certifies` — compare the conditional theorem and replay the Geb certificate.

## Tags

proof sketch, conversion, certificate, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.ProofHolesMirror

open Geb Geb.Kernel Geb.FreeTopos Geb.FreeTopos.Internal GebMirror.Metalogic
open Agreement.Encode Agreement.Provers ProofHoles InternalHoles
open InternalLogic (GL)
open InternalHolesConditional (entries)
open scoped FinEnum

/-- Encode a test sketch using natural-number leaves as hole identities. -/
abbrev encSketch := Agreement.ProofHoles.encSketch (α := ℕ) leaf

/-- Read an encoded natural-number identity and encode its declared sequent. -/
def declarations (g : ℕ → Thm) (h : Tree) : Tree := encThm (g h.label)

/-- Compare reports, including rejection, repeated occurrences and local sequents. -/
def reportAgrees (g : ℕ → Thm) (a : Thm) (d : Sketch ℕ) : Bool :=
  «ProofHoles.checkSketch» (encGlobals GL) (entries.toList.map encEntry) [] (declarations g)
    (encThm a) (encSketch d) == encOpt ((check GL entries [] g a d).map fun hs ↦
      RoseTree.node 0 (hs.map fun (h, b) ↦ encPair (leaf h, encThm b)))

#guard reportAgrees cutGoals reflexive cutSketch
#guard reportAgrees cutGoals reflexive (node (.base (.cut reflexive.concl)) [.pure 0, .pure 0])
#guard reportAgrees cutGoals reflexive (node (.base .join) [.pure 0, .pure 1])
#guard reportAgrees (fun _ ↦ cutGoals 1)
  { reflexive with concl := Term.eq reflexive.concl reflexive.concl }
  (node (.base .propExt) [.pure 0, .pure 0])
#guard reportAgrees (fun _ ↦ { reflexive with concl := Term.var 8 }) reflexive
  (node (.base .join) [node (.norm [] 4) [.pure 1], node (.base .refl) []])
#guard [RoseTree.node 42 [], RoseTree.node 42 [leaf 0, leaf 1], RoseTree.node 43 [leaf 0]].all
  fun t ↦ «ProofHoles.checkSketch» (encGlobals GL) [] [] (declarations cutGoals)
    (encThm reflexive) t == encOpt none

/-- Compare checked substitution, allowing a filling to introduce a new obligation. -/
def fillAgrees (f : ℕ → Sketch ℕ) : Bool :=
  «ProofHoles.fill» (encGlobals GL) (entries.toList.map encEntry) [] (declarations cutGoals)
    (encThm reflexive) (encSketch cutSketch) (declarations cutGoals) (fun h ↦ encSketch (f h.label))
    == encOpt ((fill GL entries [] cutGoals reflexive cutSketch cutGoals f).map encSketch)

#guard fillAgrees (fun h ↦ if h = 0 then byRefl else .pure 2)
#guard fillAgrees (fun _ ↦ node (.base (.hyp 0)) [])
#guard fillAgrees (fun h ↦ if h = 0 then byRefl else node (.base (.hyp 0)) [])
#guard [byRefl, cutSketch].all fun d ↦
  «ProofHoles.finish» (encGlobals GL) (entries.toList.map encEntry) [] (declarations cutGoals)
    (encThm reflexive) (encSketch d) ==
      encOpt ((finish GL entries [] cutGoals reflexive d).map encConv)

/-- Compare the conditional theorem with the Lean target and replay a successful certificate. -/
def certifies (g : ℕ → Thm) (a : Thm) (d : Sketch ℕ) (G : Globals := GL)
    (E : Array Entry := entries) : Bool :=
  let b := encThm (Closed.conditional 2 g a d)
  let target := «HoleConditions.conditional» (leaf 2) (declarations g) (encThm a) (encSketch d)
  let c := «HoleCertificates.certify» (encGlobals G) (E.toList.map encEntry) [] (leaf 2) (leaf 0)
    (declarations g) (encThm a) (encSketch d)
  let replay := «Conversion.thmConvChecks» (encGlobals G) (E.toList.map encEntry) [] b
  target == b && c.label != 0 && (replay («Prelude.get» c)).label != 0

-- A suspended arbitrary proposition yields a certificate of its conditional theorem.
#guard
  let a : Thm := ⟨0, [omega], [], Term.var 0⟩
  let d := encSketch (.pure 0)
  let g := declarations (fun _ ↦ a)
  let G := encGlobals GL
  let E := entries.toList.map encEntry
  let c := «HoleCertificates.certify» G E [] (leaf 2) (leaf 0) g (encThm a) d
  let replay := fun b ↦ («Conversion.thmConvChecks» G E [] b («Prelude.get» c)).label
  c.label != 0 && replay («HoleConditions.conditional» (leaf 2) g (encThm a) d) != 0 &&
    replay (encThm a) == 0 && «ProofHoles.finish» G E [] g (encThm a) d == encOpt none

#guard certifies cutGoals reflexive cutSketch
#guard certifies (fun _ ↦ extensionalityGoal) functionGoal (node (.base .funExt) [.pure 0])
#guard certifies inductionGoals reflexive (node (.base (.natIndHyp 2 3)) [.pure 0, .pure 1])
#guard certifies cutGoals reflexive byRefl
#guard
  let g := declarations cutGoals
  «HoleConditions.directCertify» (encGlobals GL) (entries.toList.map encEntry) [] (leaf 2) (leaf 0)
    g (encThm reflexive) (encSketch cutSketch) ==
    encOpt ((ProofHoles.certify GL entries [] 2 0 cutGoals reflexive cutSketch).map encConv)
#guard
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let a : Thm := ⟨0, [nat, nat], [φ], φ⟩
  let steps : List ConvRule := [.base (.rwHyp 0 false), .norm [.hyp 0] 8,
    .eval [.hyp 0] 8 .full, .machine 8 0 [] 0 1 [.hyp 0]]
  steps.all fun s ↦ certifies (fun _ ↦ a) a (node (.base (.cut a.concl))
    [.pure 0, node (.base .join) [node s [], node (.base .refl) []]])
#guard
  let a : Thm := ⟨0, [rose], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let s := Term.arr 4 [] (Term.pair (Term.var 1) (Term.var 0))
  let h : Thm := ⟨0, [list rose, nat], [],
    Term.eq (roseNodeAt 4 rose nat (Term.var 0))
      (Term.subst s (atVar0 (roseMapAt 0 1 rose (Term.var 0))))⟩
  certifies (fun _ ↦ h) a (node (.base (.roseInd 4 0 1 s)) [.pure 0, .pure 0]) InternalRoseTrees.GR
#guard
  let b := { reflexive with hyps := [reflexive.concl] }
  let s := b.seq GL
  let c := (⟨s.ctx, s.hyps⟩ : PartialHorn.Scope).cite entries.size
  certifies (fun _ ↦ reflexive) reflexive
    (node (.base (.cut reflexive.concl)) [.pure 0, node (.base (.certSeq c)) []])
    GL (entries.push (.language b))

-- A parameterized rose algebra in either orientation, including ambient hypotheses.
#guard
  InternalRoseTrees.theorems[1]?.any fun (a, _) ↦
    (eqParts a.concl).any fun (t, u) ↦ [a, { a with concl := Term.eq u t }].all fun a ↦
      let s := Term.arr 5 [x 0] (Term.pair (Term.var 1) (Term.var 0))
      let r := ConvRule.base (.roseInd 5 0 1 s)
      ((Closed.premises InternalRoseTrees.GR entries [] a r [Rose.nd .refl, Rose.nd .refl]).bind
        fun (_, ps) ↦ do
          let [.proof b, .proof c] := ps | none
          let g (h : ℕ) := if h = 0 then b else c
          let d : Sketch ℕ := node r [.pure 0, .pure 1]
          pure (certifies g a d InternalRoseTrees.GR &&
            certifies g { a with hyps := [a.concl] } d InternalRoseTrees.GR)).getD false

-- Object arguments in a cited theorem and the local hypothesis of a nested cut survive transport.
#guard
  let G : Globals := ⟨[], [], sig.length⟩
  let a : Thm := ⟨1, [x 0], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let s := a.seq G
  let citation := (⟨s.ctx, s.hyps⟩ : PartialHorn.Scope).cite 0
  let c := PartialHorn.Cert.cut citation (PartialHorn.Cert.hyp 0)
  let E := #[Entry.language a]
  let hs := [a.concl]
  let w := «HoleSequent.weakenSequent» (encGlobals G) (E.toList.map encEntry) (encThm a)
    (hs.map encTerm) c
  w.label != 0 && Internal.certifies G E («Prelude.get» w) ({ a with hyps := hs }.seq G)

#guard
  let G : Globals := ⟨[], [], sig.length⟩
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let a : Thm := ⟨0, [nat, nat], [φ], φ⟩
  «HoleSequent.weakenSequent» (encGlobals G) [encEntry (.language a)] (encThm a) []
    (PartialHorn.Cert.thm 0 [] [] []) == encOpt none

#guard «HoleCertificates.certify» (encGlobals GL) [] [] (leaf 2) (leaf 0)
  (declarations cutGoals) (encThm reflexive) (encSketch cutSketch) == encOpt none

end GebTests.Prototypes.FreeTopos.ProofHolesMirror

end
