/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep

set_option doc.verso true in
/-!
# Rose trees in the internal language

The constructions of the rose-tree object and of the rose-tree object over a type of labels,
placed after the primitive arrows of the natural numbers and lists and confirmed by the checker's
inference, and the computation of the fold of each at a construction checked: the fold that
takes a tree to its root's label computes the label. The fold that rebuilds a tree is the
identity, by induction on rose trees, with the fold that rebuilds a list, the identity by
induction on lists, cited at the children. Induction on rose trees with an induction hypothesis
proves a formula from its instance at a construction, and a derivation whose premise does not
prove that instance is rejected.

## Main definitions

* {lit}`GR` — the constants, the constructions of rose trees among them.
* {lit}`theorems` — the computations and the inductions, each with its proof.

## Tags

internal language, rose tree, fold, derivation
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalRoseTrees

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv checkThms compileDefs nodePrim lnodePrim)
open Geb.FreeTopos.Internal.Logic (nd)

/-- The constants: the primitive arrows of the natural numbers and lists, the constructions of
rose trees, and the definitions of appending, addition and the connectives. -/
def GR : Internal.Globals :=
  ⟨prims ++ [nodePrim, lnodePrim], (defs ++ Internal.Logic.defs 2).map .language, sig.length⟩

-- the constants are well formed, the primitive arrows of the types they name
#guard (compileDefs GR).any fun cs ↦ GR.ok (ExtEnv.ofDefs cs)

/-- The fold of a list of the object parameter that rebuilds it. -/
def rebuildList : Term :=
  Term.listRec (Term.arr 0 [x 0] Term.star)
    (Term.arr 1 [x 0] (Term.pair (Term.var 1) (Term.var 0))) (Term.var 0)

/-- The fold of a rose tree over the object parameter that rebuilds it. -/
def rebuildRose : Term :=
  Term.roseRec (lrose (x 0)) (Term.arr 5 [x 0] (Term.var 0)) (Term.var 0)

/-- The theorems, each with its proof: the fold taking a rose tree over a type of labels, and a
rose tree, to its root's label computes the label at a construction; the folds that rebuild a
list and a rose tree are the identities. -/
def theorems : List (Thm × Deriv) := [
  (⟨1, [list (x 0)], [], Term.eq rebuildList (Term.var 0)⟩,
    nd (.listInd 0 1 (Term.arr 1 [x 0] (Term.pair (Term.var 1) (Term.var 0)))) [
      nd .join [nd (.listNil 0), nd .refl],
      nd .join [nd (.listCons 1), nd .refl],
      nd .join [nd .refl, nd .refl]]),
  (⟨1, [lrose (x 0)], [], Term.eq rebuildRose (Term.var 0)⟩,
    nd (.roseInd 5 0 1 (Term.arr 5 [x 0] (Term.pair (Term.var 1) (Term.var 0)))) [
      nd .join [nd (.roseNode 5 0 1), nd .refl],
      nd .join [nd .refl, nd .cong [nd .cong [nd .refl,
        nd (.thm 0 [lrose (x 0)] [Term.var 0] false)]]]]),
  (⟨1, [list (lrose (x 0)), x 0], [],
    Term.eq (Term.roseRec (x 0) (Term.fst (Term.var 0))
      (Term.arr 5 [x 0] (Term.pair (Term.var 1) (Term.var 0)))) (Term.var 1)⟩,
    nd .join [nd .trans [nd (.roseNode 5 0 1), nd .fstPair], nd .refl]),
  (⟨0, [list rose, nat], [],
    Term.eq (Term.roseRec nat (Term.fst (Term.var 0))
      (Term.arr 4 [] (Term.pair (Term.var 1) (Term.var 0)))) (Term.var 1)⟩,
    nd .join [nd .trans [nd (.roseNode 4 0 1), nd .fstPair], nd .refl])]

-- the development checks
#guard checkThms GR (theorems.map fun (a, d) ↦ .language a d) #[]

/-- The fold of a rose tree over the object parameter that takes it to its root's label. -/
def labelRose : Term :=
  Term.roseRec (x 0) (Term.fst (Term.var 0)) (Term.var 0)

/-- A tree's root's label is its rebuilding's, by induction on rose trees with the induction
hypothesis: at a construction both sides compute the label. -/
def labelRebuild : Thm :=
  ⟨1, [lrose (x 0)], [], Term.eq (Term.app (Term.lam (lrose (x 0)) labelRose) rebuildRose)
    labelRose⟩

-- the induction with the hypothesis checks, and fails where its premise is not proved
#guard checkThms GR [.language labelRebuild (nd (.roseIndHyp 5 0 1) [
  nd .join [nd .trans [nd .cong [nd .refl, nd (.roseNode 5 0 1)], nd .trans [nd .beta,
    nd .trans [nd (.roseNode 5 0 1), nd .fstPair]]], nd .trans [nd (.roseNode 5 0 1),
      nd .fstPair]]])] #[]
#guard !checkThms GR [.language labelRebuild (nd (.roseIndHyp 5 0 1) [nd (.hyp 0)])] #[]

end GebTests.Prototypes.FreeTopos.InternalRoseTrees

end
