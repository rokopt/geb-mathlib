/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep

set_option doc.verso true in
/-!
# Declared constants in the internal language

A development that declares constants beside its theorems. The prover's library of the
combinators opens it, and the prover proves that the successor after itself is an arrow from the
natural numbers to themselves; the development then declares two primitive arrows, the constant
one, confirmed by the checker's inference, and adding two, confirmed by the prover's certificate;
a definition applying adding two; and a theorem that applies the definition and both primitive
arrows, proved by unfolding the definition. The development checks; a theorem stated before the
constants it applies does not, nor a primitive arrow whose certificate proves the sequent of
another.

## Main definitions

* {lit}`onePrim`, {lit}`twoPrim`, {lit}`addTwoD` — the declared constants.
* {lit}`development` — the development, its declarations of every kind in order.

## Tags

internal language, combinators, primitive arrow, definition, certificate, development
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalConstants

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Entry Decl Globals checkThms compileDefs)

/-- The definitions of the combinators that appending and addition compile to. -/
def cds : List PartialHorn.Defn := (compileDefs G).getD []

/-- The constant one: the successor after zero. -/
def onePrim : Internal.Prim := ⟨0, comp succ zeroN, one, nat⟩

/-- Adding two: the successor after itself. -/
def twoPrim : Internal.Prim := ⟨0, comp succ succ, nat, nat⟩

/-- Adding two to a natural number, a definition applying the primitive arrow adding two. -/
def addTwoD : Internal.Defn := ⟨0, [nat], nat, Term.arr 5 [] (Term.var 0)⟩

/-- The constants with the declared ones. -/
def G₃ : Globals :=
  ⟨prims ++ [onePrim, twoPrim], (defs ++ [addTwoD]).map .language, sig.length⟩

/-- Adding two to one by the definition is adding two to one by the primitive arrow. -/
def addTwoOne : Thm :=
  ⟨0, [], [], Term.eq (Term.defn 2 [] [Term.arr 4 [] Term.star])
    (Term.arr 5 [] (Term.arr 4 [] Term.star))⟩

/-- The development: the prover's library and its proof that adding two is an arrow from the
natural numbers to themselves, the two primitive arrows, the definition, and the theorem. The
result's last component is the certificate that confirms adding two. -/
def developmentWith : Option (List Decl × Tree) := do
  let (i, lib) ← libraryWith false
  let (k, dev) ← (proveSeq twoPrim.seq (Prover.byNorm (rules i) twoPrim.seq.concl) cds).run lib
  let c := Scope.cite ⟨[], []⟩ k
  let E : Array Entry := (dev.map fun (s, _) ↦ Entry.combinators s).toArray
  let d ← Internal.byNorm G₃ E 0 [.delta 2] 16 [] [] (Term.defn 2 [] [Term.arr 4 [] Term.star])
    (Term.arr 5 [] (Term.arr 4 [] Term.star))
  pure (dev.map (fun (s, c) ↦ Decl.combinators s c) ++
    [Decl.constant onePrim none, Decl.constant twoPrim (some c), Decl.definition addTwoD,
      Decl.language addTwoOne d], c)

/-- The development. -/
def development : Option (List Decl) := developmentWith.map Prod.fst

-- the development checks, its declarations of every kind
#guard development.any fun ds ↦ checkThms G ds #[]

-- the theorem does not check before the constants it applies
#guard development.any fun ds ↦ !checkThms G (ds.take (ds.length - 4) ++
  ds.drop (ds.length - 1) ++ (ds.drop (ds.length - 4)).take 3) #[]

-- the certificate does not confirm a primitive arrow of another codomain
#guard developmentWith.any fun (ds, c) ↦ !checkThms G (ds.take (ds.length - 4) ++
  [Decl.constant ⟨0, comp succ succ, nat, one⟩ (some c)]) #[]

end GebTests.Prototypes.FreeTopos.InternalConstants

end
