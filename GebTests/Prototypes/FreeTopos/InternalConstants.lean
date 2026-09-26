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
natural numbers to themselves, that the product of the natural numbers with themselves is defined,
and the sequent that a pair's round trip through a type of pairs compiles to. The development then
declares two primitive arrows, the constant one, confirmed by the checker's inference, and adding
two, confirmed by the prover's certificate; a definition applying adding two; a theorem that
applies the definition and both primitive arrows, proved by unfolding the definition; two object
definitions, the pairs of the object parameter, confirmed by the inference, and the product of the
natural numbers with themselves, confirmed by the prover's certificate; arrows into and out of the
pairs, whose types name the object definition, confirmed by the inference; and theorems in
contexts of those types. The development checks; a theorem stated before the constants it applies
or the types it names does not, nor a constant whose certificate proves the sequent of another.

## Main definitions

* {lit}`onePrim`, {lit}`twoPrim`, {lit}`addTwoD` — the declared primitive arrows and definition.
* {lit}`pairsObj`, {lit}`toPairs`, {lit}`fromPairs` — the pairs, and the arrows into and out of
  them.
* {lit}`development` — the development, its declarations of every kind in order.

## Tags

internal language, combinators, primitive arrow, definition, object, certificate, development
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalConstants

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Entry Decl Globals checkThms compileDefs)
open Geb.FreeTopos.Internal.Logic (nd)

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

/-- The pairs of the object parameter: its product with itself. -/
def pairsObj : Tree := prod (x 0) (x 0)

/-- The type of the pairs of a type: the operation of the object definition of the pairs. -/
def pairsTy (a : Tree) : Tree := op (sig.length + 3) [a]

/-- Into the pairs of the object parameter: the identity of its product with itself. -/
def toPairs : Internal.Prim := ⟨1, idt pairsObj, pairsObj, pairsTy (x 0)⟩

/-- Out of the pairs of the object parameter: the identity of its product with itself. -/
def fromPairs : Internal.Prim := ⟨1, idt pairsObj, pairsTy (x 0), pairsObj⟩

/-- The constants with the object definitions and the arrows into and out of the pairs. -/
def G₅ : Globals :=
  ⟨prims ++ [onePrim, twoPrim, toPairs, fromPairs],
    (defs ++ [addTwoD]).map .language ++ [.object 1 pairsObj, .object 0 (prod nat nat)],
    sig.length⟩

/-- A pair of natural numbers, into and out of their pairs, is itself. -/
def roundTrip : Thm :=
  ⟨0, [prod nat nat], [], Term.eq (Term.arr 7 [nat] (Term.arr 6 [nat] (Term.var 0))) (Term.var 0)⟩

/-- An element of the pairs of the natural numbers is itself. -/
def pairsRefl : Thm := ⟨0, [pairsTy nat], [], Term.eq (Term.var 0) (Term.var 0)⟩

/-- The development: the prover's library, and its proofs that adding two is an arrow from the
natural numbers to themselves, that the product of the natural numbers with themselves is
defined, and of the sequent a pair's round trip through the pairs compiles to; the two primitive
arrows, the definition, and the theorem applying them; the object definitions of the pairs of
the object parameter, confirmed by the inference, and of the product of the natural numbers with
themselves, confirmed by the prover's certificate; the arrows into and out of the pairs; and the
theorems of the round trip, citing the prover's certificate, and of an element of the pairs. The
result's last components are the certificates that confirm adding two and the product. -/
def developmentWith : Option (List Decl × Tree × Tree) := do
  let (i, lib) ← libraryWith false
  let (k, dev) ← (proveSeq twoPrim.seq (Prover.byNorm (rules i) twoPrim.seq.concl) cds).run lib
  let dfdProd : PartialHorn.Seq := ⟨[], [], dfd (prod nat nat)⟩
  let (k₂, dev) ← (proveSeq dfdProd (Prover.byNorm (rules i) dfdProd.concl) cds).run dev
  let q ← Internal.compileEq G₅ 0 [prod nat nat]
    (Term.arr 7 [nat] (Term.arr 6 [nat] (Term.var 0))) (Term.var 0)
  let (k₃, dev) ← (proveSeq q (Prover.byNorm (rules i) q.concl) cds).run dev
  let c := Scope.cite ⟨[], []⟩ k
  let c₂ := Scope.cite ⟨[], []⟩ k₂
  let c₃ := Scope.cite ⟨[], []⟩ k₃
  let E : Array Entry := (dev.map fun (s, _) ↦ Entry.combinators s).toArray
  let d ← Internal.byNorm G₃ E 0 [.delta 2] 16 [] [] (Term.defn 2 [] [Term.arr 4 [] Term.star])
    (Term.arr 5 [] (Term.arr 4 [] Term.star))
  pure (dev.map (fun (s, c) ↦ Decl.combinators s c) ++
    [Decl.constant onePrim none, Decl.constant twoPrim (some c), Decl.definition addTwoD,
      Decl.language addTwoOne d, Decl.object 1 pairsObj none,
      Decl.object 0 (prod nat nat) (some c₂), Decl.constant toPairs none,
      Decl.constant fromPairs none, Decl.language roundTrip (nd (.cert c₃)),
      Decl.language pairsRefl (nd .join [nd .refl, nd .refl])], c, c₂)

/-- The development. -/
def development : Option (List Decl) := developmentWith.map Prod.fst

/-- The declarations of the combinators that open the development. -/
def opening (ds : List Decl) : List Decl := ds.take (ds.length - 10)

-- the development checks, its declarations of every kind
#guard development.any fun ds ↦ checkThms G ds #[]

-- the theorem does not check before the constants it applies
#guard development.any fun ds ↦ !checkThms G (opening ds ++
  (ds.drop (ds.length - 7)).take 1 ++ (ds.drop (ds.length - 10)).take 3) #[]

-- the certificate does not confirm a primitive arrow of another codomain
#guard developmentWith.any fun (ds, c, _) ↦ !checkThms G (opening ds ++
  [Decl.constant ⟨0, comp succ succ, nat, one⟩ (some c)]) #[]

-- a theorem in a context of the pairs does not check before their definition
#guard development.any fun ds ↦ !checkThms G (opening ds ++ (ds.drop (ds.length - 1))) #[]

-- the certificate of the product's definedness does not confirm another object
#guard developmentWith.any fun (ds, _, c₂) ↦ !checkThms G (opening ds ++
  [Decl.object 0 (prod nat one) (some c₂)]) #[]

end GebTests.Prototypes.FreeTopos.InternalConstants

end
