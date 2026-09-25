/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep

set_option doc.verso true in
/-!
# The computational core's theorems, proved in the combinators

The theorems of {lit}`bootstrap/proofs/prelude.geb` and {lit}`bootstrap/proofs/nat.geb`, proved
again in the theory of an elementary topos by the prover: appending lists, and addition on the
natural numbers object. A function of several arguments is an arrow from their product;
appending is recursion on the first list into the exponential of lists, evaluated at the
second, and addition is recursion on its second argument into the exponential of the natural
numbers object, evaluated at the first. A theorem quantified over lists or numbers is an
equation between arrows. Each is proved by normalization, by induction through the uniqueness
of recursion, or by rewriting with an earlier theorem, and the development of the library and
the theorems checks.

## Main definitions

* {lit}`append`, {lit}`add` — appending lists and addition.
* {lit}`appendNilLeft`, {lit}`appendNil`, {lit}`appendAssoc`, {lit}`appendNilTwice` — the
  prelude's theorems.
* {lit}`addZero`, {lit}`addSucc`, {lit}`addZeroLeft` — the theorems about addition.
* {lit}`benchmark` — the development proving them.

## Tags

elementary topos, prover, benchmark, lists, natural numbers
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Benchmark

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts

/-- The list object of the object variable. -/
def L : Tree := list (x 0)

/-- The product of two list objects, the parameter of appending's recursion. -/
def P : Tree := prod L L

/-- Appending to the empty list, curried: the identity of lists. -/
def appendNilC : Tree := curry one L (snd one L)

/-- The product of an element and a curried appending. -/
def appendStepDom : Tree := prod (x 0) (exp L L)

/-- Appending to a constructed list, curried: the element constructed onto the tail's
appending. -/
def appendConsC : Tree := curry appendStepDom L
  (comp (cons (x 0)) (pair (comp (fst (x 0) (exp L L)) (fst appendStepDom L))
    (comp (ev L L) (pair (comp (snd (x 0) (exp L L)) (fst appendStepDom L))
      (snd appendStepDom L)))))

/-- Appending, curried: recursion on the first list. -/
def appendC : Tree := listRec (x 0) appendNilC appendConsC

/-- Appending two lists. -/
def append : Tree := comp (ev L L) (pair (comp appendC (fst L L)) (snd L L))

/-- The empty list, as an arrow from lists. -/
def nilL : Tree := comp (nil (x 0)) (bang L)

/-- The empty list is a left unit of appending. -/
def appendNilLeft : Seq := ⟨[obj], [], ⟨comp append (pair nilL (idt L)), idt L⟩⟩

/-- The empty list is a right unit of appending. -/
def appendNil : Seq := ⟨[obj], [], ⟨comp append (pair (idt L) nilL), idt L⟩⟩

/-- Appending is associative. -/
def appendAssoc : Seq := ⟨[obj], [], ⟨
  comp append (pair (comp append (pair (fst L P) (comp (fst L L) (snd L P))))
    (comp (snd L L) (snd L P))),
  comp append (pair (fst L P) (comp append (snd L P)))⟩⟩

/-- Appending the empty list twice. -/
def appendNilTwice : Seq :=
  ⟨[obj], [], ⟨comp append (pair (comp append (pair (idt L) nilL)) nilL), idt L⟩⟩

/-- Addition, curried: recursion on the second argument. -/
def addC : Tree :=
  natRec (curry one nat (snd one nat)) (curry (exp nat nat) nat (comp succ (ev nat nat)))

/-- Addition. -/
def add : Tree := comp (ev nat nat) (pair (comp addC (snd nat nat)) (fst nat nat))

/-- Zero, as an arrow from the natural numbers object. -/
def zeroNat : Tree := comp zeroN (bang nat)

/-- Zero is a right unit of addition. -/
def addZero : Seq := ⟨[], [], ⟨comp add (pair (idt nat) zeroNat), idt nat⟩⟩

/-- Addition of a successor is the successor of addition. -/
def addSucc : Seq :=
  ⟨[], [], ⟨comp add (pair (fst nat nat) (comp succ (snd nat nat))), comp succ add⟩⟩

/-- Zero is a left unit of addition. -/
def addZeroLeft : Seq := ⟨[], [], ⟨comp add (pair zeroNat (idt nat)), idt nat⟩⟩

/-- The development of the library and the theorems, each proved by its tactic. -/
def benchmark : Option Development := library.bind fun (i, d) ↦ ((do
  let rs := rules i
  let _ ← proveSeq appendNilLeft (byNorm rs appendNilLeft.concl)
  let an ← proveSeq appendNil
    (byListInduction rs (x 0) (nil (x 0)) (cons (x 0)) appendNil.concl)
  let _ ← proveSeq appendAssoc (byListParamInduction rs (x 0) append
    (comp (cons (x 0)) (fst (prod (x 0) L) P)) appendAssoc.concl)
  let k ← normalizeThm rs an
  let _ ← proveSeq appendNilTwice (byNorm (rs ++ [{ src := .thm k }]) appendNilTwice.concl)
  let _ ← proveSeq addZero (byNorm rs addZero.concl)
  let _ ← proveSeq addSucc (byNorm rs addSucc.concl)
  let _ ← proveSeq addZeroLeft (byNatInduction rs zeroN succ addZeroLeft.concl)
  pure () : StateT Development Option Unit).run d).map Prod.snd

-- the theorems are proved, and the development checks
#guard benchmark.any (checkDevelopment theory)

end GebTests.Prototypes.FreeTopos.Benchmark

end
