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
numbers object, evaluated at the first. Each is a definition of the theory's extension, as are
the curried cases of its recursion. A theorem quantified over lists or numbers is an equation
between arrows. The recursions' computation lemmas are proved by unfolding them; each theorem
is proved, with the recursions folded, by normalization, by induction through the uniqueness of
recursion, or by rewriting with an earlier theorem. The development of the library and the
theorems checks in the extension, and again as a shared development, its terms stored once
({name}`Geb.PartialHorn.checkShared`).

## Main definitions

* {lit}`defs`, {lit}`append`, {lit}`add` — the definitions, among them appending lists and
  addition.
* {lit}`appendCNil`, {lit}`appendCCons`, {lit}`addCZero`, {lit}`addCSucc` — the recursions'
  computation lemmas.
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

/-- The application of the definition at position {lit}`i` to arguments. -/
def defOp (i : ℕ) (args : List Tree) : Tree := op (sig.length + i) args

/-- Appending to the empty list, curried: the identity of lists. -/
def appendNilC : Tree := defOp 0 [x 0]

/-- Appending to a constructed list, curried: the element constructed onto the tail's
appending. -/
def appendConsC : Tree := defOp 1 [x 0]

/-- Appending, curried: recursion on the first list. -/
def appendC : Tree := defOp 2 [x 0]

/-- Appending two lists. -/
def append : Tree := defOp 3 [x 0]

/-- Adding zero, curried: the identity of the natural numbers object. -/
def addZeroC : Tree := defOp 4 []

/-- Adding a successor, curried: the successor after the addition. -/
def addSuccC : Tree := defOp 5 []

/-- Addition, curried: recursion on the second argument. -/
def addC : Tree := defOp 6 []

/-- Addition. -/
def add : Tree := defOp 7 []

/-- The product of an element and a curried appending. -/
def appendStepDom : Tree := prod (x 0) (exp L L)

/-- The definitions, each over the signature the earlier ones extend. -/
def defs : List Defn := [
  ⟨[obj], arr, curry one L (snd one L)⟩,
  ⟨[obj], arr, curry appendStepDom L
    (comp (cons (x 0)) (pair (comp (fst (x 0) (exp L L)) (fst appendStepDom L))
      (comp (ev L L) (pair (comp (snd (x 0) (exp L L)) (fst appendStepDom L))
        (snd appendStepDom L)))))⟩,
  ⟨[obj], arr, listRec (x 0) appendNilC appendConsC⟩,
  ⟨[obj], arr, comp (ev L L) (pair (comp appendC (fst L L)) (snd L L))⟩,
  ⟨[], arr, curry one nat (snd one nat)⟩,
  ⟨[], arr, curry (exp nat nat) nat (comp succ (ev nat nat))⟩,
  ⟨[], arr, natRec addZeroC addSuccC⟩,
  ⟨[], arr, comp (ev nat nat) (pair (comp addC (snd nat nat)) (fst nat nat))⟩]

-- each definition is well formed over the signature the earlier ones extend
#guard defs.zipIdx.all fun (d, i) ↦
  sortOf (sig ++ (defs.take i).map fun d ↦ (d.ctx, d.sort)) d.ctx d.body == some d.sort &&
    (List.range d.ctx.length).all fun j ↦ Occurs j d.body

/-- Curried appending at the empty list. -/
def appendCNil : Seq := ⟨[obj], [], ⟨comp appendC (nil (x 0)), appendNilC⟩⟩

/-- Curried appending at a constructed list. -/
def appendCCons : Seq :=
  ⟨[obj], [], ⟨comp appendC (cons (x 0)), comp appendConsC (prodMapRight (x 0) appendC)⟩⟩

/-- Curried addition at zero. -/
def addCZero : Seq := ⟨[], [], ⟨comp addC zeroN, addZeroC⟩⟩

/-- Curried addition at a successor. -/
def addCSucc : Seq := ⟨[], [], ⟨comp addC succ, comp addSuccC addC⟩⟩

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

/-- Zero, as an arrow from the natural numbers object. -/
def zeroNat : Tree := comp zeroN (bang nat)

/-- Zero is a right unit of addition. -/
def addZero : Seq := ⟨[], [], ⟨comp add (pair (idt nat) zeroNat), idt nat⟩⟩

/-- Addition of a successor is the successor of addition. -/
def addSucc : Seq :=
  ⟨[], [], ⟨comp add (pair (fst nat nat) (comp succ (snd nat nat))), comp succ add⟩⟩

/-- Zero is a left unit of addition. -/
def addZeroLeft : Seq := ⟨[], [], ⟨comp add (pair zeroNat (idt nat)), idt nat⟩⟩

/-- The development of the library and the theorems, each proved by its tactic, with the
definitions in force: the recursions' computation lemmas by unfolding them, and the theorems
with the recursions folded. -/
def benchmark : Option Development := library.bind fun (i, d) ↦ ((do
  let prove (a : Seq) (m : PM Tree) := proveSeq a m defs
  let rs := rules i
  let cn ← prove appendCNil (byNorm (rs ++ [deltaRule 2]) appendCNil.concl)
  let cc ← prove appendCCons (byNorm (rs ++ [deltaRule 2]) appendCCons.concl)
  let lrs := rs ++ [{ src := .thm cn }, { src := .thm cc }, deltaRule 0, deltaRule 1,
    deltaRule 3]
  let _ ← prove appendNilLeft (byNorm lrs appendNilLeft.concl)
  let an ← prove appendNil
    (byListInduction lrs (x 0) (nil (x 0)) (cons (x 0)) appendNil.concl)
  let _ ← prove appendAssoc (byListParamInduction lrs (x 0) append
    (comp (cons (x 0)) (fst (prod (x 0) L) P)) appendAssoc.concl)
  let k ← normalizeThm lrs an defs
  let _ ← prove appendNilTwice (byNorm (lrs ++ [{ src := .thm k }]) appendNilTwice.concl)
  let az ← prove addCZero (byNorm (rs ++ [deltaRule 6]) addCZero.concl)
  let as ← prove addCSucc (byNorm (rs ++ [deltaRule 6]) addCSucc.concl)
  let nrs := rs ++ [{ src := .thm az }, { src := .thm as }, deltaRule 4, deltaRule 5,
    deltaRule 7]
  let _ ← prove addZero (byNorm nrs addZero.concl)
  let _ ← prove addSucc (byNorm nrs addSucc.concl)
  let _ ← prove addZeroLeft (byNatInduction nrs zeroN succ addZeroLeft.concl)
  pure () : StateT Development Option Unit).run d).map Prod.snd

-- the theorems are proved, and the development checks in the extension by the definitions,
-- and again with its terms shared
#guard benchmark.any fun d ↦ checkDevelopment (theory.extendAll defs) d &&
  (share (theory.extendAll defs) d).any (checkShared (theory.extendAll defs))

end GebTests.Prototypes.FreeTopos.Benchmark

end
