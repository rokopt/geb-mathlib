/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Internal -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Internal -- shake: keep
public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep

set_option doc.verso true in
/-!
# The computational core's theorems, stated in the internal language

The theorems of {lit}`bootstrap/proofs/prelude.geb` and {lit}`bootstrap/proofs/nat.geb`, stated
as equations of the internal language between terms applying its definitions of appending and
addition, compiled to sequents of the combinators and proved by the prover: by unfolding the
definitions and normalizing, by induction through the uniqueness of recursion, or by rewriting
with an earlier theorem. A theorem's context is compiled over the product of its variables'
types without the terminal object, so that its arrows are from a list object, the natural
numbers object or their products, as the prover's induction takes them.

## Main definitions

* {lit}`stmt` — the sequent an equation compiles to in an environment.
* {lit}`benchmark` — the development proving the theorems.

## Tags

internal language, prover, benchmark, lists, natural numbers
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalBenchmark

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term compile compileDefs)
open scoped FinEnum

/-- The definitions of the combinators that appending and addition compile to. -/
def cds : List PartialHorn.Defn := (compileDefs G).getD []

/-- The sequent an equation of two terms in {lit}`n` object variables compiles to, in an
environment over {lit}`X`. -/
def stmt (n : ℕ) (X : Tree) (e : List (Tree × Tree)) (t u : Term) : Option Seq := do
  let (f, a) ← compile G n t X e
  let (g, b) ← compile G n u X e
  if a = b then pure ⟨List.replicate n obj, [], ⟨f, g⟩⟩ else none

/-- The product of two lists, the parameter of appending's associativity. -/
def P : Tree := prod L L

/-- The environment of a list variable. -/
def envL : List (Tree × Tree) := [(idt L, L)]

/-- The environment of a natural number variable. -/
def envN : List (Tree × Tree) := [(idt nat, nat)]

/-- The environment of two natural number variables, the second the innermost. -/
def envNN : List (Tree × Tree) := [(snd nat nat, nat), (fst nat nat, nat)]

/-- The environment of two list variables, the second the innermost. -/
def envP : List (Tree × Tree) := [(snd L L, L), (fst L L, L)]

/-- The environment of three list variables, the last two the parameter. -/
def envLP : List (Tree × Tree) :=
  [(comp (snd L L) (snd L P), L), (comp (fst L L) (snd L P), L), (fst L P, L)]

/-- The empty list is a left unit of appending. -/
def appendNilLeft : Option Seq := stmt 1 L envL (appendT nilT (Term.var 0)) (Term.var 0)

/-- The empty list is a right unit of appending. -/
def appendNil : Option Seq := stmt 1 L envL (appendT (Term.var 0) nilT) (Term.var 0)

/-- Appending is associative. -/
def appendAssoc : Option Seq := stmt 1 (prod L P) envLP
  (appendT (appendT (Term.var 2) (Term.var 1)) (Term.var 0))
  (appendT (Term.var 2) (appendT (Term.var 1) (Term.var 0)))

/-- Appending the empty list twice. -/
def appendNilTwice : Option Seq :=
  stmt 1 L envL (appendT (appendT (Term.var 0) nilT) nilT) (Term.var 0)

/-- Zero is a right unit of addition. -/
def addZero : Option Seq := stmt 0 nat envN (addT (Term.var 0) zeroT) (Term.var 0)

/-- Addition of a successor is the successor of addition. -/
def addSucc : Option Seq := stmt 0 (prod nat nat) envNN
  (addT (Term.var 1) (succT (Term.var 0))) (succT (addT (Term.var 1) (Term.var 0)))

/-- Zero is a left unit of addition. -/
def addZeroLeft : Option Seq := stmt 0 nat envN (addT zeroT (Term.var 0)) (Term.var 0)

/-- Appending the parameter's lists, the start of the recursion in associativity. -/
def appendP : Option Tree :=
  (compile G 1 (appendT (Term.var 1) (Term.var 0)) P envP).map Prod.fst

/-- The development of the library and the theorems, each proved by its tactic with the
compiled definitions in force. -/
def benchmark : Option Development := library.bind fun (i, d) ↦ ((do
  let prove (a : Seq) (m : PM Tree) := proveSeq a m cds (infer := true)
  let rs := rules i
  let lrs := rs ++ [deltaRule 0]
  let nrs := rs ++ [deltaRule 1]
  let some a := appendNilLeft | failure
  let _ ← prove a (byNorm lrs a.concl)
  let some a := appendNil | failure
  let an ← prove a (byListInduction lrs (x 0) (nil (x 0)) (cons (x 0)) a.concl)
  let some a := appendAssoc | failure
  let some z := appendP | failure
  let _ ← prove a (byListParamInduction lrs (x 0) z
    (comp (cons (x 0)) (fst (prod (x 0) L) P)) a.concl)
  let k ← normalizeThm lrs an cds (infer := true)
  let some a := appendNilTwice | failure
  let _ ← prove a (byNorm (lrs ++ [{ src := .thm k }]) a.concl)
  let some a := addZero | failure
  let _ ← prove a (byNorm nrs a.concl)
  let some a := addSucc | failure
  let _ ← prove a (byNorm nrs a.concl)
  let some a := addZeroLeft | failure
  let _ ← prove a (byNatInduction nrs zeroN succ a.concl)
  pure () : StateT Development Option Unit).run d).map Prod.snd

-- the theorems are proved, and the development, its terms shared, checks in the extension by
-- the compiled definitions, with the typing inferred
#guard benchmark.any fun d ↦ (share (theory.extendAll cds) d).any (checkTopos cds)

end GebTests.Prototypes.FreeTopos.InternalBenchmark

end
