/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The stage-1 compiler

The stage-1 compiler is the stage-0 compiler with the expansion of the datatype language rewritten
in the datatype language, {lit}`bootstrap/stage1/datatype.geb`. The seed cannot read the datatype
language, so the stage-0 compiler builds its image, the committed {lit}`bootstrap/compiler.img`,
which {lit}`scripts/bootstrap.sh` checks natively to be the stage-0 compiler's image of the
stage-1 sources; run from that image, the stage-1 compiler agrees with the stage-0 compiler on
the programs in the datatype language and the kernel's examples. The fixed point of the staged
self-compilation, where the stage-1 compiler compiles its own source to its own image, is
checked natively by the same script, with the Lean backend.

## Main definitions

* {lit}`runImage` runs an image's definition named {lit}`main` on an input tree.
* {lit}`agreesOn` compares the stage-1 compiler's image with the stage-0 compiler on a program.
* The typing of the stage-1 compiler, {lit}`bootstrap/stage1/typing.geb`, is tested through the
  image's {lit}`Datatype.typeErrorOf`, which names the first definition it rejects.

## Tags

bootstrap, stage 1, self-compilation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Stage1Tests

open Stage0Tests
open scoped FinEnum

/-- Run an image on an input tree: apply its definition named {lit}`main`. -/
def runImage (img : ByteArray) (input : Tree) : Option Tree := do
  runEntry (← readImage img) ['m', 'a', 'i', 'n'] input

/-- Whether an image of the stage-1 compiler compiles a program as the stage-0 compiler, given as
text, does. -/
def agreesOn (img : ByteArray) (compilerText p : List Char) : Bool :=
  runImage img (nameTree p) == runMain compilerText (nameTree p)

-- the stage-1 compiler, from the committed image, agrees with the stage-0 compiler on the
-- programs in the datatype language and the kernel's examples
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  unless [naturals, roses, decoding, Tests.factorial, Tests.sugar, Tests.numerals, Tests.listCase,
      "(def f (lam (x T) y))", "(defnum n m)"].all (agreesOn img compiler.toList ·.toList) do
    throw (IO.userError "the stage-1 compiler disagrees with the stage-0 compiler")

-- the stage-1 compiler checks the datatypes data declares, each distinct from the trees: it
-- rejects, naming the definition, a case analysis of a tree, a constructor applied to a tree, a
-- primitive of trees applied to a value of a datatype, the representation of a tree, a datum
-- that is not a member, and a decoding into a function of trees; it accepts the representation
-- given to the primitive, and the datatypes tree-data declares
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let some t := readImage img | throw (IO.userError "the committed image does not read")
  let typeErrorOf (p : String) : Option Tree :=
    runEntry t "Datatype.typeErrorOf".toList (nameTree p.toList)
  let nat := "(data Nat (zero) (succ Nat)) "
  let rejected := [(nat ++ "(def f (lam ((t T)) (case t ((zero) 0) ((succ n) 1))))", "f"),
    (nat ++ "(def g (lam ((t T)) (succ t)))", "g"),
    (nat ++ "(def h (lam ((n Nat)) (label n)))", "h"),
    ("(def r (lam ((t T)) (rep t)))", "r"),
    (nat ++ "(def d (datum Nat (2)))", "d"),
    (nat ++ "(def e (lam ((t T)) (decode Nat t (lam ((x T)) 1) 0)))", "e")]
  for (p, n) in rejected do
    unless typeErrorOf p == some (nameTree n.toList) do
      throw (IO.userError s!"the typing does not reject {n}")
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {n}")
  let accepted := [nat ++ "(def h (lam ((n Nat)) (label (rep n))))",
    "(tree-data Nat (zero) (succ Nat)) (def f (lam ((t T)) (case t ((zero) 0) ((succ n) 1))))"]
  unless accepted.all fun p ↦ typeErrorOf p == some (mk 0 []) do
    throw (IO.userError "the typing rejects a well-typed program")

-- the stage-1 compiler checks a template at opaque sorts, which have no representation: it
-- rejects a template applying a primitive of trees to a value of its sort, or representing it,
-- though no import instantiates it and the stage-0 compiler compiles it; it compiles, as the
-- stage-0 compiler does, a template over a sort and an operation, and one declaring a datatype
-- whose field is of its sort
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let main := " (def main (lam ((t T)) t))"
  for p in ["(module Bad (parameter A) (export f) (def f (lam ((x A)) (label x))))" ++ main,
      "(module Peek (parameter A) (export f) (def f (lam ((x A)) (rep x))))" ++ main] do
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {p}")
    if runMain compiler.toList (nameTree p.toList) == some (mk 0 []) then
      throw (IO.userError s!"the stage-0 compiler rejects {p}")
  unless ["(module Twice (parameter A) (parameter (f (A) A)) (export twice)" ++
        " (def twice (lam ((x A)) (f (f x))))) (def inc (lam ((x T)) (add x 1)))" ++
        " (import (Twice T inc)) (def main (lam ((t T)) (twice t)))",
      "(module Box (parameter A) (export box unbox) (data Box (box A))" ++
        " (defn unbox ((b Box)) A (case b ((box x) x)))) (import (Box T))" ++
        " (def main (lam ((t T)) (unbox (box t))))"].all fun p ↦
      runImage img (nameTree p.toList) != some (mk 0 []) && agreesOn img compiler.toList p.toList do
    throw (IO.userError "the stage-1 compiler rejects a template the typing admits")

end Geb.Kernel.Stage1Tests

end
