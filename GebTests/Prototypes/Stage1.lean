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

* {lit}`seq`, {lit}`typing`, {lit}`datatype` — the sources the stage-1 compiler adds to the
  stage-0 compiler's, in the datatype language.
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

/-- The source of the lists of the datatype language, a module with a parameter. -/
def seq : String := include_str "../../bootstrap/seq.geb"

/-- The source of the stage-1 typing. -/
def typing : String := include_str "../../bootstrap/stage1/typing.geb"

/-- The source of the stage-1 expansion of the datatype language. -/
def datatype : String := include_str "../../bootstrap/stage1/datatype.geb"

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
-- that is not a member, a decoding into a function of trees, a binder named by a keyword the
-- erasure rewrites, a variable named by a keyword, a list headed by a keyword in none of its
-- forms, binders named by a recognizer and by a primitive, which the erasure and the expansion
-- write free under them, a decoding whose default, read in the scope of the variable the erasure
-- binds to the decoded tree, is that tree, of another type than the function's result, a datum
-- one of whose atoms names a numeral abbreviation, which the reader replaces, a decoding of a
-- datatype whose recognizer's name a numeral abbreviation abbreviates, which the reader would read
-- in place of the recognizer the erasure writes, a case analysis missing a constructor, one of a
-- datatype tree-data declares, which has no marker to check its clauses against, and a numeral
-- abbreviation named by a numeral, which the reader would expand in the labels a case analysis's
-- erasure tests; the compiler rejects a clause's variable named like the erasure's own; the
-- typing accepts the representation given to the primitive, an application to several arguments,
-- that clause with its variable renamed, a decoding whose default is the decoded tree, and a datum
-- whose atom names no abbreviation, read as its characters' codes
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
    (nat ++ "(def e (lam ((t T)) (decode Nat t (lam ((x T)) 1) 0)))", "e"),
    ("(def b (lam ((rep T)) rep))", "b"), ("(def c (lam ((x T) (datum T)) x))", "c"),
    ("(def u (lam ((fold T)) fold))", "u"),
    ("(def k (lam ((lam (Arrow T T)) (x T)) (lam x)))", "k"),
    (nat ++ "(def m (lam ((Nat.member (Arrow T T))) " ++
      "(decode Nat 7 (lam ((n Nat)) n) zero)))", "m"),
    (nat ++ "(def v (lam ((\"%e\" Nat)) (decode Nat 7 (lam ((n Nat)) n) \"%e\")))", "v"),
    (nat ++ "(def q (lam ((child (Arrow T (Arrow T T))) (t Nat)) " ++
      "(case t ((zero) zero) ((succ n) n))))", "q"),
    ("(data Q (q0) (q1 T T)) (defnum ab 3) (def d (datum Q (1 ab)))", "d"),
    ("(defnum Nat.member 3) " ++ nat ++
      "(def e (lam ((t T)) (decode Nat t (lam ((n Nat)) (rep n)) 0)))", "e"),
    (nat ++ "(def z (lam ((n Nat)) (case n ((zero) 0))))", "z"),
    ("(tree-data Nat (zero) (succ Nat)) (def f (lam ((t T)) (case t ((zero) 0) ((succ n) 1))))",
      "f"),
    ("(data D (a T) (b T)) (defnum 0 1) " ++
      "(def m (lam ((t T)) (case (datum D (1 (9))) ((a x) 2) ((b y) 3))))", "0")]
  for (p, n) in rejected do
    unless typeErrorOf p == some (nameTree n.toList) do
      throw (IO.userError s!"the typing does not reject {n}")
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {n}")
  let clause (x : String) : String :=
    nat ++ "(data Q (mk T Nat)) (def s (lam ((p Q)) (case p ((mk " ++ x ++ " y) y))))"
  unless runImage img (nameTree (clause "\"%s\"").toList) == some (mk 0 []) do
    throw (IO.userError "the stage-1 compiler compiles a clause's variable named %s")
  let accepted := [nat ++ "(def h (lam ((n Nat)) (label (rep n))))", clause "x",
    "(def p (lam ((f (Arrow T (Arrow T T))) (x T)) (f x x)))",
    nat ++ "(def m (lam ((t T)) (decode Nat t (lam ((n Nat)) (rep n)) \"%e\")))",
    "(data L (l0) (l1 & T)) (def d (datum L (1 ab)))"]
  unless accepted.all fun p ↦ typeErrorOf p == some (mk 0 []) do
    throw (IO.userError "the typing rejects a well-typed program")

-- the stage-1 compiler reads the type of a decoding and of a datum through a type abbreviation as
-- the datatype it abbreviates: the datum is checked a member of the datatype, and the datatype's
-- recognizer decides the decoding, though a definition takes the abbreviation's recognizer name
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let p := "(data Nat (zero) (succ Nat)) (deftype N Nat) (def N.member (lam ((t T)) 1)) " ++
    "(def two (datum N (1 (1 (0))))) " ++
    "(def main (lam ((t T)) (decode N t (lam ((n Nat)) (rep n)) (rep two))))"
  let run (input : Tree) : Option Tree := do
    let out ← runImage img (nameTree p.toList)
    runEntry (← readImage (← toBytes out)) "main".toList input
  unless run (mk 7 []) == some (mk 1 [mk 1 [mk 0 []]]) && run (mk 0 []) == some (mk 0 []) do
    throw (IO.userError "a decoding through an abbreviation is not decided by its recognizer")

-- both compilers reject a program whose source names one of the implementation's names, those
-- beginning with %, outside its quotations and datums: a definition named as the variable the
-- erasure binds to a decoded tree, which would take its place in the decoding's default, and
-- binders named as the variables the expansions of case and cata bind, which would take their
-- places in the clauses; and both compile a program quoting such a name
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let nat := "(data Nat (zero) (succ Nat)) "
  let main := " (def main (lam ((t T)) t))"
  for p in [nat ++ "(def \"%e\" zero) " ++
        "(def m (lam ((t T)) (decode Nat t (lam ((n Nat)) n) \"%e\")))" ++ main,
      nat ++ "(def g (lam ((\"%s\" T) (n Nat)) (case n ((zero) \"%s\") ((succ m) 1))))" ++ main,
      nat ++ "(def g (lam ((\"%o\" T) (n Nat)) (cata Nat T n ((zero) \"%o\") ((succ r) r))))" ++
        main] do
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {p}")
    unless runMain compiler.toList (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-0 compiler compiles {p}")
  let quoted := "(def q (quote (1 \"%s\")))" ++ main
  unless runImage img (nameTree quoted.toList) != some (mk 0 []) &&
      agreesOn img compiler.toList quoted.toList do
    throw (IO.userError "a compiler rejects a program quoting an implementation's name")

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
