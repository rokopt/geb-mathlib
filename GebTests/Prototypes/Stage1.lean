/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep
public import GebMirror.Hygiene -- shake: keep
public meta import GebMirror.Hygiene -- shake: keep
public import Geb.Prototypes.Kernel.LoadCommand -- shake: keep
public meta import Geb.Prototypes.Kernel.LoadCommand -- shake: keep

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

-- The emitted module compiles and its definition references survive local and runtime names,
-- quoted-identifier delimiters, the encoding prefix, and line breaks.
#guard GebMirror.Hygiene.«main» (leaf 99) = mk 99 ((List.range 10).map fun n ↦ leaf (n + 1))
#guard GebMirror.Hygiene.«Prefix._root_.GebBoot.name» = leaf 10

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

/-- Names that exercise the Lean backend's escaping and qualification. -/
def hygieneSource : String := include_str "../../bootstrap/hygiene.geb"

-- The loader finds the escaped mirror names and proves each definition's denotation.
run_cmd do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let some b := (runImage img (ofBytes hygieneSource.toUTF8)).bind toBytes |>.bind readImage
    | throwError "the hygiene fixture does not compile"
  let some ds := unbundle b | throwError "the hygiene fixture does not unbundle"
  let some gs := load (ds.map Prod.snd) | throwError "the hygiene fixture does not load"
  Lean.Elab.Command.liftCoreM <| LoadCommand.declareLoading
    `Geb.Kernel.Stage1Tests.hygiene `GebMirror.Hygiene ds (gs.map (·.1)) false

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
-- that is not a member, a decoding into a function of trees, a list headed by a keyword in none
-- of its forms, and a decoding whose default, read in the scope of the variable the erasure
-- binds to the decoded tree, is that tree, of another type than the function's result, a datum
-- one of whose atoms names a numeral abbreviation, which the reader replaces, a decoding of a
-- datatype whose recognizer's name a numeral abbreviation abbreviates, which the reader would read
-- in place of the recognizer the erasure writes, a case analysis missing a constructor, a numeral
-- abbreviation named by a numeral, which the reader would expand in the labels a case analysis's
-- erasure tests, and a term naming one of the names the erasure binds, as a decoding's default
-- naming the variable bound to the decoded tree; the compiler rejects a clause's
-- variable named like the erasure's own; the typing accepts the representation given to the
-- primitive, an application to several arguments, that clause with its variable renamed, and a
-- datum whose atom names no abbreviation, read as its characters' codes. The raw typing entry
-- also rejects names reserved for generated operations; module elaboration gives source binders
-- private names, so the public compiler accepts these binders.
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
    ("(def k (lam ((lam (Arrow T T)) (x T)) (lam x)))", "k"),
    (nat ++ "(def v (lam ((\"%e\" Nat)) (decode Nat 7 (lam ((n Nat)) n) \"%e\")))", "v"),
    ("(data Q (q0) (q1 T T)) (defnum ab 3) (def d (datum Q (1 ab)))", "d"),
    ("(defnum Nat.member 3) " ++ nat ++
      "(def e (lam ((t T)) (decode Nat t (lam ((n Nat)) (rep n)) 0)))", "e"),
    (nat ++ "(def z (lam ((n Nat)) (case n ((zero) 0))))", "z"),
    ("(data D (a T) (b T)) (defnum 0 1) " ++
      "(def m (lam ((t T)) (case (datum D (1 (9))) ((a x) 2) ((b y) 3))))", "0"),
    (nat ++ "(def m (lam ((t T)) (decode Nat t (lam ((n Nat)) (rep n)) \"%e\")))", "m")]
  let privateBinders := [
    ("(def b (lam ((rep T)) rep))", "b"), ("(def c (lam ((x T) (datum T)) x))", "c"),
    ("(def u (lam ((fold T)) fold))", "u"),
    (nat ++ "(def m (lam ((Nat.member (Arrow T T))) " ++
      "(decode Nat 7 (lam ((n Nat)) n) zero)))", "m"),
    (nat ++ "(def q (lam ((child (Arrow T (Arrow T T))) (t Nat)) " ++
      "(case t ((zero) zero) ((succ n) n))))", "q")]
  for (p, n) in rejected ++ privateBinders do
    unless typeErrorOf p == some (nameTree n.toList) do
      throw (IO.userError s!"the typing does not reject {n}")
  for (p, n) in rejected do
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {n}")
  for (p, n) in privateBinders do
    unless ((runImage img (nameTree p.toList)).bind toBytes).bind readImage |>.isSome do
      throw (IO.userError s!"the stage-1 compiler rejects the private binder in {n}")
  let clause (x : String) : String :=
    nat ++ "(data Q (mk T Nat)) (def s (lam ((p Q)) (case p ((mk " ++ x ++ " y) y))))"
  unless runImage img (nameTree (clause "\"%s\"").toList) == some (mk 0 []) do
    throw (IO.userError "the stage-1 compiler compiles a clause's variable named %s")
  let accepted := [nat ++ "(def h (lam ((n Nat)) (label (rep n))))", clause "x",
    "(def p (lam ((f (Arrow T (Arrow T T))) (x T)) (f x x)))",
    "(data L (l0) (l1 & T)) (def d (datum L (1 ab)))"]
  unless accepted.all fun p ↦ typeErrorOf p == some (mk 0 []) do
    throw (IO.userError "the typing rejects a well-typed program")

-- Private source binders cannot capture generated operations. Patterns repeat &, and omitted
-- bindings preserve field positions and lexical scope, including nested shadowing and quotations.
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let compile (p : String) : Option ByteArray := (runImage img (nameTree p.toList)).bind toBytes
  let run (p : String) : Option Tree := do
    runEntry (← readImage (← compile p)) "main".toList (leaf 0)
  let packet := "(data Packet (packet T T & T)) "
  let value := "(packet 10 20 (cons 30 (nil T)))"
  let clause (pat body : String) := packet ++ "(def main (lam ((t T)) (case " ++ value ++
    " ((packet " ++ pat ++ ") " ++ body ++ "))))"
  for (p, expected) in [
      (clause "_ y & xs" "(add y (lcase T T xs 0 (lam ((h T) (r (List T))) h)))", leaf 50),
      (clause "_ y & _" "y", leaf 20),
      (clause "x y & xs" "((lam ((x T)) x) y)", leaf 20),
      (clause "x x & _" "x", leaf 20),
      (packet ++ "(def choose (lam ((_ T)) (case " ++ value ++
        " ((packet _ y & _) _)))) (def main (lam ((t T)) (choose 99)))", leaf 99),
      (packet ++ "(def choose (lam ((label T) (children T) (eq T) (child T)) " ++
        "(case " ++ value ++ " ((packet _ y & _) y))))" ++
        "(def main (lam ((t T)) (choose 1 2 3 4)))", leaf 20)] do
    unless run p == some expected && agreesOn img compiler.toList p.toList do
      throw (IO.userError s!"hygiene or pattern semantics disagree: {p}")
  for body in ["y", "((lam ((x T)) x) y)", "(quote (0 x))",
      "(case " ++ value ++ " ((packet x z & _) x))"] do
    let named := compile (clause "x y & xs" body)
    let ignored := compile (clause "_ y & _" body)
    unless (named.bind readImage).isSome && (ignored.bind readImage).isSome && named != ignored do
      throw (IO.userError s!"an unused named pattern binding is omitted: {body}")
  for pat in ["x y xs", "& x y xs", "x & y xs", "x y & &", "x y & xs & ys"] do
    let p := clause pat "0"
    unless compile p == some ByteArray.empty && agreesOn img compiler.toList p.toList do
      throw (IO.userError s!"a malformed rest pattern is accepted: {pat}")
  unless compile (clause "_ y & _" "_") == some ByteArray.empty do
    throw (IO.userError "a wildcard binds a name")
  let nat := "(data Nat (zero) (succ Nat)) "
  let p := nat ++ "(defn size ((unit T) (node T) (n Nat)) T " ++
    "(cata Nat T n ((zero) 0) ((succ r) (add r 1)))) " ++
    "(defn decodeSize ((Nat.member (Arrow T T)) (t T)) T " ++
    "(decode Nat t (lam ((n Nat)) (size 99 99 n)) 9)) " ++
    "(def main (lam ((t T)) (decodeSize (lam ((u T)) 0) (quote (1 (1 (0)))))))"
  unless run p == some (leaf 2) && agreesOn img compiler.toList p.toList do
    throw (IO.userError "a source binder captures recursion or decoding")
  let ignored := nat ++ "(def main (lam ((t T)) " ++
    "(cata Nat T (succ (succ zero)) ((zero) 7) ((succ _) 3))))"
  unless run ignored == some (leaf 3) && agreesOn img compiler.toList ignored.toList do
    throw (IO.userError "a discarded recursive field changes the result")
  let named := ignored.replace "(succ _)" "(succ unused)"
  unless run named == some (leaf 3) && agreesOn img compiler.toList named.toList &&
      compile named != compile ignored do
    throw (IO.userError "an unused named recursive field loses its binding")
  let abbreviated := "(defnum _ 42) " ++ ignored
  unless run abbreviated == some (leaf 3) && agreesOn img compiler.toList abbreviated.toList do
    throw (IO.userError "a numeral abbreviation changes a wildcard")
  let foldClause (pat body : String) :=
    "(data Rose (tip T) (branch Rose Rose & Rose)) (def main (lam ((t T)) " ++
    "(cata Rose T (branch (tip 10) (tip 20) (cons (tip 30) (nil Rose))) " ++
    "((tip n) n) ((branch " ++ pat ++ ") " ++ body ++ "))))"
  for (pat, body, expected) in [
      ("_ y & rs", "(add y (foldr T T add 0 rs))", 50),
      ("_ y & _", "y", 20), ("_ _ & _", "99", 99)] do
    let p := foldClause pat body
    unless run p == some (leaf expected) && agreesOn img compiler.toList p.toList do
      throw (IO.userError s!"discarded recursive fields change later positions: {pat}")
  let namedRest := compile (foldClause "_ y & unused" "y")
  unless (namedRest.bind readImage).isSome && namedRest != compile (foldClause "_ y & _" "y") do
    throw (IO.userError "an unused named recursive rest field loses its binding")

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

-- the stage-1 compiler checks a declaration with type parameters at opaque sorts where it is
-- declared: it rejects a function applying a primitive of trees to a value of its parameter's
-- type, one representing such a value, and one applying the primitive to a field of that type of
-- a datatype's instance, though nothing uses them and the stage-0 compiler compiles them; it
-- rejects a constructor's instance at one type where the datatype's instance at another is
-- required, and the instance of a datatype at a type of lists, which a field does not hold; and
-- it compiles, as the stage-0 compiler does, a datatype and a function over it used at the trees
-- and at a datatype, and modules of which one returns an optional value that another consumes,
-- with a function over lists and a composition each at two lists of types
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let main := " (def main (lam ((t T)) t))"
  let option := "(data (Option A) (none) (some A))"
  let orElse := " (defn (orElse A) ((d A) (m (Option A))) A (case m ((some A x) x) ((none A) d)))"
  for p in ["(defn (peek A) ((x A)) T (label x))" ++ main,
      "(defn (peek A) ((x A)) T (rep x))" ++ main,
      option ++ " (defn (peek A) ((m (Option A))) T" ++
        " (case m ((some A x) (label x)) ((none A) 0)))" ++ main] do
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {p}")
    if runMain compiler.toList (nameTree p.toList) == some (mk 0 []) then
      throw (IO.userError s!"the stage-0 compiler rejects {p}")
  for p in [option ++ " (data Light (red) (green))" ++
        " (defn use ((t T)) (Option Light) (some T t))" ++ main,
      option ++ " (def lists (none (List T)))" ++ main] do
    unless runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler compiles {p}")
  unless [option ++ orElse ++ " (data Light (red) (green))" ++
        " (def main (lam ((t T)) (node (orElse T t (none T))" ++
        " (cons (rep (orElse Light red (some Light green))) (nil T)))))",
      "(module Optional (export Option none some orElse) " ++ option ++ orElse ++ ")" ++
        " (module Lists (export map find) (import Optional)" ++
        " (defn (map A B) ((f (Arrow A B)) (xs (List A))) (List B)" ++
        " (foldr A (List B) (lam ((x A) (r (List B))) (cons (f x) r)) (nil B) xs))" ++
        " (defn (find A) ((p (Arrow A T)) (xs (List A))) (Option A)" ++
        " (foldr A (Option A) (lam ((x A) (r (Option A))) (if (p x) (some A x) r))" ++
        " (none A) xs)))" ++
        " (module Functions (export compose)" ++
        " (defn (compose A B C) ((g (Arrow B C)) (f (Arrow A B))) (Arrow A C)" ++
        " (lam ((x A)) (g (f x)))))" ++
        " (module Finder (export first) (import Optional) (import Lists)" ++
        " (defn first ((xs (List T))) (Option T) (find T (lam ((x T)) x) xs)))" ++
        " (module Client (export run) (import Optional) (import Lists) (import Functions)" ++
        " (import Finder) (data Light (red) (green))" ++
        " (defn lightOf ((x T)) Light (if x green red))" ++
        " (defn shade ((l Light)) T (case l ((red) 1) ((green) 2)))" ++
        " (defn run ((t T)) T (node (orElse T 0 (first (children t)))" ++
        " (map Light T shade (map T Light lightOf (children t))))))" ++
        " (def main (lam ((t T)) (Client.run" ++
        " ((Functions.compose T T T (lam ((x T)) x) (lam ((x T)) x)) t))))"].all fun p ↦
      runImage img (nameTree p.toList) != some (mk 0 []) && agreesOn img compiler.toList p.toList do
    throw (IO.userError "the stage-1 compiler rejects declarations with type parameters")

-- module elaboration removes chains before the datatype typing: both compilers emit the same
-- image as the nested forms, and the stage-1 compiler checks their datatype annotations
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  let program := "(data N (z) (s N)) (def main (lam ((t T)) "
  let chain := program ++ "(let* ((x N z) (y N (s x)))" ++
    " (cond ((eq t 0) (rep x)) (else (rep y))))))"
  let nested := program ++ "(let x N z (let y N (s x) (if (eq t 0) (rep x) (rep y))))))"
  let out := runImage img (nameTree chain.toList)
  unless ((out.bind toBytes).bind readImage).isSome &&
      out == runImage img (nameTree nested.toList) &&
      agreesOn img compiler.toList chain.toList do
    throw (IO.userError "binding and conditional chains disagree with their nested forms")
  for body in ["(let* ((x N t)) (rep x))", "(cond (1 z) (else t))",
      "(cond ((eq t 0) (rep z)))", "(cond (else 0) (else 1))"] do
    let p := program ++ body ++ "))"
    unless (readSExps p.toList).isSome && runImage img (nameTree p.toList) == some (mk 0 []) do
      throw (IO.userError s!"the stage-1 compiler accepts the invalid chain {body}")

end Geb.Kernel.Stage1Tests

end
