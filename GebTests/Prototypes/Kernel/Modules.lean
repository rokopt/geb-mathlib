/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.ModuleIdentity -- shake: keep
public meta import Geb.Prototypes.Kernel.ModuleIdentity -- shake: keep
public import Geb.Prototypes.Kernel.Strict -- shake: keep
public meta import Geb.Prototypes.Kernel.Strict -- shake: keep
public import GebTests.Prototypes.Kernel.Identity -- shake: keep
public meta import GebTests.Prototypes.Kernel.Identity -- shake: keep

set_option doc.verso true in
/-!
# Module examples

A program without modules or binding and conditional chains is unchanged by their elaboration,
the kernel's examples among them. Modules without parameters export their definitions under
qualified names, imported unqualified or under a name. A module with parameters is instantiated at
each import, a sort parameter by a type and an operation by a term of its type. A name bound in a
term, a quoted datum and a hole are not renamed. A clash, an import naming no module or leaving a
parameter unsupplied, and an export naming nothing are rejected with a message. The elaboration
written in Geb, {lit}`bootstrap/modules.geb`, agrees with Lean's, and the stage-0 compiler
compiles a module of the datatype language. A module's identifier is unchanged by renaming the
module and its members, and changed, with the root's, by a change of one of its definitions;
the identifiers computed in Geb agree with Lean's.

Sequential bindings and guarded clauses give the same checked bundles as their nested forms,
with names resolved in each binding's scope and quotations preserved. Malformed chains and
declarations taking their keywords are rejected.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`.

## Tags

module, import, export, parameter, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.ModulesTests

open Geb.Kernel.Stage0Tests Document

-- a program without modules is unchanged, the kernel's examples among them
#guard [Tests.factorial, Tests.size, Tests.mirror, Tests.quadruple, Tests.sugar,
    Tests.numerals].all fun p ↦
  ((readSExps p.toList).bind expandModules).map (·.map canonOf) =
    (readSExps p.toList).map (·.map canonOf)

/-- A module of arithmetic exporting one of its definitions. -/
def arith : String :=
  "(module Arith (export double) (def twice (lam ((x T)) (add x x)))" ++
    " (def double (lam ((x T)) (twice x))))"

-- a module's declarations are qualified by its name, and its exports used as Arith.x
#guard (readProgram (arith ++ " (def main (lam ((t T)) (Arith.double 3)))").toList).map
    (·.map Prod.fst) =
  some ["Arith.twice".toList, "Arith.double".toList, "main".toList]
#guard runMain (arith ++ " (def main (lam ((t T)) (Arith.double 3)))").toList (leaf 0) =
  some (leaf 6)
-- an unexported definition is not visible outside its module
#guard diagnose (arith ++ " (def main (lam ((t T)) (Arith.twice 3)))").toList =
  some "main does not resolve"
-- imports, unqualified and under a name
#guard runMain ("(module A (export f) (def f (lam ((x T)) (add x 1))))" ++
    " (module B (import A) (export g) (def g (lam ((x T)) (f (f x)))))" ++
    " (def main (lam ((t T)) (B.g 0)))").toList (leaf 0) = some (leaf 2)
#guard runMain ("(module A (export f) (def f (lam ((x T)) (add x 1))))" ++
    " (import A as N) (def main (lam ((t T)) (N.f 0)))").toList (leaf 0) = some (leaf 1)
-- a nested module's exports, re-exported by the enclosing module
#guard runMain ("(module Outer (export Inner.y z)" ++
    " (module Inner (export y) (def y (lam ((x T)) (add x 2))))" ++
    " (def z (lam ((x T)) (Inner.y x))))" ++
    " (def main (lam ((t T)) (Outer.z (Outer.Inner.y 1))))").toList (leaf 0) = some (leaf 5)

/-- A module with a sort and an operation as parameters. -/
def twice : String :=
  "(module Twice (parameter A) (parameter (f (A) A)) (export twice)" ++
    " (def twice (lam ((x A)) (f (f x)))))" ++
    " (def inc (lam ((x T)) (add x 1)))"

-- a module with parameters is instantiated at its import
#guard runMain (twice ++ " (module Use (import (Twice T inc)) (export run)" ++
    " (def run (lam ((x T)) (twice x))))" ++
    " (def main (lam ((t T)) (Use.run 5)))").toList (leaf 0) = some (leaf 7)
#guard runMain (twice ++ " (def cons2 (lam ((xs (List T))) (cons 0 xs)))" ++
    " (import (Twice (List T) cons2) as L)" ++
    " (def main (lam ((t T)) (node 9 (L.twice (nil T)))))").toList (leaf 0) =
  some (mk 9 [leaf 0, leaf 0])
-- a parameter left unsupplied, and an argument of the wrong type, are rejected
#guard diagnose (twice ++ " (import (Twice T))").toList =
  some "the import of Twice supplies 1 of its 2 parameters"
#guard (diagnose (twice ++ " (def u (lam ((x T)) unit)) (import (Twice T u))").toList).isSome

-- a name bound in a term is not renamed, nor a quoted datum
#guard runMain ("(module M (export h q) (def tail (lam ((x T)) x))" ++
    " (def h (lam ((tail T)) tail)) (def q (lam ((x T)) (quote (0 tail)))))" ++
    " (def main (lam ((t T)) (node 0 (cons (M.h 4) (children (M.q 0))))))").toList (leaf 0) =
  some (mk 0 (leaf 4 :: "tail".toList.map fun c ↦ leaf c.toNat))

-- a clash with a visible name, an import of no module and an export of nothing are rejected
#guard diagnose ("(module A (export f) (def f (lam ((x T)) x)))" ++
    " (import A) (def f (lam ((x T)) x))").toList = some "f is reserved or declared before"
#guard diagnose "(def x (lam ((y T)) y)) (module M (def x (lam ((y T)) y)))".toList =
  some "x is reserved or declared before"
#guard diagnose "(import Nowhere)".toList = some "the module Nowhere is not declared"
#guard diagnose "(module M (export ghost))".toList = some "the export ghost names nothing"
#guard diagnose "(def module (lam ((x T)) x))".toList =
  some "module is reserved or declared before"

/-- Sequential bindings and guarded clauses, paired with their nested forms. The bindings
exercise shadowing of a visible definition, dependence on preceding bindings, and type names
qualified by their module. -/
def chainPairs : List (String × String) :=
  [("(def main (lam ((t T)) (let* () t)))", "(def main (lam ((t T)) t))"),
    ("(def main (lam ((t T)) (cond (else t))))", "(def main (lam ((t T)) t))"),
    ("(def main (lam ((t T)) (cond ((eq t 0) 7) ((eq t 1) 8) (else 9))))",
      "(def main (lam ((t T)) (if (eq t 0) 7 (if (eq t 1) 8 9))))"),
    ("(module M (export f) (deftype A T) (def x 4)" ++
        " (def f (lam ((t A)) (let* ((x A (add x t)) (y A x) (x A (add y 1))) x))))" ++
        " (def main M.f)",
      "(module M (export f) (deftype A T) (def x 4)" ++
        " (def f (lam ((t A)) (let x A (add x t) (let y A x (let x A (add y 1) x))))))" ++
        " (def main M.f)"),
    ("(def main (lam ((t T)) (let* ((x T (cond (t 2) (else 3))))" ++
        " (cond ((let* ((y T x)) (eq y 2)) (let* ((z T 4)) z)) (else x)))))",
      "(def main (lam ((t T)) (let x T (if t 2 3)" ++
        " (if (let y T x (eq y 2)) (let z T 4 z) x))))"),
    ("(module M (parameter A) (parameter (f (A) A)) (export g)" ++
        " (def g (lam ((x A)) (let* ((y A (f x)) (z A (f y))) z))))" ++
        " (import (M T (lam ((x T)) (add x 1)))) (def main g)",
      "(module M (parameter A) (parameter (f (A) A)) (export g)" ++
        " (def g (lam ((x A)) (let y A (f x) (let z A (f y) z)))))" ++
        " (import (M T (lam ((x T)) (add x 1)))) (def main g)")]

-- the complete checked kernel bundles agree, including their variable indices and global references
#guard chainPairs.all fun (p, q) ↦
  let a := readProgram p.toList
  a.isSome && a == readProgram q.toList && (a.bind fun ds ↦ load (ds.map Prod.snd)).isSome

-- the guards select the first true branch, with the final else used when none is true
#guard [0, 1, 2].all fun n ↦
  runMain "(def main (lam ((t T)) (cond ((eq t 0) 7) ((eq t 1) 8) (else 9))))".toList
    (leaf n) == some (leaf (n + 7))
#guard runMain "(def main (lam ((t T)) (cond (1 7) (1 8) (else 9))))".toList
  (leaf 0) == some (leaf 7)

/-- Malformed chains and ill-scoped or ill-typed bindings, rejected as programs. A local
function taking a keyword's name cannot make a malformed chain an ordinary application. -/
def badChains : List String :=
  ["(let*)", "(let* () 0 1)", "(let* x 0)", "(let* (x) 0)", "(let* ((x T)) 0)",
    "(let* ((x T 1 2)) x)", "(let* (((x) T 1)) 0)", "(let* ((x T x)) x)",
    "(let* ((x T y) (y T 1)) x)", "(let* ((x Unit 0)) x)",
    "(cond)", "(cond (1 2))", "(cond (else))", "(cond (else 1 2))",
    "(cond (else 1) (else 2))", "(cond (else 1) (1 2))", "(cond (1 2 3) (else 4))",
    "(cond (1 unit) (else 0))", "(let cond (Arrow T T) (lam ((x T)) x) (cond 1))",
    "(let let* (Arrow T T) (lam ((x T)) x) (let* 1))",
    "(nil (cond (else T)))", "(nil (let* () T))"]

#guard badChains.all fun b ↦
  let p := ("(def main (lam ((t T)) " ++ b ++ "))").toList
  (readSExps p).isSome && (diagnose p).isSome

-- declarations and constructors cannot take the new keywords
#guard ["let*", "cond"].all fun k ↦
  [s!"(def {k} 0)", s!"(deftype {k} T)", s!"(defnum {k} 0)",
    s!"(defn {k} ((x T)) T x)", s!"(data D ({k}))"].all fun p ↦
      ((readSExps p.toList).bind expandModules).isNone

/-- Forms in quotations, datums and hole names are preserved by module elaboration. -/
def quotedChains : String :=
  "(def q (quote (let* ((x T 1)) (cond (else x)))))" ++
    " (def d (datum D (cond (else (let* () 1))))) (def h (hole cond))"

#guard (readSExps quotedChains.toList).isSome &&
  ((readSExps quotedChains.toList).bind expandModules).map (·.map canonOf) ==
    (readSExps quotedChains.toList).map (·.map canonOf)

/-- An S-expression as the Geb reader represents it: an atom the node of label 1 over its
characters' codes, a list the node of label 2 over its elements. -/
def sexpTree : SExp → Tree :=
  RoseTree.elim fun a rs ↦
    match a with
    | some s => mk 1 (s.map fun c ↦ leaf c.toNat)
    | none => mk 2 rs

/-- The elaboration of modules written in Geb, applied to a text's S-expressions: the node of
label 1 over the node of the elaborated forms, or the leaf 0. -/
def elaborator : String :=
  compiler ++ "(import Prelude) (import Reader) (import Modules) " ++
    "(def modulesMain (lam ((file T)) (let sx T (readSExps (children file)) " ++
    "(if (isSome sx) (expandModules (children (get sx))) none))))"

/-- What the elaboration written in Geb gives for a text, computed in Lean. -/
def expectedModules (text : List Char) : Tree :=
  match (readSExps text).bind expandModules with
  | some fs => mk 1 [mk 0 (fs.map sexpTree)]
  | none => leaf 0

/-- The texts the elaboration is compared on: each example above, and failures. -/
def moduleTexts : List String :=
  chainPairs.flatMap (fun (p, q) ↦ [p, q]) ++
    badChains.map (fun b ↦ "(def main (lam ((t T)) " ++ b ++ "))") ++
    [quotedChains, "(def let* 0)", "(def cond 0)",
    arith ++ " (def main (lam ((t T)) (Arith.double 3)))",
    "(def x (lam ((t T)) (quote (0 \"…\"))))",
    arith ++ " (def main (lam ((t T)) (Arith.twice 3)))",
    "(module A (export f) (def f (lam ((x T)) (add x 1))))" ++
      " (module B (import A) (export g) (def g (lam ((x T)) (f (f x)))))",
    "(module A (export f) (def f (lam ((x T)) (add x 1)))) (import A as N)",
    "(module Outer (export Inner.y z) (module Inner (export y) (def y (lam ((x T)) x))))",
    twice ++ " (module Use (import (Twice T inc)) (export run) (def run (lam ((x T)) (twice x))))",
    twice ++ " (import (Twice T))",
    "(module M (export h q) (def tail (lam ((x T)) x)) (def h (lam ((tail T)) tail))" ++
      " (def q (lam ((x T)) (quote (0 tail)))))",
    "(module D (export Maybe nothing just get) (data Maybe (nothing) (just T))" ++
      " (defn get ((d T) (m Maybe)) T (case m ((nothing) d) ((just x) x))))",
    "(module N (export Nat isNat two) (data Nat (zero) (succ Nat)) (tree-data Old (old T))" ++
      " (def tail 0) (def two (datum Nat (1 (1 (0)))))" ++
      " (def isNat (lam ((t T)) (decode Nat t (lam ((n Nat)) (rep n)) (datum Nat (0 tail))))))",
    "(module Box (parameter A) (parameter (f (A A) A)) (export box) (data Box (box A))" ++
      " (def g (lam ((b Box)) (case b ((box x) (f x x))))))",
    "(def x 1) (module M (def x 2))", "(import Nowhere)", "(module M (export ghost))"]

-- the elaboration written in Geb agrees with Lean's
#guard moduleTexts.all fun text ↦
  runMain elaborator.toList (mk 0 (text.toList.map fun c ↦ leaf c.toNat)) ==
    some (expectedModules text.toList)

-- a module of the datatype language, compiled by the stage-0 compiler
#guard runDatatype compiler.toList ("(module Opt (export Maybe nothing just fromMaybe)" ++
    " (data Maybe (nothing) (just T))" ++
    " (defn fromMaybe ((d T) (m Maybe)) T" ++
    " (let* ((fallback T (cond ((eq d 0) 7) (else d))))" ++
    " (case m ((nothing) fallback) ((just x) (cond (1 x) (else fallback)))))))" ++
    " (defn main ((t T)) T (Opt.fromMaybe 7 (Opt.just 3)))").toList (leaf 0) = some (leaf 3)

-- a datatype of a module decoded, its name qualified in the recognizer the decoding refers to
#guard [(leaf 0, leaf 1), (mk 1 [leaf 0], leaf 1), (mk 2 [], leaf 0)].all fun (t, r) ↦
  runDatatype compiler.toList ("(module N (export Nat zero succ isNat)" ++
    " (data Nat (zero) (succ Nat)) (def isNat (lam ((t T)) (decode Nat t (lam ((n Nat)) 1) 0))))" ++
    " (def main (lam ((t T)) (N.isNat t)))").toList t == some r

/-- Two modules, the first exporting one of its definitions. -/
def twoModules (m f g n h : String) (k : ℕ) : String :=
  s!"(module {m} (export {f}) (def {g} (lam ((x T)) x)) (def {f} (lam ((y T)) ({g} y))))" ++
    s!" (module {n} (export {h}) (def {h} (lam ((x T)) (add x {k}))))"

open Identity in
-- renaming modules and their members changes no identifier
#guard (programModules (twoModules "M" "f" "g" "N" "h" 1).toList).isSome &&
  ((programModules (twoModules "M" "f" "g" "N" "h" 1).toList).map (·.map Prod.snd)) ==
    ((programModules (twoModules "Q" "e" "k" "P" "u" 1).toList).map (·.map Prod.snd))
open Identity in
-- a changed definition changes its module's identifier and the root's, and no other module's
#guard ((programModules (twoModules "M" "f" "g" "N" "h" 1).toList).bind fun xs ↦
    (programModules (twoModules "M" "f" "g" "N" "h" 2).toList).map fun ys ↦
      (xs.zip ys).map fun (x, y) ↦ x.2 == y.2) = some [true, false, false]

/-- The identifiers of a text's modules computed in Geb: its modules elaborated, its forms read
into a bundle, its definitions migrated, and its tree of modules identified. -/
def moduleIdentifier : String :=
  Identity.Tests.withIdentity <|
    "(def modulesMain (lam ((file T)) (let sx T (readSExps (children file)) " ++
    "(if (isSome sx) (let r T (expandModulesTree (children (get sx))) " ++
    "(if (isSome r) (let b T (readProgram (children (child (get r) 0))) " ++
    "(if (isSome b) (let cids Ts (cidsOf (migrate (children (child (get b) 0)))) " ++
    "(some (node 0 (moduleCids (zipWith2 (lam ((n T) (c T)) (node2 0 n c)) " ++
    "(children (child (get b) 1)) cids) (children (child (get r) 1)))))) none)) none)) none))))"

open Identity in
-- the identifiers of modules computed in Geb agree with Lean's
#guard [twoModules "M" "f" "g" "N" "h" 1, twoModules "M" "f" "g" "N" "h" 2,
    "(module A (export f) (module B (export g) (def g (lam ((x T)) x))) (def f B.g))"].all
  fun text ↦
  runMain moduleIdentifier.toList (mk 0 (text.toList.map fun c ↦ leaf c.toNat)) ==
    some (match programModules text.toList with
      | some ms => mk 1 [mk 0 (ms.map fun (p, c) ↦ mk 0 [mk 0 (p.map fun ch ↦ leaf ch.toNat),
          Identity.Tests.bytesTree c])]
      | none => leaf 0)

end Geb.Kernel.ModulesTests

end
