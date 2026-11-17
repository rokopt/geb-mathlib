/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Chains -- shake: keep
public meta import Geb.Prototypes.Kernel.Chains -- shake: keep

set_option doc.verso true in
/-!
# Examples of the conversion of chains

A text of nested bindings and tests is converted and formatted to a pinned text: a sequence of
{lit}`let` forms is one {lit}`let*`, a sequence of conditionals one {lit}`cond`, and each
comment line precedes the binding or the clause that the form after it became. A {lit}`let*` or
a {lit}`cond` already written is joined with the forms nested in its body or its default. The
conversion is idempotent, keeps every comment line in order, and gives a program whose modules
elaborate to the declarations of the original's, in each role the elaboration gives a term. A
form in any other role is unchanged: a quoted datum, a datum, the name of a hole, a type, a
pattern, the argument of an import, a note, and a form of a document that is no program; so is
a single binding or test, a test named {lit}`else`, a binding of no name, and a conditional
before a malformed {lit}`cond`.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`.

## Main definitions

* {lit}`nested` is a module of nested bindings and tests with comments, and
  {lit}`nestedConverted` its converted text.
* {lit}`joined` pairs texts with their conversions, and {lit}`unchanged` are texts the
  conversion leaves as they are.

## Tags

S-expression, source conversion, sequential binding, conditional, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document.ChainsTests

/-- A module of nested bindings and tests, with comment lines before a nested binding, a nested
test and a default. -/
def nested : String := "; a header
(module M
  (export f g)
  (def f
    (lam ((t T))
      ; the bindings
      (let x T (add t 1)
        ; the second
        (let y T (add x 1)
          (if (eq y 0) 7
            ; the next test
            (if (eq y 1) 8
              ; neither
              9))))))
  (defn g ((t T)) T (if t 1 (if (eq t 2) 3 (if (eq t 4) 5 6)))))
"

/-- The converted text of {name}`nested`. -/
def nestedConverted : String := "; a header
(module M (export f g)
  (def f
    (lam ((t T))
      ; the bindings
      (let*
        ((x T (add t 1))
         ; the second
         (y T (add x 1)))
        (cond ((eq y 0) 7)
          ; the next test
          ((eq y 1) 8)
          ; neither
          (else 9)))))
  (defn g ((t T)) T (cond (t 1) ((eq t 2) 3) ((eq t 4) 5) (else 6))))
"

/-- Texts paired with their conversions: forms already written as chains joined with those
nested in them, and nested forms in a clause of a case analysis, in the arguments of the folds
and of {lit}`decode`, in a module nested in another and in a module with parameters. -/
def joined : List (String × String) :=
  [("(def a (lam ((t T)) (let* ((x T 1)) (let y T 2 (let* ((z T 3) (w T 4)) (add x w))))))",
      "(def a (lam ((t T)) (let* ((x T 1) (y T 2) (z T 3) (w T 4)) (add x w))))"),
    ("(def b (lam ((t T)) (cond ((eq t 0) 1)" ++
        " (else (if (eq t 1) 2 (cond ((eq t 2) 3) (else 4)))))))",
      "(def b (lam ((t T)) (cond ((eq t 0) 1) ((eq t 1) 2) ((eq t 2) 3) (else 4))))"),
    ("(def c (lam ((t T)) (if t 1 (cond ((eq t 2) 3) (else 4)))))",
      "(def c (lam ((t T)) (cond (t 1) ((eq t 2) 3) (else 4))))"),
    ("(def p (lam ((e T)) (case e ((if a b c) (if 1 2 (if 3 4 5))) ((let x A y z) 0))))",
      "(def p (lam ((e T)) (case e ((if a b c) (cond (1 2) (3 4) (else 5))) ((let x A y z) 0))))"),
    ("(def k (lam ((t T)) (fold T (lam ((n T) (rs (List T))) (lcase T T rs (if n 1 (if 2 3 4))" ++
        " (lam ((r T) (xs (List T))) (let a T r (let b T n (foldr T T (lam ((u T) (v T))" ++
        " (if u v (if v u 0))) a xs)))))) t)))",
      "(def k (lam ((t T)) (fold T (lam ((n T) (rs (List T)))" ++
        " (lcase T T rs (cond (n 1) (2 3) (else 4))" ++
        " (lam ((r T) (xs (List T))) (let* ((a T r) (b T n)) (foldr T T (lam ((u T) (v T))" ++
        " (cond (u v) (v u) (else 0))) a xs))))) t)))"),
    ("(def d (lam ((t T)) (decode D (if t 1 (if 2 3 4)))))",
      "(def d (lam ((t T)) (decode D (cond (t 1) (2 3) (else 4)))))"),
    ("(module A (module B (export h) (def h (lam ((t T)) (let x T t (let y T x y))))))",
      "(module A (module B (export h) (def h (lam ((t T)) (let* ((x T t) (y T x)) y)))))"),
    ("(module M (parameter A) (parameter (f (A) A)) (export g)" ++
        " (def g (lam ((x A)) (let y A (f x) (let z A (f y) z)))))" ++
        " (import (M T (lam ((x T)) (add x 1)))) (def main g)",
      "(module M (parameter A) (parameter (f (A) A)) (export g)" ++
        " (def g (lam ((x A)) (let* ((y A (f x)) (z A (f y))) z))))" ++
        " (import (M T (lam ((x T)) (add x 1)))) (def main g)")]

/-- Texts the conversion leaves as they are: nested forms in a quoted datum, a datum, the name
of a hole, the fields of a constructor, a type, a note, the argument of an import and a document
of proofs; a test named {lit}`else`; a conditional before a malformed {lit}`cond`; a binding of
no name; an empty {lit}`let*`; and a single binding and test. -/
def unchanged : List String :=
  ["(def q (quote (if a b (if c d e))))",
    "(def d (datum D (let x T 1 (let y T 2 y))))",
    "(def h (lam ((t T)) (hole (if a b (if c d e)))))",
    "(data E (if E E E) (let E E E E))",
    "(def n (lam ((t T)) (nil (if a b (if c d e)))))",
    "(note (example (if a b (if c d e)) 0))",
    "(import (M T (lam ((x T)) (if x 1 (if 2 3 4)))))",
    "(proofs 1 (theorem t (equal (if a b (if c d e)) f) (by (normalize 1))))",
    "(def s (lam ((else T)) (if else 1 (if 2 3 4))))",
    "(def m (lam ((t T)) (if 1 2 (cond (3 4)))))",
    "(def n (lam ((t T)) (let (x) T 1 (let y T 2 y))))",
    "(def o (lam ((t T)) (let x T 1 (let* () t))))",
    "(def single (lam ((t T)) (let x T 1 (if t x 2))))"]

/-- The comment lines of a text, in order. -/
def commentsOf (convert : Bool) (text : List Char) : Option (List (List Char)) :=
  (readDoc text).map fun d ↦
    (if convert then d.chains else d).tokens.filterMap fun
      | .comment _ s => some s
      | _ => none

#guard formatChains 100 nested.toList = some nestedConverted.toList

-- the conversion is idempotent
#guard formatChains 100 nestedConverted.toList = some nestedConverted.toList
#guard joined.all fun (_, q) ↦ formatChains 100 q.toList = format 100 q.toList

-- every comment line is kept, in order, as is one before a list's end
#guard commentsOf true nested.toList = commentsOf false nested.toList
#guard formatChains 100 "(def f (lam ((t T)) (if t 1 (if 2 3 4\n ; last\n ))))".toList =
  some "(def f\n  (lam ((t T))\n    (cond (t 1) (2 3) (else 4)\n      ; last\n      )))\n".toList

-- forms already written as chains are joined with those nested in them, in each role of a term
#guard joined.all fun (p, q) ↦ formatChains 100 p.toList = format 100 q.toList

-- the modules of a converted program elaborate to the declarations of the original's
#guard (nested :: joined.map Prod.fst).all fun p ↦
  let a := (readSExps p.toList).bind expandModules
  a.isSome && ((formatChains 100 p.toList).bind readSExps).bind expandModules == a

-- a form in a role that is no term is unchanged, as are a single binding and a single test
#guard unchanged.all fun p ↦ formatChains 100 p.toList = format 100 p.toList

end Geb.Kernel.Document.ChainsTests

end
