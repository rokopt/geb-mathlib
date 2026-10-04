/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Printer -- shake: keep
public meta import Geb.Prototypes.Kernel.Printer -- shake: keep
public import Geb.Prototypes.Kernel.Strict -- shake: keep
public meta import Geb.Prototypes.Kernel.Strict -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# Printer examples

A variable is printed as its binder's name, an abstraction with one binder and its type written
structurally, and a reference by the name of the definition it refers to. The definitions of the
stage-0 compiler are well formed, and printed they read back to themselves, also through their
canonical encoding. A variable that no binder binds is not well formed.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`.

## Tags

printer, reader, retraction, test
-/

set_option doc.verso true

set_option linter.privateModule false

@[expose] public section

namespace Geb.Kernel.PrinterTests

open Geb.Kernel.Stage0Tests
open scoped FinEnum

-- binders are named by their depth, references by the definitions' names, and an application
-- of several arguments is written as applications of one
#guard (readProgram ("(def double (lam ((x T)) (add x x)))" ++
    " (def quad (lam ((x T) (y (List T))) (double (double x))))").toList).map printProgram =
  readSExps ("(def double (lam (_0 T) ((add _0) _0)))" ++
    " (def quad (lam (_0 T) (lam (_1 (List T)) (double (double _0)))))").toList

-- a quoted leaf is printed as its numeral, another quoted tree as a datum
#guard (readProgram "(def k (lam ((t T)) (pair 7 (quote (1 2 (3 4))))))".toList).map
    printProgram =
  readSExps "(def k (lam (_0 T) (pair 7 (quote (1 2 (3 4))))))".toList

-- the stage-0 compiler's definitions are well formed
#guard (readProgram compiler.toList).all fun ds ↦ ds.zipIdx.all fun (d, i) ↦ TermWf i d.2 0

-- printed, they read back to themselves
#guard (readProgram compiler.toList).bind (fun ds ↦ readForms (printProgram ds)) =
  readProgram compiler.toList

-- and through their canonical encoding
#guard (readProgram compiler.toList).bind
    (fun ds ↦ (readSExps ((printProgram ds).flatMap Document.canonOf)).bind readForms) =
  readProgram compiler.toList

-- a variable that no binder binds is not well formed
#guard !TermWf 0 (mk Label.var [leaf 0]) 0

end Geb.Kernel.PrinterTests

end
