/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.Triage -- shake: keep; #guard needs it

set_option doc.verso true in
/-!
# Executable triage checks

The tests cover every absorption and triage rule, nested evaluation order,
terminal values, malformed words, and binary trees violating the value grammar.
-/

set_option doc.verso true

open Geb.Triage
open Expr

public section

/-- Compare the bitstring interface with one expected successor expression. -/
def checkRoot (f x : Value) (expected : Expr) : Bool :=
  reduce (app (value f) (value x)).encodeFast == .next expected.encodeFast

#guard checkRoot Value.leaf Value.leaf (value (Value.stem Value.leaf))
#guard checkRoot (Value.stem Value.leaf) Value.leaf
  (value (Value.fork Value.leaf Value.leaf))
#guard checkRoot (Value.fork Value.leaf (Value.stem Value.leaf)) Value.leaf
  (value (Value.stem Value.leaf))
#guard checkRoot (Value.fork (Value.stem Value.leaf) Value.leaf) Value.leaf
  (app (app (value Value.leaf) (value Value.leaf)) (app (value Value.leaf) (value Value.leaf)))
#guard checkRoot (Value.fork (Value.fork (Value.stem Value.leaf) Value.leaf) Value.leaf)
  Value.leaf (value (Value.stem Value.leaf))
#guard checkRoot (Value.fork (Value.fork Value.leaf (Value.stem Value.leaf)) Value.leaf)
  (Value.stem Value.leaf) (app (value (Value.stem Value.leaf)) (value Value.leaf))
#guard checkRoot (Value.fork (Value.fork Value.leaf Value.leaf) (Value.stem Value.leaf))
  (Value.fork Value.leaf (Value.stem Value.leaf))
  (app (app (value (Value.stem Value.leaf)) (value Value.leaf)) (value (Value.stem Value.leaf)))

#guard reduce (app (app (value Value.leaf) (value Value.leaf))
  (app (value Value.leaf) (value Value.leaf))).encodeFast ==
  .next (app (app (value Value.leaf) (value Value.leaf)) (value (Value.stem Value.leaf))).encodeFast
#guard reduce (value (Value.fork (Value.stem Value.leaf) Value.leaf)).encodeFast == .value
#guard reduce [] == .invalid
#guard reduce [false, false, false] == .invalid

/-- A valid binary tree whose stem child is an application, violating the triage grammar. -/
def applicationUnderStem : List Bool := Geb.BitTree.encode
  (Geb.BitTree.fork (Geb.BitTree.leaf [false]) (app (value Value.leaf) (value Value.leaf)).toTree)

#guard Geb.BitTree.validBool applicationUnderStem && !recognize applicationUnderStem
#guard reduce applicationUnderStem == .invalid
#guard !recognize (Geb.BitTree.encode (Geb.BitTree.leaf [true, true]))
