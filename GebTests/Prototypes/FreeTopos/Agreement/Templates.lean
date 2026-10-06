/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic
public import Mathlib.CategoryTheory.Category.Init

set_option doc.verso true in
/-!
# The instances of the datatype language's templates in the mirror

A module with parameters of the datatype language ({lit}`bootstrap/seq.geb`,
{lit}`bootstrap/free-topos/base.geb`) is instantiated at each import, each instance a copy of the
template's definitions, which the bootstrap compiler emits in Lean under the instance's name. At a
datatype, which erases to the trees, the copies of a definition are one Lean function. This module
states each such function once; the command {lit}`template_equations`
({lit}`GebTests.Prototypes.FreeTopos.Agreement.TemplateEquations`) equates every copy with it.

## Main definitions

* {lit}`single`, {lit}`length`, {lit}`append`, {lit}`reverse`, {lit}`tail`, {lit}`drop`,
  {lit}`atOr` — the template {lit}`Seq`.
* {lit}`nothing`, {lit}`just`, {lit}`isJust`, {lit}`fromMaybe`, {lit}`nthOf`, {lit}`allJust` — the
  template {lit}`Option`.
* {lit}`all`, {lit}`any`, {lit}`isEmpty`, {lit}`take`, {lit}`map`, {lit}`l2` to {lit}`l6` — the
  templates {lit}`Each`, {lit}`Map` and {lit}`Few`.
* {lit}`res`, {lit}`bad`, {lit}`ok`, {lit}`pure`, {lit}`fail`, {lit}`orElse` — the template
  {lit}`Comp` of {lit}`bootstrap/free-topos/combinator.geb`.

## Tags

template, module, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Templates

open Geb Geb.Kernel GebMirror.Metalogic

/-- A list of one tree. -/
def single (x : Tree) : List Tree := [x]

/-- The length of a list, as a label. -/
def length (xs : List Tree) : Tree := Const.foldr (fun _ n ↦ Const.add n (leaf 1)) (leaf 0) xs

/-- The concatenation of two lists. -/
def append (xs ys : List Tree) : List Tree := Const.foldr (fun x r ↦ x :: r) ys xs

/-- The reversal of a list. -/
def reverse (xs : List Tree) : List Tree :=
  Const.foldr (fun x (k : List Tree → List Tree) acc ↦ k (x :: acc)) (fun acc ↦ acc) xs []

/-- The tail of a list. -/
def tail (xs : List Tree) : List Tree := Const.lcase xs [] fun _ r ↦ r

/-- A list without its first elements. -/
def drop (n : Tree) (xs : List Tree) : List Tree := Const.iter tail xs n

/-- The element of a list at a position, or a default. -/
def atOr (d : Tree) (xs : List Tree) (i : Tree) : Tree := Const.lcase (drop i xs) d fun x _ ↦ x

/-- The absent optional value. -/
def nothing : Tree := Const.node (leaf 0) []

/-- A present optional value. -/
def just (x : Tree) : Tree := Const.node (leaf 1) [x]

/-- Whether an optional value is present. -/
def isJust (m : Tree) : Tree :=
  if (Const.eq (Const.label m) (leaf 1)).label ≠ 0 then leaf 1 else leaf 0

/-- An optional value's value, or a default. -/
def fromMaybe (d m : Tree) : Tree :=
  if (Const.eq (Const.label m) (leaf 1)).label ≠ 0 then Const.child m (leaf 0) else d

/-- The element of a list at a position, when the list is longer. -/
def nthOf (xs : List Tree) (i : Tree) : Tree :=
  Const.lcase (Const.iter (fun ys ↦ Const.lcase ys [] fun _ r ↦ r) xs i) nothing fun x _ ↦ just x

/-- Whether every optional value of a list is present, and the present values. -/
def allJust (ms : List Tree) : Tree × List Tree :=
  Const.foldr
    (fun m acc ↦
      if (Const.eq (Const.label m) (leaf 1)).label ≠ 0 then (acc.1, Const.child m (leaf 0) :: acc.2)
      else (leaf 0, acc.2))
    (leaf 1, []) ms

/-- Whether a test holds of every element of a list. -/
def all (f : Tree → Tree) (xs : List Tree) : Tree :=
  Const.foldr (fun x r ↦ «Prelude.and» (f x) r) (leaf 1) xs

/-- Whether a test holds of some element of a list. -/
def any (f : Tree → Tree) (xs : List Tree) : Tree :=
  Const.foldr (fun x r ↦ «Prelude.or» (f x) r) (leaf 0) xs

/-- Whether a list is empty. -/
def isEmpty (xs : List Tree) : Tree := Const.eq (length xs) (leaf 0)

/-- The first elements of a list. -/
def take (n : Tree) (xs : List Tree) : List Tree :=
  (Const.foldr
    (fun x (s : Tree × List Tree) ↦
      (Const.add s.1 (leaf 1),
        if (Const.lt (Const.sub (Const.sub (length xs) s.1) (leaf 1)) n).label ≠ 0 then x :: s.2
        else s.2))
    (leaf 0, []) xs).2

/-- The image of a list under a function. -/
def map (f : Tree → Tree) (xs : List Tree) : List Tree := Const.foldr (fun x r ↦ f x :: r) [] xs

/-- A list of two trees. -/
def l2 (a b : Tree) : List Tree := [a, b]

/-- A list of three trees. -/
def l3 (a b c : Tree) : List Tree := a :: l2 b c

/-- A list of four trees. -/
def l4 (a b c d : Tree) : List Tree := a :: l3 b c d

/-- A list of five trees. -/
def l5 (a b c d e : Tree) : List Tree := a :: l4 b c d e

/-- A list of six trees. -/
def l6 (a b c d e f : Tree) : List Tree := a :: l5 b c d e f

/-- A computation's result: its value and the state after it. -/
def res (v st : Tree) : Tree := Const.node (leaf 0) [v, st]

/-- The outcome of a computation that fails. -/
def bad : Tree := Const.node (leaf 0) []

/-- The outcome of a computation that succeeds with a result. -/
def ok (r : Tree) : Tree := Const.node (leaf 1) [r]

/-- The computation of a value. -/
def pure (v : Tree) : Tree → Tree → Tree := fun _ st ↦ ok (res v st)

/-- The computation that fails. -/
def fail (_ _ : Tree) : Tree := bad

/-- The first of two computations that succeeds. -/
def orElse (a b : Tree → Tree → Tree) : Tree → Tree → Tree := fun sc st ↦
  if (Const.eq (Const.label (a sc st)) (leaf 1)).label ≠ 0 then a sc st else b sc st

end GebTests.Prototypes.FreeTopos.Agreement.Templates

end
