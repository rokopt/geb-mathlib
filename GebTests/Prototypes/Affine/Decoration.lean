/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Affine.Decoration -- shake: keep
public meta import Geb.Prototypes.Affine.Decoration -- shake: keep
public import Geb.Prototypes.Kernel.Reader -- shake: keep
public meta import Geb.Prototypes.Kernel.Reader -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The check of elementary-affine certificates

The checker {name}`Geb.Affine.check` against the certificate that {lit}`scripts/eal/eal.py`
writes for the definitions of {lit}`scripts/eal/examples.defs`: the certificate checks, with
an instance of exactly the definitions the search finds typable with a decoration per use,
{lit}`unzipR` among them at two decorations; it does not check with its instances in the
reverse order, where an instance refers to one after it; and the instance of {lit}`twice`
alone checks, and does not with no {lit}`!` on its argument, which it contracts.

The files are read at elaboration by {lit}`include_str` and converted to lists of characters
inside each {lit}`#guard`: core's {lit}`String.toList` depends on {lit}`Classical.choice`,
and a {lit}`#guard` is not a declaration.

## Main definitions

* {lit}`examples` and {lit}`examplesCert` are the files.
* {lit}`program` reads a program's definitions in the form of {lit}`examples`, and
  {lit}`certificate` a certificate.
* {lit}`twice` is the instance of {lit}`twice` as a certificate of its own, and
  {lit}`twiceLinear` the same with no {lit}`!` on its argument.

## Tags

elementary affine logic, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Affine.DecorationTests

open Geb.Kernel
open scoped FinEnum

/-- The definitions of the search's examples. -/
def examples : String := include_str "../../../scripts/eal/examples.defs"

/-- The certificate the search writes for them. -/
def examplesCert : String := include_str "../../../scripts/eal/examples.cert"

/-- A program's definitions, one per line as a name, a tab and the term as an S-expression
of labels, lines that are empty or begin with {lit}`#` skipped. -/
def program (text : List Char) : Option (List Tree) :=
  ((text.splitOn '\n').filter fun l ↦ !l.isEmpty && l.head? != some '#').mapM fun l ↦ do
    let [e] ← readSExps ((l.dropWhile (· != '\t')).drop 1) | none
    readDatum e

/-- A certificate, one S-expression of labels. -/
def certificate (text : List Char) : Option Tree := do
  let [e] ← readSExps text | none
  readDatum e

/-- The instance of {lit}`twice` in the examples' certificate, as a certificate of its own.
-/
def twice : String := "(0 (7 (0 (1 (0) (0)) (0 (0) (1 (1) (1 (1) (0)))))))"

/-- The same with no {lit}`!` on the argument that {lit}`twice` applies twice. -/
def twiceLinear : String := "(0 (7 (0 (0 (0) (0)) (0 (0) (1 (1) (1 (1) (0)))))))"

#guard (do
  let prog ← program examples.toList
  let cert ← certificate examplesCert.toList
  let E ← check prog cert
  some (E.map Prod.fst)) ==
    some [0, 1, 2, 3, 5, 5, 6, 7, 8, 10, 11, 14, 15, 16]

#guard (do
  let prog ← program examples.toList
  let cert ← certificate examplesCert.toList
  some (check prog (RoseTree.node cert.label cert.children.reverse)).isNone) == some true

#guard (do
  let prog ← program examples.toList
  some ((check prog (← certificate twice.toList)).isSome,
    (check prog (← certificate twiceLinear.toList)).isSome)) == some (true, false)

end Geb.Affine.DecorationTests
