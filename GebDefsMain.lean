/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Image

/-!
# The definitions of an image

`lake exe geb-defs IMAGE OUT` writes the definitions of the bundle an image stores, one per
line: the definition's name, a tab, and its kernel term as an S-expression of labels, a node
written as its label followed by its children. `scripts/eal/eal.py` reads this form.

## Main definitions

* `main`: write an image's definitions.

## Tags

bootstrap, kernel, image, command line
-/

/-- A tree as an S-expression of labels: a node is its label followed by its children. -/
def sexpr : Geb.Kernel.Tree → String :=
  Geb.RoseTree.elim fun l rs ↦ "(" ++ toString l ++ String.join (rs.map (" " ++ ·)) ++ ")"

/-- Write the definitions of the bundle an image stores, one per line. -/
public def main : List String → IO UInt32
  | [img, out] => do
    let some t := Geb.Kernel.readImage (← IO.FS.readBinFile img)
      | IO.eprintln s!"geb-defs: {img} is not an image"; return 1
    let some ds := Geb.Kernel.unbundle t
      | IO.eprintln s!"geb-defs: {img} stores no bundle"; return 1
    IO.FS.writeFile out <| String.join <| ds.map fun (n, d) ↦
      String.ofList n ++ "\t" ++ sexpr d ++ "\n"
    return 0
  | _ => do
    IO.eprintln "usage: geb-defs IMAGE OUT"
    return 2
