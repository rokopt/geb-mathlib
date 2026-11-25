/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Kernel.Identity
import Geb.Prototypes.Kernel.Image

/-!
# The definitions of an image

`lake exe geb-defs IMAGE OUT` writes the definitions of the bundle an image stores, one per
line: the definition's name, a tab, and its kernel term as an S-expression of labels, a node
written as its label followed by its children. `scripts/eal/eal.py` reads this form.
`lake exe geb-defs --identities IMAGE OUT` writes in place of each term the definition's content
identifier, its CID in the multibase base16 form of a CIDv1: the letter `f` followed by the CID's
bytes in lowercase hexadecimal. A definition refers to another by its position in the bundle, and
its identifier to another by that one's identifier (`Geb.Kernel.Identity`), so that a definition
inserted before others changes their terms and not their identifiers.

## Main definitions

* `main`: write an image's definitions or their identifiers.

## Tags

bootstrap, kernel, image, command line
-/

/-- A tree as an S-expression of labels: a node is its label followed by its children. -/
def sexpr : Geb.Kernel.Tree → String :=
  Geb.RoseTree.elim fun l rs ↦ "(" ++ toString l ++ String.join (rs.map (" " ++ ·)) ++ ")"

/-- A byte as two lowercase hexadecimal digits. -/
def hexByte (b : UInt8) : String :=
  String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]

/-- A CID in the multibase base16 form: `f` followed by its bytes in lowercase hexadecimal. -/
def base16 (cid : List UInt8) : String := "f" ++ String.join (cid.map hexByte)

/-- Write a line for each definition of the bundle an image stores: its name, a tab, and the
text that `text` gives it. -/
def write (img out : String) (text : List (List Char × Geb.Kernel.Tree) → List String) :
    IO UInt32 := do
  let some t := Geb.Kernel.readImage (← IO.FS.readBinFile img)
    | IO.eprintln s!"geb-defs: {img} is not an image"; return 1
  let some ds := Geb.Kernel.unbundle t
    | IO.eprintln s!"geb-defs: {img} stores no bundle"; return 1
  IO.FS.writeFile out <| String.join <| (ds.zip (text ds)).map fun ((n, _), x) ↦
    String.ofList n ++ "\t" ++ x ++ "\n"
  return 0

/-- Write the definitions of the bundle an image stores, or their identifiers, one per line. -/
public def main : List String → IO UInt32
  | [img, out] => write img out fun ds ↦ ds.map (sexpr ·.2)
  | ["--identities", img, out] =>
    write img out fun ds ↦ (Geb.Kernel.Identity.migrate (ds.map Prod.snd)).map (base16 ·.cid)
  | _ => do
    IO.eprintln "usage: geb-defs [--identities] IMAGE OUT"
    return 2
