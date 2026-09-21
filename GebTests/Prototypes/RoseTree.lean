/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.RoseTree  -- shake: keep; #guard needs it
public meta import Geb.Prototypes.RoseTree  -- shake: keep; #guard needs it

/-!
# Tests for the rose-tree representations

The word-level serialization `Geb.Packed.encode` is tested against the list
form `Geb.RoseTree.wire` it is stated to agree with, its recognizer against
`Geb.BitTree.Elias.validBool` on every word of a small length, and its decoder
on the round trip, since none of the three is proved.

## Main definitions

* `sample`, `deep`, `wide`, `long` — trees of the shapes the serialization
  distinguishes: a small mixed tree, a chain, a node of many children, and
  labels beyond one machine word.
* `bitsOf` — the bits of a number below a length, the words the recognizers
  are compared on.
-/

public section

open Geb Geb.RoseTree Geb.Packed Geb.Oitavem

/-- A small tree of mixed arities and short labels. -/
def sample : RoseTree ℕ :=
  node (rank [true, false, true]) [node 5 [], node 0 [node 12 [], node 3 []]]

/-- A chain. -/
def deep : RoseTree ℕ := node 1 [node 2 [node 3 [node 4 [node 5 []]]]]

/-- A node of many children. -/
def wide : RoseTree ℕ := node 7 ((List.range 70).map fun i ↦ node i [])

/-- Labels longer than one machine word. -/
def long : RoseTree ℕ := node (2 ^ 100 + 12345) [node (2 ^ 70) [], node (2 ^ 64 - 1) [], sample]

/-- The bits of a number below a length, least significant first. -/
def bitsOf (n k : ℕ) : List Bool := (List.range k).map fun i ↦ n.testBit i

-- The word-level serialization agrees with the list form.
#guard (Packed.encode sample).toList = wire sample
#guard (Packed.encode deep).toList = wire deep
#guard (Packed.encode wide).toList = wire wide
#guard (Packed.encode long).toList = wire long
#guard (Packed.encode (node 0 [])).toList = wire (node 0 [])

-- The buffer round-trips a list.
#guard (Buf.ofList (wire long)).toList = wire long

-- The word-level decoder inverts the serialization.
#guard (Packed.decode (Packed.encode sample)).map wire = some (wire sample)
#guard (Packed.decode (Packed.encode deep)).map wire = some (wire deep)
#guard (Packed.decode (Packed.encode wide)).map wire = some (wire wide)
#guard (Packed.decode (Packed.encode long)).map wire = some (wire long)
#guard (Packed.decode (Packed.encode (node 0 []))).map wire = some (wire (node 0 []))

-- The word-level recognizer accepts serialized trees and rejects a trailing
-- bit, a truncation, and the empty word.
#guard Packed.recognize (Packed.encode long) = true
#guard Packed.recognize (Buf.ofList (wire sample ++ [true])) = false
#guard Packed.recognize (Buf.ofList (wire sample).dropLast) = false
#guard Packed.recognize Buf.empty = false

-- The word-level recognizer agrees with the list recognizer on every word of
-- length at most ten.
#guard (List.range 11).all fun k ↦ (List.range (2 ^ k)).all fun n ↦
  Packed.recognize (Buf.ofList (bitsOf n k)) == Geb.BitTree.Elias.validBool (bitsOf n k)

end
