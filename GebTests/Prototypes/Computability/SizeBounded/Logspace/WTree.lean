/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree -- shake: keep; #guard needs it
public import Geb.Mathlib.Data.FinEnum

/-!
# The W-tree recognizer at the signature of binary trees of bitstrings

The signature with a shape per bitstring, without directions, and one
shape with two directions, over one index: its W-trees are the binary trees
of bitstrings. The recognizer accepts the spellings of a leaf, a fork of
leaves and a fork of forks, and rejects the empty word, a fork spelled with
one child, a leaf spelled with a child, a label that is no code, and a fork
whose label carries a payload.

## Main definitions

* `binSig` — the signature.

## Main statements

The recognizer accepts each spelling and rejects each corruption, by
`#guard`.

## Tags

W-type, binary tree, bitstring, recognizer
-/

set_option linter.privateModule false

open Geb.SizeBounded.Logspace.WTree
open scoped FinEnum

/-- The directions: none at a leaf, two at a fork. -/
def binArity : Option (List Bool) → Type
  | some _ => Fin 0
  | none => Fin 2

/-- Every shape has finitely many directions. -/
@[instance_reducible] def binFinitary : ∀ a, FinEnum (binArity a)
  | some _ => inferInstanceAs (FinEnum (Fin 0))
  | none => inferInstanceAs (FinEnum (Fin 2))

/-- The code: the tag `false` and the bitstring at a leaf, the tag `true` at a
fork. -/
def binCode : Option (List Bool) → List Bool
  | some s => false :: s
  | none => [true]

/-- The decoder. -/
def binDecode : List Bool → Option (Option (List Bool))
  | false :: s => some (some s)
  | [true] => some none
  | _ => none

/-- The signature: a leaf shape per bitstring, with no direction, and a fork
shape with two, every shape and direction over the one index. -/
def binSig : CodedSig Unit where
  P := { A := Option (List Bool), B := binArity, r := fun _ ↦ (), q := fun _ ↦ () }
  finitary := binFinitary
  code := binCode
  decode := binDecode
  decode_code := fun a ↦ match a with | some _ => rfl | none => rfl
  code_of_decode := fun {w a} h ↦ by
    match w, h with
    | false :: s, h => cases h; rfl
    | [true], h => cases h; rfl

/-- A leaf of the signature's W-type. -/
def leafW (s : List Bool) : WType binArity := WType.mk (some s) Fin.elim0

/-- A fork of the signature's W-type. -/
def forkW (l r : WType binArity) : WType binArity := WType.mk none ![l, r]

-- The spelling of a leaf: its arity zero, the tag, the length of its label and
-- the label, the tag `false` and the bitstring.
#guard binSig.spell (leafW [true, false]) =
  false :: (Geb.BitTree.Elias.encodeNat 3 ++ [false, true, false])

#guard binSig.recognize (binSig.spell (leafW [])) = true

#guard binSig.recognize (binSig.spell (leafW [true, false, true])) = true

#guard binSig.recognize (binSig.spell (forkW (leafW []) (leafW [true]))) = true

#guard binSig.recognize (binSig.spell (forkW (forkW (leafW [true]) (leafW []))
  (forkW (leafW [false, false]) (leafW [true, true, true])))) = true

#guard binSig.recognize [] = false

-- A fork with one child: the tree `fork (leaf [true]) (leaf [])` where the leftmost leaf
-- carries the fork code; the arity is one.
#guard binSig.recognize (Geb.BitTree.Elias.encode
  (Geb.BitTree.fork (Geb.BitTree.leaf [true]) (Geb.BitTree.leaf [false]))) = false

-- A leaf with a child: a rose node labelled by a leaf code with one child.
#guard binSig.recognize (Geb.BitTree.Elias.encode
  (Geb.BitTree.fork (Geb.BitTree.leaf [false, true]) (Geb.BitTree.leaf [false]))) = false

-- The empty label is no code.
#guard binSig.recognize (Geb.BitTree.Elias.encode (Geb.BitTree.leaf [])) = false

-- A fork code with a payload is no code.
#guard binSig.recognize (Geb.BitTree.Elias.encode
  (Geb.BitTree.fork (Geb.BitTree.fork (Geb.BitTree.leaf [true, true]) (Geb.BitTree.leaf [false]))
    (Geb.BitTree.leaf [false]))) = false
