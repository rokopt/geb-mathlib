/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem -- shake: keep; #guard needs it
public meta import Geb.Prototypes.BitStream.Oitavem -- shake: keep; #guard needs it

set_option doc.verso true in
/-!
# Executable checks of the recognizer of Oitavem-coded bitstreams

The recognizer accepts the words coding the streams of three expressions of
one normal and no safe argument, the projection of the depth, a set bit
before the depth and the last bit of the depth, and rejects the empty word,
the spelling of an expression without the root, a coding word with a bit
appended or removed, and an expression of two normal arguments under the
root. The streams the three expressions code are observed at small depths:
the empty stream, the constant stream of set bits, and the constant stream
of clear bits; and decoding a coding word yields the stream. The tail on
words yields a coding word, the code of the composite, whose stream is the
tail of the stream.

## Tags

bitstream, M-type, logspace, recognizer, test
-/

set_option doc.verso true
set_option linter.privateModule false

open Geb.BitStream.Oitavem Geb.Oitavem Geb.BitStream.WConstruction

/-- The projection of the depth: its value at every depth is the depth's
word, empty at depth zero, so the stream is empty. -/
private def projE : Expr 1 0 := Expr.initial (.proj 1 0)

/-- A set bit before the depth: the constant stream of set bits. -/
private def onesE : Expr 1 0 :=
  Expr.comp (safe := false) (Expr.initial (.succ true)) ![Expr.initial (.proj 1 0)]

/-- The last bit of the depth's word: a clear bit at every depth. -/
private def lastE : Expr 1 0 := Expr.initial .last

/-- An expression of two normal arguments, which no bundle admits. -/
private def binE : Expr 2 0 := Expr.initial (.proj 2 0)

#guard recognize (spellExpr projE) = true

#guard recognize (spellExpr onesE) = true

#guard recognize (spellExpr lastE) = true

#guard recognize [] = false

#guard recognize (coded.spell (embed projE.1.1)) = false

#guard recognize (spellExpr projE ++ [false]) = false

#guard recognize ((spellExpr onesE).take ((spellExpr onesE).length - 1)) = false

#guard recognize (rootPrefix ++ coded.spell (embed binE.1.1)) = false

#guard (prefixEquiv (ofNat 3) (observe (toStream projE) (ofNat 3))).val = []

#guard (prefixEquiv (ofNat 3) (observe (toStream onesE) (ofNat 3))).val = [true, true, true]

#guard (prefixEquiv (ofNat 2) (observe (toStream lastE) (ofNat 2))).val = [false, false]

#guard (decodeStream (spellExpr onesE)).map
  (fun s ↦ (prefixEquiv (ofNat 2) (observe s (ofNat 2))).val) = some [true, true]

#guard decodeStream [] = none

#guard tailWord (spellExpr onesE) = spellExpr (tailExpr onesE)

#guard recognize (tailWord (spellExpr lastE)) = true

#guard (prefixEquiv (ofNat 2) (observe (toStream (tailExpr onesE)) (ofNat 2))).val = [true, true]

#guard (prefixEquiv (ofNat 2) (observe (tail (toStream lastE)) (ofNat 2))).val =
  (prefixEquiv (ofNat 2) (observe (toStream (tailExpr lastE)) (ofNat 2))).val
