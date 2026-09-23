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
tail of the stream; the head of a coding word is the stream's first entry,
and the coalgebra on codes steps from a coding word to the tail word. The
value at depth zero of the iterated unary squaring of a two-bit constant has
length the iterated square of two, within the bound by the code's size.
An expression whose value is the code of a composition at the empty word
and the code of an initial function elsewhere codes, in the M-type of the
bundle signature itself, a tree whose root is the composition and whose
children are that initial function; the projection's empty values read as
the default shape, the root, at every node.
The recognizer of expressions at every arity accepts
the spellings of the expression of two normal arguments and of an
expression under no root, and rejects a coding word and the empty word.

## Tags

bitstream, M-type, logspace, recognizer, test
-/

set_option doc.verso true
set_option linter.privateModule false

open Geb.BitStream.Oitavem Geb.Oitavem Geb.BitStream.WConstruction
open Geb.MType.Depth (ofNat)
open Geb.MType.M (observe)

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

#guard headCode (spellExpr projE) = some none

#guard headCode (spellExpr onesE) = some (some true)

#guard headCode (spellExpr lastE) = some (some false)

#guard headCode [] = none

#guard stepCode (spellExpr projE) = none

#guard stepCode (spellExpr onesE) = some (true, spellExpr (tailExpr onesE))

/-- The product of an argument with itself. -/
private def squareE : Expr 1 0 :=
  Expr.comp (safe := false) (Expr.initial .product)
    ![Expr.initial (.proj 1 0), Expr.initial (.proj 1 0)]

/-- The iterated square of a two-bit constant. -/
private def squaresE : ℕ → Expr 1 0
  | 0 => Expr.comp (safe := false) (Expr.initial (.succ true))
      ![Expr.comp (safe := false) (Expr.initial (.succ true)) ![Expr.initial (.zero 1)]]
  | k + 1 => Expr.comp (safe := false) squareE ![squaresE k]

#guard (List.range 5).map (fun k ↦ (valueAt (squaresE k) 0).length) = [2, 4, 16, 256, 65536]

#guard (List.range 5).map (fun k ↦ size (squaresE k).1.1) = [5, 10, 15, 20, 25]

#guard (valueAt (squaresE 3) 0).length ≤ (0 + 2) ^ 2 ^ size (squaresE 3).1.1

#guard codedPlain.recognize (codedPlain.spell binE.1.1) = true

#guard codedPlain.recognize (codedPlain.spell onesE.1.1) = true

#guard codedPlain.recognize (spellExpr onesE) = false

#guard codedPlain.recognize [] = false

/-- A constant word: a chain of successors over zero. -/
private def constE : List Bool → Expr 1 0
  | [] => Expr.initial (.zero 1)
  | b :: w => Expr.comp (safe := false) (Expr.initial (.succ b)) ![constE w]

/-- The shape of a composition with one argument, under the root. -/
private def compShape : Option Shape := some (.comp 1 1 false)

/-- The shape of the last-bit function, under the root. -/
private def lastShape : Option Shape := some (.initial .last)

/-- The root as the default shape of the bundle signature: the fallback of a
value that decodes to no shape. -/
instance : Inhabited coded.P.A := ⟨(none : Option Shape)⟩

/-- Decidable equality of the bundle signature's shapes, at the coded
signature's shape type. -/
instance : DecidableEq coded.P.A := inferInstanceAs (DecidableEq (Option Shape))

/-- The shape at the root of a tree of the bundle signature. -/
private def rootShape (t : coded.P.toPFunctor.M) : Option Shape := PFunctor.M.head t

/-- The shape at a path of a tree of the bundle signature. -/
private def shapeAtPath (ps : List coded.P.toPFunctor.Idx) (t : coded.P.toPFunctor.M) :
    Option Shape :=
  PFunctor.M.iselect ps t

/-- The code of the composition at the empty word, and of the last-bit
function elsewhere. -/
private def branchE : Expr 1 0 :=
  Expr.comp (safe := false) (Expr.initial .cond)
    ![Expr.initial (.proj 1 0), constE (code compShape), constE (code lastShape)]

#guard rootShape (toM coded branchE) = compShape

#guard shapeAtPath [⟨compShape, Sum.inl ()⟩] (toM coded branchE) = lastShape

#guard shapeAtPath [⟨compShape, Sum.inr 0⟩] (toM coded branchE) = lastShape

#guard rootShape (toM coded projE) = none

#guard shapeAtPath [⟨none, ()⟩, ⟨none, ()⟩] (toM coded projE) = none

#guard pathWord coded [⟨compShape, Sum.inl ()⟩, ⟨compShape, Sum.inr 0⟩] = [false, true, false]
