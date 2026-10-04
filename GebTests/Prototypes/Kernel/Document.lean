/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Document -- shake: keep
public meta import Geb.Prototypes.Kernel.Document -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# Source document examples

A text with comments, empty lines and nested lists is read into S-expressions decorated with
them, and formatted to a pinned text: a list that fits on a line is written on it, one that
does not fills its first line and indents the rest past its opening parenthesis, comments begin
lines, and empty lines between items are kept. Formatting is idempotent, and the formatted
text reads to the S-expressions the kernel's reader reads from the original, on that text and
on the sources of the stage-0 compiler. Unbalanced text does not read.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`,
as in the kernel's examples.

## Main definitions

* {lit}`sample` is a text with comments and empty lines, and {lit}`sampleFormatted` its
  formatted text.

## Tags

S-expression, comments, formatter, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document.Tests

open Geb.Kernel.Stage0Tests

/-- A text with a header comment, an empty line, comments before definitions and inside a
list, and a definition too long for one line. -/
def sample : String := "; a header

; the identity
(def id (lam ((x T)) x))
(def pick (lam ((a T) (b T) (c T))
  ; the first unless it is zero
  (if a a (if b b c))))
(def long (lam ((alpha T) (beta T) (gamma T) (delta T)) " ++
  "(pair (pair alpha beta) (pair gamma delta))))"

/-- The formatted text of {name}`sample`. -/
def sampleFormatted : String := "; a header

; the identity
(def id (lam ((x T)) x))
(def pick
  (lam ((a T) (b T) (c T))
    ; the first unless it is zero
    (if a a (if b b c))))
(def long
  (lam ((alpha T) (beta T) (gamma T) (delta T)) (pair (pair alpha beta) (pair gamma delta))))
"

-- the sample's S-expressions: three definitions, the first decorated with the two comment
-- lines before it, the second after an empty line, and no comment lines after the last
#guard ((readDoc sample.toList).map (·.items.length)) = some 3
#guard ((readDoc sample.toList).map fun d ↦
    d.items.map fun t ↦ (RoseTree.extract t).lead.map (·.gap)) =
  some [[false, true], [], []]
#guard ((readDoc sample.toList).map (·.trail)) = some []
-- a comment line before a list's end decorates the list, and one after the last S-expression
-- the document
#guard ((readDoc "(a\n ; x\n )\n; y\n".toList).map fun d ↦
    (d.items.map fun t ↦ (RoseTree.extract t).close.map (·.text), d.trail.map (·.text))) =
  some ([[" x".toList]], [" y".toList])

#guard format 100 sample.toList = some sampleFormatted.toList
#guard format 100 sampleFormatted.toList = some sampleFormatted.toList

-- the formatted text reads to the S-expressions of the original
#guard ((format 100 sample.toList).bind readSExps) = readSExps sample.toList

-- the sources of the stage-0 compiler: formatting is idempotent and keeps their S-expressions
#guard [prelude, serialize, reader, check, datatype, compile].all fun src ↦
  let t := src.toList
  (format 100 t).bind (format 100) = format 100 t &&
    (format 100 t).bind readSExps = readSExps t

-- a narrow line width breaks every list that does not fit, and keeps the S-expressions
#guard ((format 20 sample.toList).bind readSExps) = readSExps sample.toList

-- an atom is written bare when it is a numeral, a token or the ampersand, and otherwise
-- quoted, its double quotes and backslashes escaped and its control characters in hexadecimal
#guard spell "let".toList = "let".toList
#guard spell "12".toList = "12".toList
#guard spell "&".toList = "&".toList
#guard spell "a b".toList = "\"a b\"".toList
#guard spell "2x".toList = "\"2x\"".toList
#guard spell ['"', '\\', Char.ofNat 9, 'σ'] = "\"\\\"\\\\\\x09σ\"".toList
#guard spell [] = "\"\"".toList

-- quoted strings read the escapes of RFC 9804, and a backslash before a line break continues the
-- string
#guard readSExps "(f \"a b\" 12 & x)".toList = some [RoseTree.node none
  ([some "f".toList, some "a b".toList, some "12".toList, some "&".toList, some "x".toList].map
    fun a ↦ RoseTree.node a [])]
#guard readSExps "\"\\t\\x41\\101\\\"\\\\\\?\"".toList =
  some [RoseTree.node (some [Char.ofNat 9, 'A', 'A', '"', '\\', '?']) []]
#guard readSExps "\"ab\\\ncd\"".toList = some [RoseTree.node (some "abcd".toList) []]
#guard readSExps "\"a\nσ\"".toList = some [RoseTree.node (some "a\nσ".toList) []]

-- a hole is the form (hole name), written ?name
#guard readSExps "(f ?x)".toList = readSExps "(f (hole x))".toList
#guard format 100 "(f (hole x))".toList = some "(f ?x)\n".toList
#guard format 100 "(f (hole\n ; why\n x))".toList = some "(f\n  (hole\n    ; why\n    x))\n".toList

-- formatting writes each atom in its spelling
#guard format 100 "(a \"x\\x41\" \"1 2\" \"007\")".toList = some "(a xA \"1 2\" 007)\n".toList

-- the profile admits no digits followed by a token's characters, no display hint, no character
-- outside a quoted string that no token admits, no hole without a name, and no string that does
-- not end; the strict encodings' spellings of atoms it admits, as their tests show
#guard readDoc "(a 12b)".toList = none
#guard readDoc "(a [h]x)".toList = none
#guard readDoc "(a σ)".toList = none
#guard readDoc "(a ?)".toList = none
#guard readDoc "(a ?1)".toList = none
#guard readDoc "(a \"bc)".toList = none
#guard readDoc "(a \"\\q\")".toList = none

-- unbalanced text does not read
#guard readDoc "(def x".toList = none
#guard readDoc "(def x))".toList = none
#guard format 100 ")".toList = none

end Geb.Kernel.Document.Tests

end
