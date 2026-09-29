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

A text with comments, empty lines and nested lists is read into items that keep them, and
formatted to a pinned text: a list that fits on a line is written on it, one that does not
fills its first line and indents the rest past its opening parenthesis, comments begin lines,
and empty lines between items are kept. Formatting is idempotent, and the formatted text reads
to the S-expressions the kernel's reader reads from the original, on that text and on the
sources of the stage-0 compiler. Unbalanced text does not read.

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

-- the sample's items: two comments and three definitions, the second comment after an empty
-- line
#guard ((readDoc sample.toList).map List.length) = some 5
#guard ((readDoc sample.toList).map fun ds ↦ ds.map (·.label.gap)) =
  some [false, true, false, false, false]

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

-- unbalanced text does not read
#guard readDoc "(def x".toList = none
#guard readDoc "(def x))".toList = none
#guard format 100 ")".toList = none

end Geb.Kernel.Document.Tests

end
