/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Strict -- shake: keep
public meta import Geb.Prototypes.Kernel.Strict -- shake: keep
public import GebTests.Prototypes.Kernel.Document -- shake: keep
public meta import GebTests.Prototypes.Kernel.Document -- shake: keep

set_option doc.verso true in
/-!
# Strict encoding examples

The authoring profile reads the spellings of atoms of the advanced encoding: verbatim, quoted
with a length, hexadecimal and base-64, each with or without a length, and rejects a length
that the bytes do not match or that is not in shortest form. A document with comments, and each
source of the stage-0 compiler, is read back from its canonical encoding, and from the basic
transport encoding's base-64 form.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`,
as in the kernel's examples.

## Tags

S-expression, RFC 9804, canonical encoding, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document.StrictTests

open Geb.Kernel.Stage0Tests Geb.Kernel.Document.Tests

-- the spellings of an atom of the advanced encoding, with and without a length
#guard readSExps "(3:abc #616263# |YWJj| 3\"abc\" 3#616263# 3|YWJj| # 61 62\n63 # abc)".toList =
  some [RoseTree.node none ((List.replicate 8 "abc".toList).map fun s ↦ RoseTree.node (some s) [])]
#guard readSExps "(|YWJjZA| |YWJjZA==| 0: ## ||)".toList = some [RoseTree.node none
  ([some "abcd".toList, some "abcd".toList, some [], some [], some []].map
    fun a ↦ RoseTree.node a [])]
-- a verbatim atom holds any bytes, parentheses and quotes among them
#guard readSExps "(4:()\"; 1:a)".toList = some [RoseTree.node none
  ([some "()\";".toList, some "a".toList].map fun a ↦ RoseTree.node a [])]

-- a length the bytes do not match, or not in shortest form, an odd number of hexadecimal
-- digits, and a base-64 group of one character, are rejected
#guard readDoc "(4\"abc\")".toList = none
#guard readDoc "(2#616263#)".toList = none
#guard readDoc "(007:abcdefg)".toList = none
#guard readDoc "(#616#)".toList = none
#guard readDoc "(|YWJjZ|)".toList = none
#guard readDoc "(5:abc)".toList = none

-- the canonical encoding of an S-expression
#guard ((readSExps "(def x (quote (0 \"a b\")))".toList).map fun es ↦ es.map canonOf) =
  some ["(3:def1:x(5:quote(1:03:a b)))".toList]

-- a document with comments and each source of the stage-0 compiler read back from its canonical
-- encoding
#guard [sample, sampleFormatted, prelude, serialize, reader, check, datatype, compile].all
  fun src ↦ (readDoc src.toList).all fun d ↦
    (readStrictDoc (printCanonDoc d)).map Doc.tokens == some d.tokens

-- the basic transport encoding: the canonical encoding, or its base-64 form between braces
#guard (readBasic "(4:*doc()1:x)".toList).map Doc.tokens = some [.atom false ['x']]
#guard (readBasic " {KDQ6KmRvYygpMTp4KQ==} ".toList).map Doc.tokens =
  (readBasic "(4:*doc()1:x)".toList).map Doc.tokens
#guard (readBasic "{KDQ6KmRvYygpKDE6YTI6YmMpKQ==}".toList).map Doc.tokens =
  (readStrictDoc "(4:*doc()(1:a2:bc))".toList).map Doc.tokens

-- a list headed by the reserved atom *ann of the annotation forms is excluded from strict form
#guard ((readDoc "(*ann a b c d)".toList).map Doc.strictWf) = some false

end Geb.Kernel.Document.StrictTests

end
