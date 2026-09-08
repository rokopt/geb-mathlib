/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.ConcreteSyntax.Command
public meta import Geb.Prototypes.ConcreteSyntax.Command -- shake: keep; #eval needs it
public import GebTests.Prototypes.ConcreteSyntax
public meta import GebTests.Prototypes.ConcreteSyntax -- shake: keep; #eval needs it

set_option doc.verso true

/-!
# S-expression file I/O tests

Exercise the library wrappers and command with temporary files removed by
{name}`IO.FS.withTempDir`. The tests compare file bytes, parsed trees and exit
statuses and exceptions, including failures that must preserve an existing output file.

## Main definitions

* {lit}`testSexprIO`: file round trips, conversion, and rejection checks.

## Tags

S-expression, file I/O, test
-/

public section

open Geb

/-- Run the file and command checks in an isolated temporary directory. -/
def testSexprIO : IO Unit := IO.FS.withTempDir fun dir ↦ do
  -- The fixed relative filenames need no choice-dependent absolute-path test from FilePath.join.
  let child := fun name ↦ System.FilePath.mk
    (dir.toString ++ System.FilePath.pathSeparator.toString ++ name)
  let input := child "input.sexp"
  let output := child "output.sexp"
  let check := fun (ok : Bool) (label : String) ↦
    unless ok do throw <| IO.userError label
  let formats := [
    ("canonical", "(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))"),
    ("canonical-rose", "(1:0(1:1(1:2)))"),
    ("readable", "(0 (1 2))")]
  for (format, expected) in formats do
    IO.FS.writeFile input "longer existing contents that must be truncated by the writer"
    Sexpr.writeAst format input sampleAst
    check ((← IO.FS.readBinFile input) == expected.toUTF8) s!"{format}: output bytes"
    check ((← Sexpr.readAst format 3 input) == some sampleAst) s!"{format}: round trip"
    check ((← Sexpr.run ["check", format, "3", input.toString]) == 0) "check status"
    check ((← Sexpr.readAst format 2 input).isNone) "label bound"
    for (target, targetText) in formats do
      check ((← Sexpr.run ["convert", format, target, "3", input.toString,
        output.toString]) == 0) "conversion status"
      check ((← IO.FS.readBinFile output) == targetText.toUTF8) "conversion bytes"
  IO.FS.writeFile input " \t(0 (1 2))\r\n"
  check ((← Rsexp.readFile 3 input) == some sampleAst.toRose) "readable whitespace"
  check ((← Sexpr.run ["convert", "readable", "canonical", "3", input.toString,
    input.toString]) == 0) "same-path conversion"
  check ((← Csexp.readFile 3 input) == some sampleAst) "same-path result"
  CSexp.writeFile output sampleAst.toCSexp
  check ((← Csexp.readFile 3 output) == some sampleAst) "canonical expression writer"
  IO.FS.writeFile output "preserve"
  check ((← (CSexp.writeFile output (CSexp.atom ['é'])).toBaseIO).toOption.isNone)
    "ASCII restriction"
  check ((← IO.FS.readBinFile output) == "preserve".toUTF8) "ASCII failure preserves output"
  for (format, _) in formats do
    for bytes in [ByteArray.empty, "(".toUTF8, "0 x".toUTF8, ⟨#[255]⟩] do
      IO.FS.writeBinFile input bytes
      check ((← Sexpr.readAst format 3 input).isNone) "invalid input"
  for args in [[], ["check", "readable", "-1", input.toString],
      ["check", "readable", "", input.toString],
      ["check", "unknown", "3", input.toString],
      ["check", "readable", "3", (child "missing").toString],
      ["convert", "readable", "canonical", "3", input.toString, output.toString]] do
    check ((← (Sexpr.run args).toBaseIO).toOption.isNone) "command error"
  check ((← IO.FS.readBinFile output) == "preserve".toUTF8) "parse failure preserves output"
  IO.FS.writeFile input "0"
  check ((← (Sexpr.run ["convert", "readable", "unknown", "3", input.toString,
    output.toString]).toBaseIO).toOption.isNone) "unknown output format"
  check ((← IO.FS.readBinFile output) == "preserve".toUTF8) "format failure preserves output"
  check ((← (Sexpr.run ["convert", "readable", "canonical", "3", input.toString,
    dir.toString]).toBaseIO).toOption.isNone) "write error"

#eval testSexprIO
