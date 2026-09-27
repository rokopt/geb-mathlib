/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Translation -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Translation -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The translation of kernel programs

The library of the translation compiles, each definition over those before it, and the programs
the computational core's proofs are about, the prelude, the reader and the kernel's type checker
written in the kernel's syntax, translate: each definition's translation has, in the internal
language, the translation of its kernel type. The literals' cost is printed: the sizes of the
program and of its translation, whose unary numerals the successors count.

## Main definitions

* {lit}`kernelText` — the text of the prelude, the reader and the type checker.
* {lit}`translated` — a program's translation.
* {lit}`literalCost` — the sizes of the program and of its translation.

## Tags

internal language, System T, translation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Translation

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open scoped FinEnum

/-- The text of the prelude, the reader and the kernel's type checker. -/
def kernelText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check

/-- A program's translation, from its text read by the seed: the kernel types of its globals and
the definitions of the internal language. -/
def translated (text : List Char) : Option (List Tree × List Internal.Defn) :=
  (Kernel.readProgram text).bind fun ds ↦ program (ds.map Prod.snd)

-- the library compiles, each definition over those before it
#guard (Internal.compileDefs (globals [])).isSome

-- the program translates
#guard (translated kernelText.toList).isSome

-- each translated definition compiles, to the translation of its kernel type
#guard (translated kernelText.toList).any fun (gt, defs) ↦
  (Internal.compileDefs (globals defs)).isSome &&
    (gt.zip defs).all fun (A, d) ↦ ty A == some d.type

/-- The number of nodes of a tree. -/
def sizeK : Tree → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- The number of nodes of a term. -/
def sizeM : Internal.Term → ℕ := RoseTree.elim fun _ rs ↦ 1 + rs.sum

/-- The number of successors a term applies, the nodes of its unary numerals but zero. -/
def succs : Internal.Term → ℕ := RoseTree.elim fun l rs ↦
  (if l = Internal.Label.arr 1 [] then 1 else 0) + rs.sum

/-- The number of quoted trees in a kernel term, and their nodes. -/
def quotes : Tree → ℕ × ℕ := RoseTree.para fun l cs ↦
  if l = Kernel.Label.quote then (1, (cs.head?.map fun c ↦ sizeK c.1).getD 0)
  else ((cs.map (·.2.1)).sum, (cs.map (·.2.2)).sum)

/-- The literals' cost of a program, from its text, printed: the program's definitions, nodes,
quoted trees and their nodes, and its translation's nodes, the successors among them, and the
library's nodes. -/
def literalCost (text : List Char) : IO Unit := do
  match Kernel.readProgram text, translated text with
  | some ds, some (_, defs) =>
    IO.println ("definitions,kernel_nodes,quoted_trees,quoted_nodes,translation_nodes," ++
      "successors,library_nodes")
    let row := [ds.length, (ds.map fun d ↦ sizeK d.2).sum, (ds.map fun d ↦ (quotes d.2).1).sum,
      (ds.map fun d ↦ (quotes d.2).2).sum, (defs.map fun d ↦ sizeM d.body).sum,
      (defs.map fun d ↦ succs d.body).sum, (lib.map fun d ↦ sizeM d.body).sum]
    IO.println (",".intercalate (row.map toString))
  | _, _ => throw (IO.userError "the program does not translate")

#eval literalCost kernelText.toList

end GebTests.Prototypes.FreeTopos.Translation

end
