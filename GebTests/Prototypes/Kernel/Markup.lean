/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Markup -- shake: keep
public meta import Geb.Prototypes.Kernel.Markup -- shake: keep

set_option doc.verso true in
/-!
# Markup of comments examples

Texts of prose the recorded subset admits are read into their blocks, which Verso's parser reads
alike ({lit}`GebTests/Prototypes/Kernel/MarkupVerso.lean`); texts holding a construct outside the
subset, or text Verso would read as one, are rejected with what rejects them. In a document of
modules, each block of comments is found in its scope, a reference to a Geb definition resolves
from it as a name resolves in Lean's namespaces, and a reference that resolves to nothing, to a
definition, a Lean constant or an entry of the bibliography, in a comment or in a note's link,
fails the check.

## Main definitions

* {lit}`accepted` and {lit}`rejected` are texts the subset admits and texts it rejects.
* {lit}`program` is a document of modules with comments and a note, and {lit}`resolver` what
  resolves its references outside it.

## Tags

documentation, markup, comment, reference, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Markup.Tests

open Geb.Kernel.Document

/-- A text's lines. -/
def linesOf (t : String) : List (List Char) := (t.splitOn "\n").map String.toList

/-- The blocks of a text. -/
def prose (t : String) : Except String (List Block) := parseProse (linesOf t)

-- text, with its escapes resolved, and a paragraph's lines
#guard prose "Plain text, (quoted) $5 and 9804.\nA second line \\_ \\* \\[x\\] \\{." ==
  .ok [.para [[.text "Plain text, (quoted) $5 and 9804.".toList],
    [.text "A second line _ * [x] {.".toList]]]
-- code and code under each role
#guard prose "See `(m T)`, {name}`Geb.Kernel.infer`, {geb}`Seq.length`, {cite}`RFC9804` and \
    {lit}`x`." ==
  .ok [.para [[.text "See ".toList, .code "(m T)".toList, .text ", ".toList,
    .role .name "Geb.Kernel.infer".toList, .text ", ".toList, .role .geb "Seq.length".toList,
    .text ", ".toList, .role .cite "RFC9804".toList, .text " and ".toList, .role .lit ['x'],
    .text ['.']]]]
-- paragraphs separated by empty lines, and a code block keeping its lines' indentation
#guard prose "First.\n\n\nSecond.\n```\n  (data D (c A))   declares D\n\n```\nThird." ==
  .ok [.para [["First.".toList].map .text], .para [["Second.".toList].map .text],
    .code ["  (data D (c A))   declares D".toList, []], .para [["Third.".toList].map .text]]

/-- Texts the subset admits. -/
def accepted : List String :=
  ["Plain text, (quoted) $5 and 9804.\nA second line \\_ \\* \\[x\\] \\{ \\}.",
    "See `(m T)`, {name}`Geb.Kernel.infer`, {geb}`Seq.length`, {cite}`RFC9804` and {lit}`x`.",
    "{geb}`f` begins a paragraph, and #2 and - and 1. stand inside a line.",
    "First.\n\n\nSecond.\n```\n  (data D (c A))   declares D\n\n```\nThird.",
    "\nA text after an empty line, \\$`x` escaped and a ! and $ alone.\n",
    "A line\n#2 after it, a number 1990. and an atom -x."]

/-- Texts the subset rejects. -/
def rejected : List String :=
  ["an unescaped _", "*emphasis*", "a citation [Key]", "a brace }", "{foo}`x`", "{name}x",
    "{name}", "`unclosed", "``", "` x`", "mathematics $`x`", "ends in \\", " leading space",
    "trailing space ", "- an item", "+ an item", "* an item", "1. an item", "2) an item",
    ": a description", ":::directive", "%%%", "> a quotation", "# A header", "```\nunclosed",
    "```\na ``` inside\n```", "```lean\nx\n```", "a line\n- an item after it"]

-- every admitted text is read, and every rejected one rejected
#guard accepted.all fun t ↦ (prose t).toBool
#guard rejected.all fun t ↦ !(prose t).toBool

/-! ## Comments in their scopes and references -/

/-- A document of modules, with comments and a note. -/
def program : String := "; The program: {geb}`Outer.f`, {geb}`top`, {name}`Geb.Kernel.infer`.
;
; {cite}`RFC9804`, and {lit}`anything`.

(module Outer (export f D c)
  ; {geb}`f`, {geb}`Inner.g`, {geb}`D`, {geb}`c` and {geb}`top`
  (def f T 0)
  (data D (c) (d T))
  (module Inner (export g)
    ; {geb}`g`, {geb}`f` and {geb}`Inner.g`
    (def g T (if 1 0
      ; {geb}`Outer.Inner.g` inside a definition
      1))))
(note (link geb Outer.f) (link lean Geb.Kernel.infer))
(def top T 0)
; {geb}`top` after the last form
"

/-- What resolves references outside {lit}`program`. -/
def resolver : Resolver :=
  ⟨(· == "Geb.Kernel.infer".toList), (· == "RFC9804".toList)⟩

/-- The failures of a text's comments and notes against its own declarations. -/
def failures (t : String) : List String :=
  match readDoc t.toList with
  | some d => check (declsOf d) resolver d
  | none => ["the text does not read"]

-- the declarations, the constructors of a datatype among them
#guard ((readDoc program.toList).map declsOf).map (·.map showPath) == some
  ["Outer", "Outer.f", "Outer.D", "Outer.c", "Outer.d", "Outer.Inner", "Outer.Inner.g", "top"]
-- the blocks of comments, each in its scope and place
#guard ((readDoc program.toList).map sitesOf).map (·.map fun s ↦ (showPath s.scope, s.place)) ==
  some [("", "before Outer"), ("Outer", "before Outer.f"),
    ("Outer.Inner", "before Outer.Inner.g"), ("Outer.Inner", "inside Outer.Inner.g"),
    ("", "after the last form")]
-- every reference resolves
#guard failures program == []

-- a reference that resolves to nothing fails, naming where it is written
#guard failures "(module M (export f)\n  ; {geb}`g`\n  (def f T 0))" ==
  ["the comment before M.f: g names no definition of the program"]
-- a definition of an inner module is not reached unqualified from outside it
#guard failures "(module M (module N (export g) (def g T 0)))\n; {geb}`g`" ==
  ["the comment after the last form: g names no definition of the program"]
#guard failures "; {name}`Geb.Kernel.nothing`\n(def f T 0)" ==
  ["the comment before f: Geb.Kernel.nothing names no Lean constant"]
#guard failures "; {cite}`Nobody2026`\n(def f T 0)" ==
  ["the comment before f: Nobody2026 is no entry of the bibliography"]
-- prose outside the subset fails, naming the line
#guard failures "; the reference [RFC9804]\n(def f T 0)" ==
  ["the comment before f: the character [ is written \\[ in text: the reference [RFC9804]"]
#guard failures ";no space\n(def f T 0)" ==
  ["the comment before f: a comment's semicolon is not followed by a space: no space"]
-- a note's link that resolves to nothing fails
#guard failures "(note (link geb g) (link lean Nope))\n(def f T 0)" ==
  ["the note of f: g names no definition of the program",
    "the note of f: Nope names no Lean constant"]

end Geb.Kernel.Markup.Tests

end
