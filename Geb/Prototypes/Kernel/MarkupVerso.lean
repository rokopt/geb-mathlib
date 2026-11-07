/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Markup
public import Lean.DocString.Parser
public import Lean.DocString.View

set_option doc.verso true in
/-!
# The markup of comments as Verso reads it

The reading of a text of prose by the parser of Verso's markup in Lean's core, the parser of
documentation strings under the option {option}`doc.verso`, in the terms of the recorded subset
({name}`Geb.Kernel.Markup.Block`): its paragraphs, each line's text, code and code under a role,
and its code blocks. A text Verso reads with a construct outside the subset is reported as
such. The subset's parser ({name}`Geb.Kernel.Markup.parseProse`) is correct of a text it accepts
when this reading of the text is its own, which is what the tests and the check of the sources
compare.

## Implementation notes

Lean's view of Verso's blocks ({name}`Lean.Doc.BlockView.of`) and its input contexts
({name}`Lean.Parser.mkInputContext`) depend on {lit}`Classical.choice`, so the module holds the
comparison alone, and the subset's parser is held to the strict axiom set.

## Main definitions

* {lit}`versoBlocks` — Verso's reading of a text in the subset's terms, or what it reads outside
  the subset.

## Tags

documentation, markup, Verso, parser
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Markup

open Lean Lean.Doc

/-- Inline content followed by more, adjacent texts joined, as the subset reads them. -/
def appendInline (out : List Inline) (i : Inline) : List Inline :=
  match out.getLast?, i with
  | some (.text a), .text b => out.dropLast ++ [.text (a ++ b)]
  | _, _ => out ++ [i]

/-- A paragraph's lines from Verso's inline content: a line break begins a line, and each other
element is text, code or code under a role of the subset. -/
def versoLines (inls : Array (TSyntax ``Lean.Doc.Parser.inline)) :
    Except String (List (List Inline)) :=
  inls.toList.foldlM (init := [[]]) fun ls stx ↦ do
    let add (i : Inline) := pure (ls.dropLast ++ [appendInline (ls.getLast?.getD []) i])
    match InlineView.of stx with
    | some (.text v) => add (.text v.getVersoText.toList)
    | some (.code v) => add (.code v.getVersoCode.toList)
    | some (.linebreak _) => pure (ls ++ [[]])
    | some (.role v) =>
      match Role.ofName? v.name.getId.toString.toList, v.brackets, v.content.toList with
      | some r, none, [c] =>
        match InlineView.of c with
        | some (.code cv) => add (.role r cv.getVersoCode.toList)
        | _ => throw "Verso reads a role whose content is not code"
      | _, _, _ => throw s!"Verso reads the role {v.name.getId} outside the subset"
    | some _ => throw "Verso reads emphasis, mathematics, a link, an image or a footnote"
    | none => throw "Verso reads an inline it has no view of"

/-- A block of the subset from Verso's block. -/
def versoBlock (stx : TSyntax ``Lean.Doc.Parser.block) : Except String Block :=
  match BlockView.of stx with
  | some (.para v) => do
    -- a line break ending the text, before its last newline, begins no line
    let ls ← versoLines v.content
    return .para (if ls.getLast? == some [] then ls.dropLast else ls)
  | some (.codeblock v) =>
    if v.name?.isSome then throw "Verso reads a code block with an expander"
    else
      let s := v.getVersoCodeBlock
      let s := if s.endsWith "\n" then s.dropEnd 1 |>.toString else s
      return .code (if s.isEmpty then [] else (s.splitOn "\n").map String.toList)
  | some _ => throw "Verso reads a list, a quotation, a directive, a header or metadata"
  | none => throw "Verso reads a block it has no view of"

/-- Verso's reading of a text in the subset's terms, the parser's tokens those of an environment,
or the error Verso reports or the construct outside the subset it reads. -/
def versoBlocks (env : Environment) (text : String) : Except String (List Block) := do
  let ictx := Parser.mkInputContext text "<comment>"
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let s := Doc.Parser.documentFn.run ictx pmctx (Parser.getTokenTable env)
    (Parser.mkParserState text)
  if let some (_, _, e) := s.allErrors[0]? then throw s!"Verso rejects the text: {e}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  doc.view.toList.mapM versoBlock

end Geb.Kernel.Markup

end
