/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public meta import GebHost.Authoring
public meta import Geb.Prototypes.Kernel.MarkupVerso
public meta import GebManual.Bibliography

/-! # Checked Geb documents in the manual

The `gebProgram` block includes the sources of a manifest and its proof document. Elaboration
checks their prose and references, executes their examples, and replays the saved certificate.
Comments before declarations become prose; comments inside expressions remain in the code.
The `geb` code-block expander checks the document syntax of a standalone snippet.

## Tags

Geb, documentation, Verso, proof replay
-/

open Lean Verso Verso.Doc.Elab Verso.ArgParse
open Verso.Genre Manual

public section

namespace GebManual.Geb

/-- An anchor for a declaration of the included Geb program. -/
def Block.gebAnchor (anchor : String) : Manual.Block where
  data := toJson anchor

/-- Render a Geb declaration's anchor around its source and documentation. -/
@[block_extension Block.gebAnchor]
def Block.gebAnchor.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := open Verso.Output.Html in some fun _ goB _ data content => do
    let .ok anchor := fromJson? (α := String) data | return .empty
    return html%{<div id={anchor}>{← content.mapM goB}</div>}
  toTeX := some fun _ goB _ _ content => content.mapM goB

end GebManual.Geb

public meta section

namespace GebManual.Geb

open _root_.Geb Geb.Kernel.Document Geb.Kernel.Markup

/-- Source bytes decoded as UTF-8 for presentation. -/
def textOf (s : List Char) : String :=
  (String.fromUTF8? ⟨(s.map fun c ↦ c.toNat.toUInt8).toArray⟩).getD (String.ofList s)

/-- A declaration's fragment identifier, using its fully qualified name. -/
def anchorOf (p : Path) : String := "geb-" ++ showPath p

/-- The target of a Geb reference, resolving the innermost scope first. -/
def targetOf (decls : List Path) (scope : Path) (s : List Char) : Option Path :=
  ((List.range (scope.length + 1)).reverse.map (scope.take · ++ s.splitOn '.')).find?
    (decls.contains ·)

/-- One inline of the checked prose subset, with references rendered as links. -/
def inlineTerm (decls : List Path) (scope : Path) : Geb.Kernel.Markup.Inline → DocElabM Term
  | .text s => ``(Verso.Doc.Inline.text $(quote (textOf s)))
  | .code s | .role .lit s => ``(Verso.Doc.Inline.code $(quote (textOf s)))
  | .role .geb s => do
    let some target := targetOf decls scope s | throwError "Unresolved Geb name: {textOf s}"
    ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.code $(quote (textOf s))]
      $(quote ("#" ++ anchorOf target)))
  | .role .name s => do
    let hl ← InlineLean.constTok (textOf s).toName (textOf s)
    `(Verso.Doc.Inline.other
      { InlineLean.Inline.name with data := toJson $(quote hl) }
      #[Verso.Doc.Inline.code $(quote (textOf s))])
  | .role .cite s => do
    let entry := mkIdent (textOf s).toName
    ``(Verso.Doc.Inline.other (Bibliography.Inline.cite
      ([$entry] : List Bibliography.Citable) Bibliography.Style.parenthetical) #[])

/-- Comment runs rendered from the same subset that the documentation checker accepts. -/
def prose (decls : List Path) (scope : Path) (ls : List Line) : DocElabM (Array Term) := do
  let mut out := #[]
  for run in blocksOf ls do
    let lines ← IO.ofExcept (run.mapM proseOf)
    let bs ← IO.ofExcept (parseProse lines)
    let vs ← IO.ofExcept (versoBlocks (← getEnv) ("\n".intercalate (lines.map String.ofList)))
    unless bs == vs do throwError "Verso and the Geb markup parser disagree"
    for b in bs do
      let term ← match b with
        | .code lines => ``(Verso.Doc.Block.code $(quote ("\n".intercalate (lines.map textOf))))
        | .para lines => do
          let ins := lines.intersperse [.text ['\n']] |>.flatten
          let ts ← ins.toArray.mapM (inlineTerm decls scope)
          ``(Verso.Doc.Block.para #[$ts,*])
      out := out.push term
  return out

/-- One document node rendered from its children's renderers, keeping module scopes. -/
def renderStep (decls : List Path) (l : Trivia × Option (List Char))
    (rs : List (SExpr × (Path → DocElabM (Array Term)))) :
    Path → DocElabM (Array Term) := fun scope ↦ do
  let t := RoseTree.node l (rs.map Prod.fst)
  let before ← prose decls scope l.1.lead
  let body ← match moduleName? t with
    | some m => do
      let title ← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.bold
        #[Verso.Doc.Inline.text $(quote ("Module " ++ showPath (scope ++ [m])))]] )
      let children ← (rs.drop 2).toArray.mapM (·.2 (scope ++ [m]))
      let after ← prose decls (scope ++ [m]) l.1.close
      pure (#[title] ++ children.flatten ++ after)
    | none => do
      let clean := RoseTree.node ({ l.1 with lead := [] }, l.2) t.children
      let d : Geb.Kernel.Document.Doc := ⟨[clean], []⟩
      let code := textOf (printAt (defaultLayout .profile 100 d) d)
      pure #[← ``(Verso.Doc.Block.code $(quote code))]
  if isDecl t then
    if let some n := declName? t then
      return before.push (← ``(Verso.Doc.Block.other
        (Block.gebAnchor $(quote (anchorOf (scope ++ [n])))) #[$body,*]))
  return before ++ body

/-- A complete source, including its trailing comments. -/
def render (decls : List Path) (d : Geb.Kernel.Document.Doc) : DocElabM (Array Term) := do
  let body ← d.items.toArray.mapM (fun t ↦ RoseTree.para (renderStep decls) t [])
  return body.flatten ++ (← prose decls [] d.trail)

/-- The program, proof source, and certificate that an inclusion checks. -/
structure ProgramConfig where
  /-- The program manifest. -/
  manifest : String
  /-- The proof document, relative to the manifest's directory. -/
  proofs : String
  /-- The saved certificate, relative to the manifest's directory. -/
  certificate : String

instance : FromArgs ProgramConfig DocElabM where
  fromArgs := ProgramConfig.mk <$> .positional `manifest .string <*>
    .positional `proofs .string <*> .positional `certificate .string

/-- Include a program only after its examples and saved proofs check. -/
@[block_command ]
def gebProgram : BlockCommandOf ProgramConfig
  | cfg => do
    let dir := (System.FilePath.mk cfg.manifest).parent.getD "."
    let proofs := dir / cfg.proofs
    let certificate := dir / cfg.certificate
    discard <| GebHost.Authoring.execute "replay" cfg.manifest proofs.toString certificate.toString
    let m ← Geb.Kernel.Manifest.read cfg.manifest
    let paths := Geb.Kernel.Manifest.sourcePaths cfg.manifest m ++ [proofs]
    let docs ← paths.mapM fun p ↦ GebHost.Authoring.readDocument p m.profile
    let decls := docs.flatMap fun d ↦ declsOf d.doc
    let env ← getEnv
    let (_, bib) ← GebMeta.loadBibliography GebMeta.referencesBib
    let resolver : Resolver :=
      ⟨fun s ↦ env.contains (textOf s).toName, fun s ↦ bib.contains (textOf s)⟩
    for d in docs do
      for failure in check decls resolver d.doc do throwError "{failure}"
    let blocks ← docs.toArray.mapM fun d ↦ render decls d.doc
    let blocks := blocks.flatten
    ``(Verso.Doc.Block.concat #[$blocks,*])

/-- A Geb snippet whose source-document syntax is checked at elaboration. -/
@[code_block ]
def geb : CodeBlockExpanderOf Unit
  | (), str => do
    let text := str.getVersoCodeBlock
    unless (readDoc (Geb.Kernel.Command.chars text.toUTF8)).isSome do
      throwErrorAt str "Malformed Geb source document"
    ``(Verso.Doc.Block.code $(quote text))

end GebManual.Geb

end

end
