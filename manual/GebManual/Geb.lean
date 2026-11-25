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
The `gebSource` block includes one source of a manifest, after the same checks of the program's
prose, references and examples, and the `gebProofs` block a proof document, whose theorems the
prover written in Geb proves as the block elaborates, so that a program with no saved certificate
is included a source to a section.
Comments before declarations become prose; comments inside expressions remain in the code.
A declaration is a link target of the manual, named by its program and its qualified name, so
that a reference to it resolves from another page.
The `geb` code-block expander checks the document syntax of a standalone snippet.

## Tags

Geb, documentation, Verso, proof replay
-/

open Lean Verso Verso.Doc.Elab Verso.ArgParse
open Verso.Genre Manual

public section

namespace GebManual.Geb

/-- The domain of the manual's link targets that holds the declarations of the included Geb
programs, each under its anchor. -/
def gebDomain : Name := `GebManual.Geb.declaration

/-- An anchor for a declaration of the included Geb program. -/
def Block.gebAnchor (anchor : String) : Manual.Block where
  data := toJson anchor

/-- Render a Geb declaration's anchor around its source and documentation, and register the
anchor as a link target on the page that holds it. -/
@[block_extension Block.gebAnchor]
def Block.gebAnchor.descr : BlockDescr where
  traverse id data _ := do
    let .ok anchor := fromJson? (α := String) data | return none
    let path ← (·.path) <$> read
    discard <| externalTag id path anchor
    modify (·.saveDomainObject gebDomain anchor id)
    return none
  toHtml := open Verso.Output.Html in some fun _ goB id data content => do
    let .ok anchor := fromJson? (α := String) data | return .empty
    let htmlId := match (← Verso.Doc.Html.HtmlT.state).externalTags[id]? with
      | some link => link.htmlId.toString
      | none => anchor
    return html%{<div id={htmlId}>{← content.mapM goB}</div>}
  toTeX := some fun _ goB _ _ content => content.mapM goB

/-- A reference to the declaration of an included Geb program under an anchor. -/
def Inline.gebRef (anchor : String) : Manual.Inline where
  data := toJson anchor

/-- Render a reference to a Geb declaration as a link to the page and anchor that hold it; a
declaration that no page of the manual includes is rendered without a link. -/
@[inline_extension Inline.gebRef]
def Inline.gebRef.descr : InlineDescr where
  traverse _ _ _ := pure none
  toHtml := open Verso.Output.Html in some fun go _ data content => do
    let inner ← content.mapM go
    let .ok anchor := fromJson? (α := String) data | return inner
    match (← Verso.Doc.Html.HtmlT.state).resolveDomainObject gebDomain anchor with
    | .ok link => return html%{<a href={link.relativeLink}>{inner}</a>}
    | .error _ => return inner
  toTeX := some fun go _ _ content => content.mapM go

end GebManual.Geb

public meta section

namespace GebManual.Geb

open _root_.Geb Geb.Kernel.Document Geb.Kernel.Markup

/-- Source bytes decoded as UTF-8 for presentation. -/
def textOf (s : List Char) : String :=
  (String.fromUTF8? ⟨(s.map fun c ↦ c.toNat.toUInt8).toArray⟩).getD (String.ofList s)

/-- A declaration's anchor: its program's name and its fully qualified name, so that the
declarations of two included programs that name one module have distinct anchors. -/
def anchorOf (program : String) (p : Path) : String := s!"geb-{program}-{showPath p}"

/-- The target of a Geb reference, resolving the innermost scope first. -/
def targetOf (decls : List Path) (scope : Path) (s : List Char) : Option Path :=
  ((List.range (scope.length + 1)).reverse.map (scope.take · ++ s.splitOn '.')).find?
    (decls.contains ·)

/-- One inline of the checked prose subset, with references rendered as links. -/
def inlineTerm (program : String) (decls : List Path) (scope : Path) :
    Geb.Kernel.Markup.Inline → DocElabM Term
  | .text s => ``(Verso.Doc.Inline.text $(quote (textOf s)))
  | .code s | .role .lit s => ``(Verso.Doc.Inline.code $(quote (textOf s)))
  | .role .geb s => do
    let some target := targetOf decls scope s | throwError "Unresolved Geb name: {textOf s}"
    ``(Verso.Doc.Inline.other (Inline.gebRef $(quote (anchorOf program target)))
      #[Verso.Doc.Inline.code $(quote (textOf s))])
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
def prose (program : String) (decls : List Path) (scope : Path) (ls : List Line) :
    DocElabM (Array Term) := do
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
          let ts ← ins.toArray.mapM (inlineTerm program decls scope)
          ``(Verso.Doc.Block.para #[$ts,*])
      out := out.push term
  return out

/-- One document node rendered from its children's renderers, keeping module scopes. -/
def renderStep (program : String) (decls : List Path) (l : Trivia × Option (List Char))
    (rs : List (SExpr × (Path → DocElabM (Array Term)))) :
    Path → DocElabM (Array Term) := fun scope ↦ do
  let t := RoseTree.node l (rs.map Prod.fst)
  let before ← prose program decls scope l.1.lead
  let body ← match moduleName? t with
    | some m => do
      let title ← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.bold
        #[Verso.Doc.Inline.text $(quote ("Module " ++ showPath (scope ++ [m])))]] )
      let children ← (rs.drop 2).toArray.mapM (·.2 (scope ++ [m]))
      let after ← prose program decls (scope ++ [m]) l.1.close
      pure (#[title] ++ children.flatten ++ after)
    | none => do
      let clean := RoseTree.node ({ l.1 with lead := [] }, l.2) t.children
      let d : Geb.Kernel.Document.Doc := ⟨[clean], []⟩
      let code := textOf (printAt (defaultLayout .profile 100 d) d)
      pure #[← ``(Verso.Doc.Block.code $(quote code))]
  if isDecl t then
    if let some n := declName? t then
      return before.push (← ``(Verso.Doc.Block.other
        (Block.gebAnchor $(quote (anchorOf program (scope ++ [n])))) #[$body,*]))
  return before ++ body

/-- A complete source, including its trailing comments. -/
def render (program : String) (decls : List Path) (d : Geb.Kernel.Document.Doc) :
    DocElabM (Array Term) := do
  let body ← d.items.toArray.mapM (fun t ↦ RoseTree.para (renderStep program decls) t [])
  return body.flatten ++ (← prose program decls [] d.trail)

/-- The documents at the given paths in a program's profile, and the declarations of all of them,
after the check of each document's prose and references against those declarations. -/
def checkedDocuments (m : Geb.Kernel.Manifest) (paths : List System.FilePath) :
    DocElabM (List Durable × List Path) := do
  let docs ← paths.mapM fun p ↦ GebHost.Authoring.readDocument p m.profile
  let decls := docs.flatMap fun d ↦ declsOf d.doc
  let env ← getEnv
  let (_, bib) ← GebMeta.loadBibliography GebMeta.referencesBib
  let resolver : Resolver :=
    ⟨fun s ↦ env.contains (textOf s).toName, fun s ↦ bib.contains (textOf s)⟩
  for d in docs do
    for failure in check decls resolver d.doc do throwError "{failure}"
  return (docs, decls)

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
    let (docs, decls) ← checkedDocuments m paths
    let blocks ← docs.toArray.mapM fun d ↦ render m.name decls d.doc
    let blocks := blocks.flatten
    ``(Verso.Doc.Block.concat #[$blocks,*])

/-- A program and one of its documents that an inclusion renders. -/
structure DocumentConfig where
  /-- The program manifest. -/
  manifest : String
  /-- The document, a source of the program or a proof document, relative to the manifest's
  directory. -/
  document : String

instance : FromArgs DocumentConfig DocElabM where
  fromArgs := DocumentConfig.mk <$> .positional `manifest .string <*>
    .positional `document .string

/-- Include one source of a program only after the program compiles and its examples check. -/
@[block_command ]
def gebSource : BlockCommandOf DocumentConfig
  | cfg => do
    let (m, text, _) ← GebHost.Authoring.readProgram cfg.manifest
    GebHost.Authoring.checkExamples cfg.manifest m text
    let paths := Geb.Kernel.Manifest.sourcePaths cfg.manifest m
    let (docs, decls) ← checkedDocuments m paths
    let source := Geb.Kernel.Manifest.resolve cfg.manifest cfg.document
    let some (_, d) := (paths.zip docs).find? (·.1 == source)
      | throwError "{cfg.manifest} lists no source {cfg.document}"
    let blocks ← render m.name decls d.doc
    ``(Verso.Doc.Block.concat #[$blocks,*])

/-- Include a proof document only after the program's examples check and the prover written in
Geb proves the document's theorems, the certificate it finds replaying; nothing is written. -/
@[block_command ]
def gebProofs : BlockCommandOf DocumentConfig
  | cfg => do
    let proofs := Geb.Kernel.Manifest.resolve cfg.manifest cfg.document
    let s ← GebHost.Authoring.Session.read cfg.manifest proofs.toString
    discard <| s.prove proofs.toString
    let m ← Geb.Kernel.Manifest.read cfg.manifest
    let paths := Geb.Kernel.Manifest.sourcePaths cfg.manifest m ++ [proofs]
    let (docs, decls) ← checkedDocuments m paths
    let some d := docs.getLast? | throwError "{proofs}: no document"
    let blocks ← render m.name decls d.doc
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
