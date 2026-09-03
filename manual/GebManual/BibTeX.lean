/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public meta import GebMeta
public meta import Lean.Elab.Command

/-! # Bibliography entries generated from `docs/references.bib`

`bibliography_entries` declares one `Citable` value per entry of the
repository's `docs/references.bib`, named by its citation key, so
that a chapter cites with `{citep Key}[]` and the `.bib` stays the
single record of the bibliographic detail
(`CONTRIBUTING.md` § Cite the literature when transcribing).

## Main definitions

* `bibliography_entries` — the command.
* `GebManual.BibTeX.citable` — the `Citable` term of one entry.

## Implementation notes

The file is read and parsed by `GebMeta.loadBibliography`, which the
`{cite}` docstring role shares. Verso's manual genre defines four
citable kinds, article, in-proceedings, thesis and arXiv; an entry of
another kind (a book, a technical report, a web page) is declared as
an article whose journal is its publisher, institution or
`howpublished` field, the nearest of the four in rendering.
-/

open Lean Elab Command
open Verso.Genre.Manual Verso.Genre.Manual.Bibliography

public meta section

namespace GebManual.BibTeX

/-- A text inline term. -/
def text (s : String) : CommandElabM Term := `(Verso.Doc.Inline.text $(quote s))

/-- An optional text inline term. -/
def text? (s : Option String) : CommandElabM Term :=
  match s with
  | some s => do `(some $(← text s))
  | none => `(none)

/-- An optional string term. -/
def str? (s : Option String) : CommandElabM Term :=
  match s with
  | some s => `(some $(quote s))
  | none => `(none)

/-- The page range of a `pages` field written `first--last`. -/
def pages? (s : Option String) : Option (Nat × Nat) := do
  let [a, b] := (← s).splitOn "--" | none
  return (← a.toNat?, ← b.toNat?)

/-- The `Citable` term of an entry, by its category. -/
def citable (e : GebMeta.BibEntry) : CommandElabM Term := do
  let get n := e.fields[n]?
  let title ← text (get "title" |>.getD e.key)
  let names := GebMeta.BibEntry.names ((get "author" <|> get "editor").getD e.key)
  let authors ← `(#[$(← names.mapM text),*])
  let year ← `(($(quote ((get "year").bind String.toNat? |>.getD 0)) : Int))
  let url ← str? e.link
  match e.category with
  | "inproceedings" | "incollection" =>
    let booktitle ← text (get "booktitle" |>.getD "")
    let series ← text? (get "series")
    `(Citable.inProceedings {
        title := $title
        authors := $authors
        year := $year
        booktitle := $booktitle
        editors := none
        series := $series
        url := $url })
  | "phdthesis" =>
    let author ← text (names[0]?.getD e.key)
    let university ← text (get "school" |>.getD "")
    `(Citable.thesis {
        title := $title
        author := $author
        year := $year
        university := $university
        degree := Verso.Doc.Inline.text "PhD thesis"
        url := $url })
  | "misc" | "unpublished" =>
    if (get "archiveprefix").map (·.toLower) == some "arxiv" && (get "eprint").isSome then
      let id := quote (get "eprint" |>.getD "")
      `(Citable.arXiv {
          title := $title
          authors := $authors
          year := $year
          id := $id })
    else article
  | _ => article
where
  /-- The article form, also used for a category the manual genre lacks. -/
  article : CommandElabM Term := do
    let get n := e.fields[n]?
    let title ← text (get "title" |>.getD e.key)
    let names := GebMeta.BibEntry.names ((get "author" <|> get "editor").getD e.key)
    let authors ← `(#[$(← names.mapM text),*])
    let year ← `(($(quote ((get "year").bind String.toNat? |>.getD 0)) : Int))
    let pages ← match pages? (get "pages") with
      | some (a, b) => `(some ($(quote a), $(quote b)))
      | none => `(none)
    let journal ← text (e.venue.getD "")
    let volume ← text (get "volume" |>.getD "")
    let number ← text (get "number" |>.getD "")
    let url ← str? e.link
    `(Citable.article {
        title := $title
        authors := $authors
        journal := $journal
        year := $year
        month := none
        volume := $volume
        number := $number
        pages := $pages
        url := $url })

/-- Declares one `public def <Key> : Citable` per entry of the
repository's `docs/references.bib`, in key order. -/
syntax (name := bibliographyEntries) "bibliography_entries" : command

elab_rules : command
  | `(bibliography_entries) => do
    let (path, bib) ← GebMeta.loadBibliography (← getFileName)
    let entries := bib.toArray.qsort (·.1 < ·.1)
    for (key, e) in entries do
      let doc : TSyntax ``Lean.Parser.Command.docComment :=
        ⟨mkNode ``Lean.Parser.Command.docComment
          #[mkAtom "/--", mkAtom s!"The entry `{key}` of `{path.fileName.getD ""}`. -/"]⟩
      let name := mkIdent (Name.mkSimple key)
      let value ← citable e
      elabCommand (← `($doc:docComment public def $name:ident : Citable := $value))

end GebManual.BibTeX
