/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.DocString
public meta import Lean.DocString.Syntax

/-!
# Axiom-hygiene linter and the `{cite}` docstring role

`detectNonstandardAxiom` is an `@[env_linter]` that fails
`lake lint` when a declaration depends on any axiom outside the
permitted set for its module. For most modules the permitted set
is `{propext, Quot.sound}`; modules in `classicalAllowedModules`
additionally permit `Classical.choice`.

`cite` is a docstring role for literate modules
(`docs/rules/lean-coding.md` § Literate modules): ``{cite}`Key` ``
resolves `Key` in the repository's `docs/references.bib` at
elaboration, failing on an unknown key, and renders as the key with
the formatted entry disclosed on demand. `loadBibliography` is the
parsed bibliography it and the manual's generated entries share.

## Main definitions

* `GebMeta.detectNonstandardAxiom` — the linter.
* `GebMeta.classicalAllowedModules` — the exact module names
  additionally permitted to depend on `Classical.choice`.
* `cite` — the docstring role, at the root namespace.
* `GebMeta.loadBibliography` — the parsed `docs/references.bib` of
  the repository containing a given source file.

## Implementation notes

The linter is built on `Lean.collectAxioms` (core Lean, in
`Lean/Util/CollectAxioms.lean`), the same primitive `#print
axioms` uses, and on the `Linter` interface and `@[env_linter]`
attribute of `Batteries/Tactic/Lint/Basic.lean`. The module lives
outside the `Geb`, `GebTests` and `GebLang` namespaces so the linter
does not audit its own metaprogramming code.

The bibliography parser reads the subset of BibTeX the repository's
file is written in: brace-delimited fields, nested braces, `\url`,
and TeX accent commands, which become the letter followed by its
combining mark. BibtexQuery, the parser doc-gen4 uses for its own
References page, is not in `module` form and so cannot be imported
here. The role's output is a core docstring footnote, which Verso's
renderers show as a disclosure whose summary is the key in brackets;
core's Markdown conversion, which doc-gen4 reads, writes it as a
Markdown footnote.

## Tags

axioms, linter, constructive
-/

public meta section

open Lean Meta Batteries.Tactic.Lint

namespace GebMeta

/-- Axioms a constructive development permits: `propext` and
`Quot.sound`. -/
def standardAxioms : NameSet :=
  (({} : NameSet).insert ``propext).insert ``Quot.sound

/-- Exact module names additionally permitted to depend on
`Classical.choice` (and only `Classical.choice`): a module with no
choice-free content of its own left to state, either because it is a
wrapper whose content is packaging or because its subject is the
correspondence between a concept developed here and a concept of an
external Lean library (Batteries, mathlib, CSLib) that itself uses
`Classical.choice`; the `GebTests` parallel of such a module (a test of a
`Classical`-allowed module is itself `Classical`-dependent); the
axiom-linter's own test fixture; and every `GebManual` module holding a
`#doc` document or a bibliography entry, whose document objects depend on
`Classical.choice` through Verso's own definitions, so that a literate
module under `manual/` is held to the strict set while the chapters that
include it are not. Feature branches append the module names their own
such modules occupy. -/
def classicalAllowedModules : NameSet :=
  [`GebTests.Prototypes.AxiomLinterClassicalFixture,
   `GebManual.Bibliography,
   `GebManual.Introduction,
   `GebManual.Root,
   `GebManual.WTypes,
   `Geb.Prototypes.PresheafIRProto.Functor,
   `Geb.Mathlib.Data.PFunctor.Slice.Functor,
   `Geb.Mathlib.Data.PFunctor.Presheaf.Functor,
   `GebTests.Mathlib.Data.PFunctor.Slice.Functor,
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor,
   `Geb.Mathlib.Data.PFunctor.Univariate.Initial,
   `GebTests.Mathlib.Data.PFunctor.Univariate.Initial,
   `Geb.Mathlib.CategoryTheory.DiscreteFibration.Packaged,
   `GebTests.Mathlib.CategoryTheory.DiscreteFibration.Packaged,
   `Geb.Mathlib.CategoryTheory.Grothendieck.Basic,
   `Geb.Mathlib.CategoryTheory.Grothendieck.Functor.Between,
   `Geb.Mathlib.CategoryTheory.Grothendieck.Functor.From,
   `Geb.Mathlib.CategoryTheory.Grothendieck.Functor.To,
   `GebTests.Mathlib.CategoryTheory.Grothendieck.Basic,
   `GebTests.Mathlib.CategoryTheory.Grothendieck.Functor,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
   `Geb.Mathlib.CategoryTheory.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.ElementaryTopos,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Coequalizer,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance,
   `Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos,
   `Geb.Mathlib.CategoryTheory.FinCat.FinCategory,
   `GebTests.Mathlib.CategoryTheory.FinCat.FinCategory,
   `Geb.Prototypes.Computability.TreeScanner.Steps,
   `Geb.Prototypes.Computability.TreeScanner.Bound,
   `GebTests.Prototypes.Computability.TreeScanner.Machine].foldl (·.insert ·)
    ({} : NameSet)

/-- Permitted axioms for a declaration in module `mod`, given the
allowlist `allowed`: the standard set, plus `Classical.choice` exactly
when `mod` is allowlisted. -/
def permittedAxioms (allowed : NameSet) (mod : Name) : NameSet :=
  let extra := if allowed.contains mod then #[``Classical.choice] else #[]
  extra.foldl (·.insert ·) standardAxioms

/-- The elements of `used` not in the `permitted` set. -/
def offendingAxioms (permitted : NameSet) (used : Array Name) : Array Name :=
  used.filter (!permitted.contains ·)

/-- The defining module of `declName`, if resolvable. Returns `none`
when `getModuleIdxFor?` returns `none` (declaration in the current,
not-yet-imported module) or when the module index is out of range;
both cases route the declaration to the strict axiom set. -/
def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => none

/-- Flags a declaration depending on an axiom outside its permitted
set. A declaration in a module listed in `classicalAllowedModules`
additionally permits `Classical.choice` (and only that); every other
axiom (`sorryAx`, `Lean.ofReduceBool`, …) is forbidden everywhere. A
declaration whose module is unresolvable is held to the strict set. -/
@[env_linter] def detectNonstandardAxiom : Batteries.Tactic.Lint.Linter where
  test declName := do
    let mod := (moduleOf? (← getEnv) declName).getD .anonymous
    let permitted := permittedAxioms classicalAllowedModules mod
    let bad := offendingAxioms permitted (← collectAxioms declName)
    if bad.isEmpty then return none
    else return some m!"depends on non-standard axiom(s): {bad.toList}"
  noErrorsFound := "All declarations depend only on permitted axioms."
  errorsFound := "Declarations depend on non-standard axioms."
  isFast := true

/-- One entry of `docs/references.bib`: its category (`article`,
`book`, …), its citation key, and its fields by lower-cased name, the
values with braces and TeX markup removed. -/
structure BibEntry where
  /-- The entry type after `@`, lower-cased. -/
  category : String
  /-- The citation key. -/
  key : String
  /-- The fields, by lower-cased name. -/
  fields : Std.HashMap String String
deriving Inhabited

/-- The bibliography of the repository: the entries of
`docs/references.bib`, keyed by citation key. -/
abbrev Bibliography := Std.HashMap String BibEntry

/-- The bibliography file's path relative to the repository root. -/
def referencesBib : System.FilePath := "docs" / "references.bib"

/-- The combining mark of a TeX accent command: `\'` acute, `` \` ``
grave, `\"` diaeresis, `\^` circumflex, `\~` tilde. -/
def texAccent : Char → Option Char
  | '\'' => some '\u0301'
  | '`' => some '\u0300'
  | '"' => some '\u0308'
  | '^' => some '\u0302'
  | '~' => some '\u0303'
  | _ => none

/-- Removes TeX markup from a field value's characters: braces are
dropped, an accent command becomes its letter followed by the
combining mark, the name of any other command (`\url`, `\emph`) is
dropped leaving its argument, and a backslash before a non-letter is
dropped. -/
partial def cleanChars : List Char → List Char
  | [] => []
  | '{' :: cs | '}' :: cs => cleanChars cs
  | '\\' :: c :: cs =>
    if let some mark := texAccent c then
      match cs.dropWhile (· == '{') with
      | l :: rest => l :: mark :: cleanChars rest
      | [] => []
    else if c.isAlpha then cleanChars (cs.dropWhile Char.isAlpha)
    else c :: cleanChars cs
  | c :: cs => c :: cleanChars cs

/-- Collapses each whitespace run to one space and drops leading
and trailing whitespace. -/
partial def collapseSpace : List Char → List Char
  | [] => []
  | c :: cs =>
    if c.isWhitespace then
      match cs.dropWhile Char.isWhitespace with
      | [] => []
      | rest => ' ' :: collapseSpace rest
    else c :: collapseSpace cs

/-- A field value with TeX markup removed and whitespace runs
collapsed to one space. -/
def cleanValue (raw : List Char) : String :=
  String.ofList (collapseSpace (cleanChars raw) |>.dropWhile Char.isWhitespace)

/-- The characters inside a brace group whose opening brace has been
consumed, and the characters after its closing brace. -/
partial def braceGroup (cs : List Char) (depth : Nat := 1) (acc : List Char := []) :
    Except String (List Char × List Char) :=
  match cs with
  | [] => throw "unterminated brace group"
  | '{' :: rest => braceGroup rest (depth + 1) ('{' :: acc)
  | '}' :: rest =>
    if depth = 1 then pure (acc.reverse, rest) else braceGroup rest (depth - 1) ('}' :: acc)
  | c :: rest => braceGroup rest depth (c :: acc)

/-- The `name = {value}` fields of an entry whose key and comma have
been consumed, up to and including the entry's closing brace. A value
is a brace group or, as a month macro or a number is written, bare up
to the next comma or closing brace. -/
partial def parseFields (cs : List Char) (acc : Std.HashMap String String := {}) :
    Except String (Std.HashMap String String × List Char) := do
  let cs := cs.dropWhile fun c => c.isWhitespace || c == ','
  match cs with
  | [] => throw "unterminated entry"
  | '}' :: rest => pure (acc, rest)
  | _ =>
    let (name, cs) := cs.span fun c => c != '=' && !c.isWhitespace
    match cs.dropWhile Char.isWhitespace with
    | '=' :: cs =>
      match cs.dropWhile Char.isWhitespace with
      | '{' :: cs =>
        let (raw, rest) ← braceGroup cs
        parseFields rest (acc.insert (String.ofList name).toLower (cleanValue raw))
      | cs =>
        -- A bare value, as a month macro or a number is written.
        let (raw, rest) := cs.span fun c => c != ',' && c != '}'
        parseFields rest (acc.insert (String.ofList name).toLower (cleanValue raw))
    | _ => throw s!"expected '=' after field {String.ofList name}"

/-- The entries of a `.bib` file's characters; text outside an entry
is skipped, as BibTeX skips it. -/
partial def parseEntries (cs : List Char) (acc : Array BibEntry := #[]) :
    Except String (Array BibEntry) := do
  match cs with
  | [] => pure acc
  | '@' :: cs =>
    let (category, cs) := cs.span Char.isAlpha
    match cs.dropWhile Char.isWhitespace with
    | '{' :: cs =>
      let (key, cs) := cs.span fun c => c != ',' && c != '}'
      let (fields, rest) ← parseFields (cs.dropWhile (· == ','))
      let entry : BibEntry :=
        { category := (String.ofList category).toLower, key := cleanValue key, fields }
      parseEntries rest (acc.push entry)
    | _ => throw s!"expected '\{' after @{String.ofList category}"
  | _ :: cs => parseEntries cs acc

/-- Parses the text of a `.bib` file into a `Bibliography`. -/
def parseBibliography (contents : String) : Except String Bibliography := do
  let entries ← parseEntries contents.toList
  return entries.foldl (fun bib e => bib.insert e.key e) {}

/-- The nearest ancestor of `dir`, itself included, holding
`referencesBib`: the repository root, when `dir` is inside a
checkout. -/
partial def findRepositoryRoot (dir : System.FilePath) :
    IO (Option System.FilePath) := do
  if ← (dir / referencesBib).pathExists then return some dir
  match dir.parent with
  | some parent => findRepositoryRoot parent
  | none => return none

/-- Bibliographies already parsed in this process, by file path, each
with the modification time of the file it was parsed from, so that an
edit to the file is seen by a long-running process. -/
initialize bibliographyCache :
    IO.Ref (Std.HashMap String (IO.FS.SystemTime × Bibliography)) ← IO.mkRef {}

/-- The bibliography of the repository containing the source file
`file`, with the path it was read from. Parsed once per process and
re-read when the file's modification time changes. -/
def loadBibliography (file : System.FilePath) :
    IO (System.FilePath × Bibliography) := do
  let dir := (← IO.FS.realPath file).parent.getD "."
  let some root ← findRepositoryRoot dir
    | throw <| IO.userError s!"no {referencesBib} in any directory above {file}"
  let path := root / referencesBib
  let modified := (← path.metadata).modified
  if let some (stamp, bib) := (← bibliographyCache.get)[path.toString]? then
    if stamp == modified then return (path, bib)
  match parseBibliography (← IO.FS.readFile path) with
  | .ok bib =>
    bibliographyCache.modify (·.insert path.toString (modified, bib))
    return (path, bib)
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- The names of an `author` or `editor` field, each in `First Last`
order. -/
def BibEntry.names (s : String) : Array String :=
  (s.splitOn " and ").toArray.map fun n =>
    match n.splitOn ", " with
    | [last, first] => s!"{first} {last}"
    | _ => n

/-- The venue of an entry: the first of its `journal`, `booktitle`,
`publisher`, `institution`, `school` and `howpublished` fields. -/
def BibEntry.venue (e : BibEntry) : Option String :=
  ["journal", "booktitle", "publisher", "institution", "school", "howpublished"].findSome?
    (e.fields[·]?)

/-- The link of an entry: its `url`, else its `doi` resolved at
doi.org, else its `eprint` at arXiv. -/
def BibEntry.link (e : BibEntry) : Option String :=
  e.fields["url"]? <|> (e.fields["doi"]?.map (s!"https://doi.org/{·}"))
    <|> (e.fields["eprint"]?.map (s!"https://arxiv.org/abs/{·}"))

open Lean.Doc in
/-- The formatted entry as docstring inlines: authors and year, the
title in quotation marks, the venue emphasised with volume, number and
pages, the link, and the `note` field. -/
def BibEntry.formatted (e : BibEntry) : Array (Inline ElabInline) := Id.run do
  let get n := e.fields[n]?
  let authors := (get "author" <|> get "editor").map (BibEntry.names ·) |>.getD #[]
  let byline := if authors.isEmpty then e.key else ", ".intercalate authors.toList
  let year := (get "year").map (s!" ({·})") |>.getD ""
  let mut out := #[.text s!"{byline}{year}. "]
  if let some title := get "title" then out := out.push (.text s!"“{title}”. ")
  if let some venue := e.venue then
    let volume := (get "volume").map (" " ++ ·) |>.getD ""
    let number := (get "number").map (s!"({·})") |>.getD ""
    let pages := (get "pages").map (s!", pp. {·.replace "--" "–"}") |>.getD ""
    out := out ++ #[.emph #[.text venue], .text s!"{volume}{number}{pages}. "]
  if let some url := e.link then out := out ++ #[.link #[.text url] url, .text ". "]
  if let some note := get "note" then out := out.push (.text s!"{note}.")
  return out

open Lean.Doc Lean.Doc.Syntax

/-- The `{cite}` docstring role: ``{cite}`Key` `` names an entry of
`docs/references.bib` by its citation key, which must exist, and
renders as a footnote whose summary is the key and whose body is the
formatted entry. `scripts/extract-pr.sh` converts it to mathlib's bare
`[Key]` form at extraction. Declared at the root namespace, since a
role name is resolved as a constant is, so that ``{cite}`Key` ``
resolves in a module that opens nothing. -/
@[doc_role]
def _root_.cite (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let key ← match xs with
    | #[stx] =>
      match stx with
      | `(inline|code($s)) => pure s
      | _ => throwErrorAt stx "expected a citation key in a code span"
    | _ => throwError "expected precisely one citation key"
  let (path, bib) ← loadBibliography (← getFileName)
  let some entry := bib[key.getString]?
    | throwErrorAt key m!"unknown citation key `{key.getString}`: not in {path}"
  return .footnote key.getString entry.formatted

end GebMeta
