/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebHost.Authoring
public import GebHost.Json

set_option doc.verso true in
/-!
# Source navigation

Declaration locations and documentation are derived from a manifest's source documents.
Module visibility is computed by the existing elaborator. References in expressions are
located by running its binder-aware renaming with a marked result at the requested atom;
quoted data and locally bound variables therefore do not resolve to global declarations.
An editor supplies snapshots of open documents, so navigation neither saves buffers nor
compiles programs. Locations use the host's one-based byte columns.

## Main definitions

* {lit}`query` — declarations and the declaration denoted at a source position.
* {lit}`run` — the JSON command-line interface, with open-document snapshots on standard input.

## Implementation notes

This service is untrusted. A malformed document or ambiguous module is rejected. A declaration
in an instantiated module navigates to its template's source. Local-variable navigation and
proof-document navigation are outside this interface.

## Tags

authoring, navigation, documentation, source location
-/

set_option doc.verso true

open Geb Geb.Kernel Geb.Kernel.Document

public section

namespace GebHost.Navigation

/-- Byte-character text for the ASCII syntax keywords. Source names and prose remain bytes. -/
def textOf (cs : List Char) : String := String.ofList cs

/-- Whether a byte position lies within a source span, including its endpoints. -/
def contains (s : Locate.Span) (p : Locate.Pos) : Bool :=
  (s.start.line < p.line || (s.start.line == p.line && s.start.col ≤ p.col)) &&
    (p.line < s.stop.line || (p.line == s.stop.line && p.col ≤ s.stop.col))

/-- The undecorated expression of a located expression. -/
def erase (t : Locate.Located) : SExp := t.map (·.2)

/-- The compiler's expression, with notes erased by the document operation. -/
def compilerForm (t : Locate.Located) : SExp :=
  let d : Doc := ⟨[(erase t).map (fun a ↦ (⟨[], false, []⟩, a))], []⟩
  (d.eraseNotes.items.head?.map (·.map (·.2))).getD (slist [])

/-- A declaration and its source presentation. -/
structure Symbol where
  /-- Its qualified source name. -/
  name : Ident
  /-- Its declaring form's keyword. -/
  kind : String
  /-- Its source file. -/
  file : String
  /-- The whole declaration. -/
  span : Locate.Span
  /-- The declaration's name. -/
  selection : Locate.Span
  /-- The declaration's source signature. -/
  signature : List Char
  /-- The comment blocks preceding the declaration. -/
  documentation : List Char

/-- A source document and its located syntax. -/
structure Source where
  /-- Its absolute path. -/
  file : String
  /-- The document, with comments retained. -/
  doc : Doc
  /-- Its located syntax, with notes omitted at block boundaries. -/
  forms : List Locate.Located

/-- The state of a source block's traversal. -/
structure State where
  /-- The compiler's module state. -/
  elaboration : ElabState := ⟨[], [], [], [], [], []⟩
  /-- Declarations in source order. -/
  symbols : List Symbol := []
  /-- Instance prefixes and their source template prefixes. -/
  origins : List (Ident × Ident) := []
  /-- The resolved name at the requested occurrence. -/
  target : Option Ident := none

/-- The marker emitted only by navigation, never by a source atom's renaming. -/
def marker : Ident := "%navigation".toList

/-- The compiler's renaming, with one free occurrence marked by its resolved name. -/
def probe (vis : Visible) (pos : Locate.Pos) (t : Locate.Located)
    (role : Role) (bound : List Ident := []) : Option Ident :=
  let marked := RoseTree.para (fun l rs r bs ↦
    let ordinary := renameStep vis l.2 (rs.map fun (a, f) ↦ (erase a, f)) r bs
    -- The renamer handles a clause's constructor directly, without recursing at that atom.
    let ctor := if r == .clause then
        match l.2, rs with
        | none, [(p, _), _] => if p.label.2.isNone then p.children.head? else none
        | _, _ => none
      else none
    let pattern := ctor.filter (fun c ↦ contains c.label.1 pos) |>.bind (·.label.2)
      |>.bind (vis.lookup ·)
    if let some name := pattern then RoseTree.node (some marker) [atom name]
    else
    if contains l.1 pos then
      match l.2, r with
      | some s, .type | some s, .term =>
        if r == .term && bs.contains s then ordinary
        else match vis.lookup s with
          | some name => RoseTree.node (some marker) [atom name]
          | none => ordinary
      | _, _ => ordinary
    else ordinary) t role bound
  RoseTree.para (fun a rs ↦
    match a, rs with
    | some m, [(n, _)] =>
      if m == marker then n.label else rs.findSome? Prod.snd
    | _, _ => rs.findSome? Prod.snd) marked

/-- Resolve an occurrence in a declaration using the roles its elaborator assigns. -/
def declarationTarget (vis : Visible) (pos : Locate.Pos) (t : Locate.Located) : Option Ident :=
  let lookupAt (e : Locate.Located) (r : Role) (bs : List Ident := []) :=
    if contains e.label.1 pos then probe vis pos e r bs else none
  match t.children with
  | k :: _ :: rest =>
    match k.label.2.map textOf, rest with
    | some "def", [b] => lookupAt b .term
    | some "defn", [ps, res, b] =>
      (lookupAt ps .binders).orElse fun _ ↦ (lookupAt res .type).orElse fun _ ↦
        lookupAt b .term (boundBy (erase ps))
    | some "deftype", [b] | some "defnum", [b] => lookupAt b .type
    | some "data", cs | some "tree-data", cs =>
      cs.findSome? fun c ↦ (c.children.drop 1).findSome? fun f ↦ lookupAt f .type
    | _, _ => none
  | _ => none

/-- A short source signature, with a function's body omitted. -/
def signatureOf (t : Locate.Located) : List Char :=
  let e := erase t
  let e := if e.children.head?.any (isKw · "defn") then
      slist (e.children.take 4)
    else if e.children.head?.any (isKw · "module") then slist (e.children.take 2)
    else e
  let d : Doc := ⟨[e.map (fun a ↦ (⟨[], false, []⟩, a))], []⟩
  printAt (defaultLayout .profile 100 d) d

/-- The source document's comments before a declaration, displayed as source prose. -/
def documentationOf (src : Source) (name : Ident) : List Char :=
  let block (rs : List (SExpr × (Ident → List Line))) (pre : Ident) : List Line :=
    (rs.foldl (fun (pending, found) (t, f) ↦
      if isNote t then (pending ++ t.label.1.lead, found)
      else ([], found ++
        if (declName? t).any (qualify pre · == name) then pending ++ f pre else f pre))
      ([], [])).2
  let render := RoseTree.para (fun l rs pre ↦
    let t := RoseTree.node l (rs.map Prod.fst)
    let own := if (declName? t).any (qualify pre · == name) then l.1.lead else []
    own ++ if headIs kwModule t then
      block rs (qualify pre ((declName? t).getD [])) else [])
  let lines := block (src.doc.items.map fun t ↦ (t, render t)) []
  ['\n'].intercalate (lines.map fun line ↦
    if line.text.head? == some ' ' then line.text.drop 1 else line.text)

/-- Add a named declaration to the index and recognize its name as its own target. -/
def addSymbol (src : Source) (pos : Option Locate.Pos) (pre : Ident) (t : Locate.Located)
    (st : State) : State :=
  match t.children with
  | k :: n :: _ => match k.label.2, n.label.2 with
    | some kw, some name =>
      let name := qualify pre name
      let sym := Symbol.mk name (textOf kw) src.file t.label.1 n.label.1
        (signatureOf t) (documentationOf src name)
      { st with symbols := st.symbols ++ [sym]
                target := if pos.any (contains n.label.1) then some name else st.target }
    | _, _ => st
  | _ => st

/-- Traverse one source form, reusing the compiler's elaboration for imports and exports. -/
def step (depth : Nat) (rec : Source → Option Locate.Pos → Ident → State → Locate.Located →
    Except String State) (src : Source) (pos : Option Locate.Pos) (pre : Ident)
    (st : State) (t : Locate.Located) : Except String State := do
  if Locate.headIs kwNote t then return st
  let e := compilerForm t
  let mut out := st
  if let k :: n :: body := t.children then
    if let some name := n.label.2 then
      if declHeads.contains (k.label.2.getD []) then out := addSymbol src pos pre t out
      if isKw (erase k) "module" then
        let inner := qualify pre name
        let mut nested := { out with
          elaboration := { st.elaboration with exports := [], members := [] } }
        for p in body.filter (Locate.headIs "parameter".toList) do
          if let some sig := p.children[1]? then
            let param := sig.label.2.orElse fun _ ↦ sig.children.head?.bind (·.label.2)
            if let some param := param then
              let elaboration ← declare nested.elaboration param (qualify inner param)
              nested := { nested with elaboration }
        for b in body.filter (!Locate.headIs "parameter".toList ·) do
          nested ← rec src pos inner nested b
        -- Exports may precede their declarations; the elaborator resolves them at block end.
        if let some p := pos then
          for b in body.filter (Locate.headIs "export".toList) do
            for n in b.children.drop 1 do
              if contains n.label.1 p then
                nested := { nested with
                  target := n.label.2.bind (nested.elaboration.vis.lookup ·) }
        out := { out with
          symbols := nested.symbols, origins := nested.origins, target := nested.target }
      else if let some p := pos then
        if out.target.isNone then
          let vis := if isKw (erase k) "data" || isKw (erase k) "tree-data" then
              (name, qualify pre name) :: st.elaboration.vis else st.elaboration.vis
          out := { out with target := declarationTarget vis p t }
      if isKw (erase k) "data" || isKw (erase k) "tree-data" then
        for c in body do
          let ctor := RoseTree.node c.label
            (Locate.atomAt k.label.1 "constructor".toList :: c.children)
          out := addSymbol src pos pre ctor out
  if let some (p, _, as?) := importSpec e then
    if let some (.template params ..) := st.elaboration.reg.lookup p then
      out := { out with origins := out.origins ++ [(pre ++ '/' :: as?.getD p, p)] }
      if let some ppos := pos then
        let args := t.children[1]?.toList.flatMap (·.children.drop 1)
        let target := (params.zip args).findSome? fun (param, arg) ↦
          if contains arg.label.1 ppos then
            probe st.elaboration.vis ppos arg
              (if param.children[1]?.any (·.label.isSome) then .type else .term)
          else none
        out := { out with target := target.orElse fun _ ↦ out.target }
    if let some ppos := pos then
      let path := t.children[1]?.bind fun n ↦
        if n.label.2.isSome then some n else n.children.head?
      if path.any (fun n ↦ contains n.label.1 ppos) then
        out := { out with target := some p }
  if Locate.headIs "export".toList t then
    if let some p := pos then
      for n in t.children.drop 1 do
        if contains n.label.1 p then
          out := { out with target := n.label.2.bind (st.elaboration.vis.lookup ·) }
  let elaboration ← elabAt depth pre st.elaboration e
  return { out with elaboration }

/-- A bounded traversal of nested source modules. -/
def walk (depth : Nat) : Source → Option Locate.Pos → Ident → State → Locate.Located →
    Except String State :=
  Nat.rec (motive := fun _ ↦ Source → Option Locate.Pos → Ident → State → Locate.Located →
    Except String State) (fun _ _ _ _ _ ↦ .error "navigation nesting exhausted")
    (fun n rec ↦ step (n + 1) rec) depth

/-- The source name of a declaration elaborated in a template instance. -/
def sourceName (origins : List (Ident × Ident)) (name : Ident) : Ident :=
  origins.foldr (fun (inst, source) n ↦
    if (inst ++ ['.']).isPrefixOf n then source ++ n.drop inst.length else n) name

/-- A span in the host's one-based byte coordinates. -/
def spanJson (s : Locate.Span) : Lean.Json :=
  Lean.toJson #[s.start.line, s.start.col, s.stop.line, s.stop.col]

/-- A declaration's JSON representation. -/
def Symbol.json (s : Symbol) : Lean.Json := Json.object
  [("name", Lean.toJson (s.name.map Char.toNat)), ("kind", Lean.toJson s.kind),
    ("file", Lean.toJson s.file), ("span", spanJson s.span),
    ("selection", spanJson s.selection), ("signature", Lean.toJson (s.signature.map Char.toNat)),
    ("documentation", Lean.toJson (s.documentation.map Char.toNat))]

/-- Read a manifest's sources, preferring editor snapshots at exactly their absolute paths. -/
def readSources (manifest : System.FilePath) (snapshots : List (String × String)) :
    IO (List Source) := do
  let manifest ← IO.FS.realPath manifest
  let m ← match snapshots.lookup manifest.toString with
    | some text => IO.ofExcept (Manifest.parse (Command.chars text.toUTF8))
    | none => Manifest.read manifest
  (Manifest.sourcePaths manifest m).mapM fun path ↦ do
    let file := (← IO.FS.realPath path).toString
    let bytes ← match snapshots.lookup file with
      | some text => pure text.toUTF8
      | none => IO.FS.readBinFile path
    let text := Command.chars bytes
    let some doc := readDoc text | throw <| IO.userError s!"{file}: malformed source document"
    discard <| IO.ofExcept (notesOf doc)
    let forms ← IO.ofExcept ((Locate.locate text).mapError fun f ↦
      s!"{file}:{f.span.start.line}:{f.span.start.col}: {f.message}")
    return ⟨file, doc, forms⟩

/-- The source declarations and the resolved declaration at an optional source position. -/
def query (manifest : System.FilePath) (file : String) (pos : Locate.Pos)
    (snapshots : List (String × String)) : IO Lean.Json := do
  let sources ← readSources manifest snapshots
  let depth := moduleCount (sources.flatMap fun s ↦ s.forms.map erase) + 1
  let mut st : State := {}
  for src in sources do
    for t in src.forms do
      st ← IO.ofExcept (walk depth src (if src.file == file then some pos else none) [] st t)
  let name := st.target.map (sourceName st.origins)
  let target := name.bind fun n ↦ st.symbols.find? (·.name == n)
  return Json.object [("symbols", Lean.toJson (st.symbols.map Symbol.json)),
    ("target", target.map Symbol.json |>.getD .null)]

/-- Read one JSON navigation request from standard input and write its JSON result. -/
def run (manifest : String) : IO UInt32 := do
  let input ← Json.readInput (← IO.getStdin)
  let json ← IO.ofExcept (Json.parse input)
  let file ← IO.ofExcept (json.getObjValAs? String "file")
  let line ← IO.ofExcept (json.getObjValAs? Nat "line")
  let column ← IO.ofExcept (json.getObjValAs? Nat "column")
  let docs ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "documents")
  let snapshots ← docs.toList.mapM fun d ↦ do
    return (← IO.ofExcept (d.getObjValAs? String "path"),
      ← IO.ofExcept (d.getObjValAs? String "text"))
  IO.println (← query manifest file ⟨line, column⟩ snapshots).compress
  return 0

end GebHost.Navigation
