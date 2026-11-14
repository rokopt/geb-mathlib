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
Local scopes and proof-script continuations locate binders and supply completion spellings.
An editor supplies snapshots of open documents, so navigation neither saves buffers nor
compiles programs. Locations use the host's one-based byte columns.

## Main definitions

* {lit}`query` — declarations and the declaration denoted at a source position.
* {lit}`run` — the JSON command-line interface, with open-document snapshots on standard input.

## Implementation notes

This service is untrusted. Strict requests reject malformed documents and ambiguous modules.
Editor requests may recover readable prefixes, reporting incomplete files and errors separately.
Recovered syntax supplies no compiler input. A declaration in an instantiated module navigates
to its template's source. Proof imports follow the author's dependency order.

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

/-- Whether one byte position follows another. -/
def after (p q : Locate.Pos) : Bool :=
  q.line < p.line || (q.line == p.line && q.col < p.col)

/-- The undecorated expression of a located expression. -/
def erase (t : Locate.Located) : SExp := t.map (·.2)

/-- The authoring spelling with line breaks escaped inside atoms. -/
def atomSpelling : Spelling :=
  { Spelling.profile with plain := fun c ↦ isPlain c && c != '\n' }

/-- Check consecutive UTF-8 sequences with the byte validator. This uses a bounded scan;
constructing a Lean string would pull choice-dependent validity proofs into navigation. -/
def validUTF8 (text : List Char) : Bool := Id.run do
  let bytes := Authoring.bytesOf text
  let mut next := 0
  for i in [:bytes.size] do
    if i == next then
      unless bytes.validateUTF8At i do return false
      let b := (bytes.data[i]?.getD 0).toNat
      next := i + if b < 128 then 1 else if b < 224 then 2 else if b < 240 then 3 else 4
  return next == bytes.size

/-- A single-line atom for insertion into a UTF-8 editor buffer. Arbitrary bytes that do not
form UTF-8 use the profile's hexadecimal escapes. -/
def spellAtom (name : Ident) : List Char :=
  let text := atomSpelling.spell name
  if validUTF8 text then text
  else ({ Spelling.profile with plain := isPlainAscii } : Spelling).spell name

/-- Use the document layout in a UTF-8 buffer, optionally escaping atom line breaks. If raw
atom bytes would produce invalid UTF-8, use ASCII atom spellings throughout the document. -/
def printDocument (doc : Doc) (singleLineAtoms := false) : List Char :=
  let printWith (spelling : Spelling) :=
    let layout := defaultLayout spelling 100 doc
    render spelling (arrangeFrom (fun i ↦ layout.getD i (false, 0)) doc.tokens none 0) ++ ['\n']
  let text := printWith (if singleLineAtoms then atomSpelling else Spelling.profile)
  if validUTF8 text then text
  else printWith { Spelling.profile with plain := isPlainAscii }

/-- An expression in the readable authoring spelling, suitable for editor hover text. -/
def sourceText (e : SExp) : List Char :=
  printDocument ⟨[e.map (fun a ↦ (⟨[], false, []⟩, a))], []⟩

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
  /-- Whether editor recovery was needed for this source or its imports. -/
  incomplete : Bool := false
  /-- Comment locations, including in recovered documents. -/
  comments : List Locate.Span := []
  /-- Errors retained while the editor inspects the readable source. -/
  errors : List String := []

/-- Names available at a source occurrence, with the role that admits them. -/
structure Scope where
  /-- Local declarations, innermost first. -/
  locals : List Symbol := []
  /-- Whether names may be completed here. -/
  active : Bool := true
  /-- Whether this occurrence admits only type names. -/
  types : Bool := false

/-- A local declaration and its written signature. -/
def localSymbol (file : String) (name signature : Locate.Located) (kind := "variable") :
    Option Symbol := name.label.2.map fun n ↦
  ⟨n, kind, file, signature.label.1, name.label.1, sourceText (erase signature), []⟩

/-- Located binders, accepting either one binder or a list of binders. -/
def localBinders (file : String) (t : Locate.Located) : List Symbol :=
  let bs := if t.children.head?.any (·.label.2.isSome) then [t] else t.children
  bs.filterMap fun b ↦ b.children.head?.bind fun n ↦ localSymbol file n b

/-- Scope at an occurrence in a term. Binding scopes follow the module renamer's roles;
quoted data and hole identities contain no references. -/
def termScope (file : String) (pos : Locate.Pos) (t : Locate.Located)
    (role : Role := .term) (locals : List Symbol := []) : Scope :=
  RoseTree.para (fun l (rs : List (Locate.Located × (Role → List Symbol → Scope)))
      (role : Role)
      (locals : List Symbol) ↦ Id.run do
    let locals := if role == .type then locals.filter (·.kind == "object") else locals
    let here : Scope := { locals, active := role != .datum, types := role == .type }
    if role == .datum then return here
    if l.2.isSome then return here
    let childAt (i : Nat) (r : Role) (ls : List Symbol) :=
      rs[i]?.filter (fun c ↦ contains c.1.label.1 pos) |>.map (fun c ↦ c.2 r ls)
    let all (r : Role) (ls : List Symbol) :=
      rs.findSome? fun c ↦ if contains c.1.label.1 pos then some (c.2 r ls) else none
    let nodes := rs.map Prod.fst
    let following (i : Nat) (ls : List Symbol) :=
      if nodes[i]?.any (fun n ↦ after pos n.label.1.stop) then { locals := ls } else here
    let kw := nodes.head?.bind (·.label.2) |>.map textOf |>.getD ""
    if role == .type then return (all .type locals).getD here
    if role == .binders then
      let bs := localBinders file (RoseTree.node l nodes)
      if let some b := bs.find? (contains ·.selection pos) then return { locals := b :: locals }
      return (all .type locals).getD { types := true }
    if role == .clause then
      if nodes.head?.bind (·.children.head?) |>.any (fun c ↦ contains c.label.1 pos) then
        return {}
      let bs := nodes.head?.toList.flatMap fun p ↦
        (p.children.drop 1).filterMap fun n ↦ localSymbol file n n
      if let some b := bs.find? (contains ·.selection pos) then return { locals := b :: locals }
      return (childAt 1 .term (bs.reverse ++ locals)).getD (following 0 (bs.reverse ++ locals))
    if role == .letBindings then
      for (b, f) in rs do
        if contains b.label.1 pos then return f .letBinding locals
      return here
    if role == .letBinding then
      return ((childAt 1 .type []).orElse fun _ ↦ childAt 2 .term locals).getD here
    if kw == "quote" || kw == "hole" || kw == "note" then return { active := false }
    if kw == "datum" then return (childAt 1 .type []).getD { active := false }
    if kw == "lam" then
      let bs := nodes[1]?.toList.flatMap (localBinders file)
      return ((childAt 1 .binders locals).orElse fun _ ↦
        childAt 2 .term (bs.reverse ++ locals)).getD (following 1 (bs.reverse ++ locals))
    if kw == "let" then
      let b := nodes[1]?.bind fun n ↦ localSymbol file n
        (RoseTree.node l (nodes.drop 1 |>.take 2))
      if b.any (contains ·.selection pos) then return { locals := b.toList ++ locals }
      return ((childAt 2 .type []).orElse fun _ ↦ (childAt 3 .term locals).orElse fun _ ↦
        childAt 4 .term (b.toList ++ locals)).getD (following 3 (b.toList ++ locals))
    if kw == "let*" then
      let bs := nodes[1]?.toList.flatMap (·.children)
      let mut scope := locals
      for b in bs do
        let binding := b.children.head?.bind fun n ↦ localSymbol file n
          (RoseTree.node b.label (b.children.take 2))
        if contains b.label.1 pos then
          if binding.any (contains ·.selection pos) then
            return { locals := binding.toList ++ scope }
          -- The binding's value precedes its own scope.
          let child := rs[1]?.map fun c ↦ c.2 .letBindings scope
          return child.getD { locals := scope }
        scope := binding.toList ++ scope
      return (childAt 2 .term scope).getD (following 1 scope)
    if kw == "case" || kw == "cata" then
      let start := if kw == "case" then 2 else 4
      for (c, f) in rs.drop start do
        if contains c.label.1 pos then return f .clause locals
      if kw == "cata" then
        if let some s := (childAt 1 .type []).orElse fun _ ↦ childAt 2 .type [] then return s
      return (childAt (start - 1) .term locals).getD here
    let types := if kw == "foldr" || kw == "lcase" then 2
      else if ["fold", "para", "iter", "nil", "decode"].contains kw then 1 else 0
    for i in List.range types do
      if let some s := childAt (i + 1) .type [] then return s
    return (all .term locals).getD here) t role locals

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
  /-- The local scope of the queried occurrence. -/
  scope : Scope := {}
  /-- The visible spellings at the queried occurrence. -/
  available : Visible := []
  /-- A local declaration selected directly by its source occurrence. -/
  localTarget : Option Symbol := none
  /-- Editor recovery keeps errors separate from the declarations still available. -/
  errors : List String := []

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

/-- The innermost atom at a position. -/
def atomAtPosition (pos : Locate.Pos) : Locate.Located → Option Ident :=
  RoseTree.elim fun l cs ↦
    if contains l.1 pos then l.2.orElse fun _ ↦ cs.findSome? id else none

/-- An atom's full span at or immediately before the caret, for completion replacement. -/
def completionSpan (pos : Locate.Pos) : Locate.Located → Option Locate.Span :=
  RoseTree.elim fun l cs ↦
    if l.2.isSome && (contains l.1 pos ||
        (pos.line == l.1.stop.line && pos.col == l.1.stop.col + 1)) then some l.1
    else cs.findSome? id

/-- The local scope of a declaration's signature or body. -/
def declarationScope (file : String) (pos : Locate.Pos) (t : Locate.Located) : Scope :=
  if Locate.headIs "data".toList t || Locate.headIs "tree-data".toList t then
    ((t.children.drop 2).flatMap (·.children.drop 1) |>.find?
      (fun f ↦ contains f.label.1 pos)).map (fun f ↦ termScope file pos f .type)
        |>.getD { active := false }
  else match t.children with
  | k :: _ :: ps :: res :: body :: [] =>
    if k.label.2 == some "defn".toList then
      if contains ps.label.1 pos then termScope file pos ps .binders
      else if contains res.label.1 pos then termScope file pos res .type
      else if contains body.label.1 pos then
        termScope file pos body .term (localBinders file ps |>.reverse)
      else { active := false }
    else termScope file pos t
  | k :: _ :: body :: [] =>
    termScope file pos body (if k.label.2 == some "deftype".toList then .type else .term)
  | [k, _, ps, res] =>
    if k.label.2 == some "defn".toList then
      if contains ps.label.1 pos then termScope file pos ps .binders
      else if after pos res.label.1.stop then { locals := (localBinders file ps).reverse }
      else termScope file pos res .type
    else { active := false }
  | [k, name] =>
    { active := after pos name.label.1.stop &&
        ["def", "deftype"].contains (textOf (k.label.2.getD [])),
      types := k.label.2 == some "deftype".toList }
  | _ => { active := false }

/-- A short source signature, with a function's body omitted. -/
def signatureOf (t : Locate.Located) : List Char :=
  let e := erase t
  let e := if e.children.head?.any (isKw · "defn") then
      slist (e.children.take 4)
    else if e.children.head?.any (isKw · "module") then slist (e.children.take 2)
    else e
  sourceText e

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
      block rs (qualify pre ((declName? t).getD []))
    else if headIs Authoring.kwProofs t then block (rs.drop 2) [] else [])
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
              let n := if sig.label.2.isSome then sig else sig.children.head?.getD sig
              let sym := (localSymbol src.file n sig
                (if sig.label.2.isSome then "type parameter" else "parameter")).map fun s ↦
                { s with name := qualify inner s.name }
              nested := { nested with elaboration, symbols := nested.symbols ++ sym.toList }
        for b in body.filter (!Locate.headIs "parameter".toList ·) do
          match rec src pos inner nested b with
          | .ok next => nested := next
          | .error e =>
            if src.incomplete then nested := { nested with errors := nested.errors ++ [e] }
            else throw e
        -- Exports may precede their declarations; the elaborator resolves them at block end.
        if let some p := pos then
          for b in body.filter (Locate.headIs "export".toList) do
            for n in b.children.drop 1 do
              if contains n.label.1 p then
                nested := { nested with
                  target := n.label.2.bind (nested.elaboration.vis.lookup ·) }
        out := { out with
          symbols := nested.symbols, origins := nested.origins, target := nested.target,
          scope := nested.scope, available := nested.available, localTarget := nested.localTarget,
          errors := nested.errors }
      else if let some p := pos then
        let vis := if isKw (erase k) "data" || isKw (erase k) "tree-data" then
            (name, qualify pre name) :: st.elaboration.vis else st.elaboration.vis
        if contains t.label.1 p then
          let scope := declarationScope src.file p t
          let localTarget := (atomAtPosition p t).bind fun n ↦
            scope.locals.find? (·.name == n)
          out := { out with scope, available := vis, localTarget }
        if out.target.isNone then
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
  match elabAt depth pre st.elaboration e with
  | .ok elaboration => return { out with elaboration }
  | .error error =>
    if src.incomplete then return { out with errors := out.errors ++ [error] }
    else throw error

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
    ("documentation", Lean.toJson (s.documentation.map Char.toNat)),
    ("insertText", Lean.toJson ((spellAtom s.name).map Char.toNat))]

/-- Completion spellings resolved through the same visibility table as navigation. -/
def completions (st : State) : List Symbol :=
  if !st.scope.active then [] else
    let globals := st.available.filterMap fun (spelling, name) ↦
      (st.symbols.find? (·.name == sourceName st.origins name)).map fun s ↦
        { s with name := spelling }
    let globals := if st.scope.types then globals.filter fun s ↦
      ["deftype", "data", "tree-data", "type parameter"].contains s.kind else globals
    (st.scope.locals ++ globals).foldl (fun out s ↦
      if out.any (·.name == s.name) then out else out ++ [s]) []

/-- The names introduced by the outer binders and assumptions of a proof statement. -/
def statementNames (file : String) (formulas := false) : Locate.Located → List Symbol :=
  RoseTree.para fun _ rs ↦
    let kw := rs.head?.bind (·.1.label.2) |>.map textOf |>.getD ""
    let arg := rs[1]?.map Prod.fst
    let tail := rs.getLast?.map Prod.snd |>.getD []
    if kw == "internal" then
      tail ++ arg.toList.flatMap fun a ↦
        a.children.filterMap fun n ↦ localSymbol file n n "object"
    else if kw == "forall" then tail ++ arg.toList.flatMap (localBinders file)
    else if kw == (if formulas then "assuming" else "implies") then
      tail ++ (rs.drop 1 |>.dropLast).filterMap fun (h, _) ↦
        h.children.head?.bind fun n ↦ localSymbol file n h "hypothesis"
    else []

/-- Names visible in a proof statement, internal term or script. Script binders are scoped to
their continuations; branch binders do not escape to sibling scripts. -/
def proofScope (file : String) (pos : Locate.Pos) (t : Locate.Located)
    (locals : List Symbol) (statement := false) (formulas := false) : Scope :=
  RoseTree.para (fun l (rs : List (Locate.Located × (Bool → List Symbol → Scope)))
      (statement : Bool)
      (locals : List Symbol) ↦ Id.run do
    let nodes := rs.map Prod.fst
    let kw := nodes.head?.bind (·.label.2) |>.map textOf |>.getD ""
    let here : Scope := { locals := locals }
    let childAt (i : Nat) (ls : List Symbol) :=
      rs[i]?.filter (fun c ↦ contains c.1.label.1 pos) |>.map fun c ↦
        c.2 (statement && ["internal", "forall",
          if formulas then "assuming" else "implies"].contains kw) ls
    let namesAt (i : Nat) (kind := "variable") :=
      nodes[i]?.toList.flatMap fun ns ↦
        (if ns.label.2.isSome then [ns] else ns.children).filterMap fun n ↦
          localSymbol file n n kind
    let boundAt (i : Nat) := nodes[i]?.toList.flatMap (localBinders file)
    let without (i : Nat) := locals.filter fun s ↦
      !(nodes[i]?.any (·.label.2 == some s.name)) || s.kind == "hypothesis" || s.kind == "object"
    let mut added : List Symbol := []
    let mut body : List Nat := []
    let mut outer := locals
    if statement && kw == "internal" then
      added := namesAt 1 "object"; body := [2]
    else if (statement && kw == "forall") || kw == "lam" then
      added := boundAt 1; body := [2]
    else if statement && kw == (if formulas then "assuming" else "implies") then
      added := (nodes.drop 1 |>.dropLast).filterMap fun h ↦
        h.children.head?.bind fun n ↦ localSymbol file n h "hypothesis"
      body := [nodes.length - 1]
    else if kw == "extensionality" || kw == "all-intro" || kw == "assume" then
      added := namesAt 1 (if kw == "assume" then "hypothesis" else "variable")
      body := [2]
    else if kw == "and-elim" then added := namesAt 2 "hypothesis"; body := [3]
    else if kw == "unfold-hypothesis" then added := namesAt 2 "hypothesis"; body := [3]
    else if kw == "imp-elim" || kw == "all-elim" then
      added := namesAt 3 "hypothesis"; body := [4]
    else if kw == "exists-elim" then
      added := (namesAt 2).mapIdx fun i s ↦
        if i == 1 then { s with kind := "hypothesis" } else s
      body := [3]
    else if kw == "or-elim" then
      let branches := namesAt 2 "hypothesis"
      if let some b := branches.find? (contains ·.selection pos) then
        return { locals := b :: locals }
      for i in [0, 1] do
        if let some s := childAt (i + 3) (branches[i]?.toList ++ locals) then return s
    else if kw == "generalize" then added := boundAt 1; body := [3]
    else if kw == "induction" || kw == "tree-induction" then
      added := (namesAt 2).mapIdx fun i s ↦
        if i == 2 then { s with kind := "hypothesis" } else s
      outer := without 1
      body := [if kw == "induction" then 4 else 3]
      if kw == "induction" then
        if let some s := childAt 3 outer then return s
    else if kw == "cases" || kw == "sum-cases" || kw == "tree-cases" then
      added := namesAt 2
      body := if kw == "sum-cases" then [3, 4] else [4]
    else if kw == "revert-cases" then added := namesAt 3; body := [5]
    else if kw == "instances" || kw == "child-hypotheses" then
      let groups := nodes[3]?.toList.flatMap (·.children)
      let insts := if kw == "child-hypotheses" then groups.flatMap (·.children) else groups
      added := insts.filterMap fun i ↦
        i.children.head?.bind fun n ↦ localSymbol file n i "hypothesis"
      body := [4]
    else if kw == "list-rec" || kw == "rose-rec" then
      added := namesAt 2; body := [3]
    else if kw == "fold-induction" || kw == "tree-fold-induction" then
      added := namesAt 2; outer := without 1; body := [3]
    if let some b := added.find? (contains ·.selection pos) then return { locals := b :: locals }
    if (statement && kw == "forall") || kw == "lam" || kw == "generalize" then
      if let some binders := nodes[1]?.filter (fun b ↦ contains b.label.1 pos) then
        return termScope file pos binders .binders locals
    for i in body do
      if let some s := childAt i (added.reverse ++ outer) then return s
    if kw == "quote" || kw == "hole" || kw == "note" then return { active := false }
    if kw == "kernel" then
      return (nodes[1]?.map fun n ↦ termScope file pos n .term locals).getD here
    if kw == "let" || kw == "let*" then
      return termScope file pos (RoseTree.node l nodes) .term locals
    return (rs.findSome? fun c ↦
      if contains c.1.label.1 pos then some (c.2 false locals) else none).getD here)
    t statement locals

/-- Inspect a theorem before adding it to the declarations available to later theorems. -/
def proofDeclaration (src : Source) (pos : Option Locate.Pos) (st : State)
    (t : Locate.Located) : State := Id.run do
  let mut out := st
  if !Locate.headIs Authoring.kwTheorem t then return out
  if let some p := pos then
    if contains t.label.1 p then
      let formulas := (src.forms.find? (Locate.headIs Authoring.kwProofs)).any fun doc ↦
        (doc.children[1]?.bind (·.label.2)) == some ['5'] &&
          t.children[2]?.any (Locate.headIs "internal".toList)
      let locals := t.children[2]?.toList.flatMap (statementNames src.file formulas)
      let scope := if t.children[3]?.any (contains ·.label.1 p) then
          proofScope src.file p (t.children[3]?.getD t) locals false formulas
        else proofScope src.file p (t.children[2]?.getD t) [] true formulas
      let name := atomAtPosition p t
      let available := (st.elaboration.out.filterMap fun e ↦
        e.children[1]?.bind (·.label)).map (fun n ↦ (n, n)) ++
        (st.symbols.filter (·.kind == "theorem")).map (fun s ↦ (s.name, s.name))
      let localTarget := if scope.active then
          name.bind (fun n ↦ scope.locals.find? (·.name == n)) else none
      let target := if scope.active then name.bind (available.lookup ·) else none
      out := { out with scope, available, localTarget, target }
  return addSymbol src pos [] t out

/-- Read bytes from the editor snapshot, or from the file when it has no snapshot. -/
def sourceBytes (path : System.FilePath) (snapshots : List (String × String)) : IO ByteArray := do
  let file := (← IO.FS.realPath path).toString
  match snapshots.lookup file with
  | some text => pure text.toUTF8
  | none => IO.FS.readBinFile path

/-- Read one source with its locations, optionally recovering an unfinished prefix for editing. -/
def readSource (path : System.FilePath) (snapshots : List (String × String))
    (recover : Bool) : IO Source := do
  let file := (← IO.FS.realPath path).toString
  let text := Command.chars (← sourceBytes path snapshots)
  let scan := (text ++ ['\n']).foldl Locate.scanStep Locate.Scan.init
  let comments := (scan.lex.toks.zip scan.spans).filterMap fun (tok, span) ↦
    match tok with
    | .comment _ _ => some span
    | _ => none
  match readDoc text, Locate.locate text with
  | some doc, .ok forms =>
    let errors ← match notesOf doc with
      | .ok _ => pure []
      | .error e => if recover then pure [e] else throw <| IO.userError e
    return { file, doc, forms, comments, errors, incomplete := !errors.isEmpty }
  | _, _ =>
    unless recover do throw <| IO.userError s!"{file}: malformed source document"
    return { file, doc := ⟨[], []⟩, forms := Locate.recover text, incomplete := true, comments }

/-- Read a manifest's sources, preferring editor snapshots at exactly their absolute paths. -/
def readSources (manifest : System.FilePath) (snapshots : List (String × String))
    (recover := false) : IO (List Source) := do
  let manifest ← IO.FS.realPath manifest
  let m ← match snapshots.lookup manifest.toString with
    | some text => IO.ofExcept (Manifest.parse (Command.chars text.toUTF8))
    | none => Manifest.read manifest
  (Manifest.sourcePaths manifest m).mapM fun path ↦ readSource path snapshots recover

/-- Read a proof import closure using the author's import parser and path rules, with snapshots.
Documents are returned in dependency order, as the proof runner consumes them. -/
def readProofSources (proofs : String) (snapshots : List (String × String)) (recover : Bool) :
    IO (List Source) := do
  if proofs.isEmpty then return []
  let mut seen : List (Source × List String) := []
  let mut work := [proofs]
  for _ in [0:Authoring.documentLimit] do
    let p :: rest := work | break
    work := rest
    let file := (← IO.FS.realPath p).toString
    if seen.any (·.1.file == file) then continue
    let mut src ← try readSource file snapshots recover catch e =>
      unless recover do throw e
      pure { file, doc := ⟨[], []⟩, forms := [], incomplete := true, errors := [e.toString] }
    let doc : Doc := ⟨src.forms.map fun t ↦ (erase t).map (⟨⟨[], false, []⟩, ·⟩), []⟩
    let imports ← try
      (← IO.ofExcept (Authoring.importsOf doc)).mapM fun s ↦ do
        unless Manifest.validSource s do throw <| IO.userError "invalid proof import path"
        return (← IO.FS.realPath (Manifest.resolve file s)).toString
      catch e =>
        unless recover do throw e
        src := { src with incomplete := true, errors := src.errors ++ [e.toString] }
        pure []
    seen := seen ++ [(src, imports)]
    work := imports ++ work
  unless work.isEmpty do throw <| IO.userError "proof import limit exceeded"
  let mut ordered : List Source := []
  for _ in seen do
    for (src, imports) in seen do
      if !ordered.any (·.file == src.file) &&
          imports.all (fun p ↦ ordered.any (·.file == p)) then
        ordered := ordered ++ [src]
  unless ordered.length == seen.length do
    unless recover do throw <| IO.userError "cyclic proof imports"
    ordered := ordered ++ (seen.filter fun s ↦ !ordered.any (·.file == s.1.file)).map
      fun (src, _) ↦
        { src with incomplete := true, errors := src.errors ++ ["cyclic proof imports"] }
  return ordered

/-- The source declarations and the resolved declaration at an optional source position. -/
def query (manifest : System.FilePath) (file : String) (pos : Locate.Pos)
    (snapshots : List (String × String)) (proofs := "") (recover := false) : IO Lean.Json := do
  let sources ← readSources manifest snapshots recover
  let (proofSources, proofErrors) ← try
      pure (← readProofSources proofs snapshots recover, [])
    catch e =>
      unless recover do throw e
      pure ([], [e.toString])
  let atomSpan := ((sources ++ proofSources).filter (·.file == file)).findSome? fun src ↦
    src.forms.findSome? (completionSpan pos)
  let pos := match atomSpan with
    | some span => if contains span pos then pos else span.stop
    | none => pos
  let depth := moduleCount (sources.flatMap fun s ↦ s.forms.map erase) + 1
  let mut st : State := { errors := proofErrors ++ (sources ++ proofSources).flatMap (·.errors) }
  let mut incomplete := (sources ++ proofSources).filter (·.incomplete) |>.map (·.file)
  for src in sources do
    let previousErrors := st.errors.length
    for t in src.forms do
      match walk depth { src with incomplete := recover || src.incomplete }
          (if src.file == file then some pos else none) [] st t with
      | .ok next => st := next
      | .error e =>
        if recover then st := { st with errors := st.errors ++ [s!"{src.file}: {e}"] }
        else throw <| IO.userError e
    if st.errors.length != previousErrors && !incomplete.contains src.file then
      incomplete := incomplete ++ [src.file]
  for src in proofSources do
    for root in src.forms.filter (Locate.headIs Authoring.kwProofs) do
      for t in root.children.drop 2 do
        st := proofDeclaration src (if src.file == file then some pos else none) st t
  if (sources ++ proofSources).any (fun src ↦ src.file == file &&
      src.comments.any (contains · pos)) then
    st := { st with scope := { active := false }, localTarget := none, target := none }
  let name := st.target.map (sourceName st.origins)
  let target := st.localTarget.orElse fun _ ↦ name.bind fun n ↦ st.symbols.find? (·.name == n)
  return Json.object [("symbols", Lean.toJson (st.symbols.map Symbol.json)),
    ("target", target.map Symbol.json |>.getD .null),
    ("completions", Lean.toJson ((completions st).map Symbol.json)),
    ("atomSpan", atomSpan.map spanJson |>.getD .null),
    ("incomplete", Lean.toJson incomplete),
    ("errors", Lean.toJson st.errors)]

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
  let proofs := (json.getObjValAs? String "proofs").toOption.getD ""
  let recover := (json.getObjValAs? Bool "recover").toOption.getD false
  IO.println (← query manifest file ⟨line, column⟩ snapshots proofs recover).compress
  return 0

end GebHost.Navigation
