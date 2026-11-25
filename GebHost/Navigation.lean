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
* {lit}`run` — one JSON request with open-document snapshots on standard input.
* {lit}`serve` — successive requests sharing parsed documents and the unchanged index prefix.

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
  /-- Preceding prose indexed by qualified source name. -/
  prose : List (Ident × List Char) := []
  /-- Bytes identifying this revision of the parsed document. -/
  bytes : ByteArray := .empty
  /-- Module forms counted toward the elaborator's depth bound. -/
  modules : Nat := 0
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
quoted data and hole identities contain no references. A name declared with type parameters is
followed by as many types as a function gives its spelling, in a term and in a pattern. -/
def termScope (file : String) (pos : Locate.Pos) (t : Locate.Located)
    (role : Role := .term) (locals : List Symbol := []) (types : Ident → Nat := fun _ ↦ 0) :
    Scope :=
  RoseTree.para (fun l (rs : List (Locate.Located × (Role → List Symbol → Scope)))
      (role : Role)
      (locals : List Symbol) ↦ Id.run do
    let locals := if role == .type then locals.filter (·.kind == "object") else locals
    let here : Scope := { locals, active := role != .datum, types := role == .type }
    if role == .datum then return here
    if l.2.isSome then return here
    let typesOf (n : Option Locate.Located) : Nat := ((n.bind (·.label.2)).map types).getD 0
    if role == .pattern then
      return ((rs.drop 1 |>.take (typesOf (rs.head?.map Prod.fst))).findSome? fun c ↦
        if contains c.1.label.1 pos then some (c.2 .type []) else none).getD { active := false }
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
      let arity := typesOf (nodes.head?.bind (·.children.head?))
      if nodes.head?.toList.flatMap (·.children.drop 1 |>.take arity) |>.any
          (fun n ↦ contains n.label.1 pos) then
        return (rs.head?.map fun c ↦ c.2 .pattern locals).getD {}
      let fields := nodes.head?.toList.flatMap fun p ↦ p.children.drop (1 + arity)
      let marker (n : Locate.Located) := n.label.2 == some ['&'] || n.label.2 == some ['_']
      if fields.any (fun n ↦ marker n && contains n.label.1 pos) then
        return { active := false }
      let bs := (fields.filter fun n ↦ !marker n).filterMap fun n ↦ localSymbol file n n
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
    let count := if kw == "foldr" || kw == "lcase" then 2
      else if ["fold", "para", "iter", "nil", "decode"].contains kw then 1
      else if nodes.head?.any fun h ↦ h.label.2.any fun s ↦ locals.any (·.name == s) then 0
      else typesOf nodes.head?
    for i in List.range count do
      if let some s := childAt (i + 1) .type [] then return s
    return (all .term locals).getD here) t role locals

/-- The lexical information determined by a cursor position. -/
structure Focus where
  /-- The resolved qualified name. -/
  target : Option Ident := none
  /-- The local scope for completion. -/
  scope : Scope := {}
  /-- The global spellings visible in that scope. -/
  available : Visible := []
  /-- A selected local binder. -/
  localTarget : Option Symbol := none

/-- A source region and the resolver in scope there. Smaller regions take precedence. -/
structure Site (α : Type) where
  /-- The declaring file. -/
  file : String
  /-- The region of this resolver. -/
  span : Locate.Span
  /-- Resolve a position within the region. -/
  resolve : Locate.Pos → α

/-- The position-independent declaration index and the module state for its continuation. -/
structure State where
  /-- The compiler's module state. -/
  elaboration : ElabState := {}
  /-- Declarations in source order. -/
  symbols : List Symbol := []
  /-- The first declaration of each name, including during recovery from duplicates. -/
  byName : Std.TreeMap.Raw String Symbol := ∅
  /-- Instance prefixes and their source template prefixes. -/
  origins : List (Ident × Ident) := []
  /-- Resolvers at source occurrences, most specific first. -/
  sites : List (Site Focus) := []
  /-- Explicit binding, import and export targets within those scopes. -/
  targets : List (Site (Option Ident)) := []
  /-- Errors retained during recovery. -/
  errors : List String := []

/-- Insert a declaration in both the source outline and the name lookup table. -/
def State.withSymbol (st : State) (s : Symbol) : State :=
  { st with symbols := st.symbols ++ [s], byName := st.byName.insertIfNew (String.ofList s.name) s }

/-- The marker emitted only by navigation, never by a source atom's renaming. -/
def marker : Ident := "%navigation".toList

/-- The compiler's renaming, with one free occurrence marked by its resolved name. -/
def probe (vis : Visible) (polys : Polys) (pos : Locate.Pos) (t : Locate.Located)
    (role : Role) (bound : List Ident := []) : Option Ident :=
  let marked := RoseTree.para (fun l rs r bs ↦
    let ordinary := renameStep vis polys l.2 (rs.map fun (a, f) ↦ (erase a, f)) r bs
    -- The renamer handles a clause's constructor directly, without recursing at that atom, and
    -- likewise the name that begins a use of a declaration with type parameters.
    let ctor := if r == .clause then
        match l.2, rs with
        | none, [(p, _), _] => if p.label.2.isNone then p.children.head? else none
        | _, _ => none
      else if r == .term || r == .type then
        match l.2, rs with
        | none, (h, _) :: _ => if r == .term && h.label.2.any bs.contains then none else some h
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
def declarationTarget (vis : Visible) (polys : Polys) (pos : Locate.Pos) (t : Locate.Located) :
    Option Ident :=
  let lookupAt (e : Locate.Located) (r : Role) (bs : List Ident := []) :=
    if contains e.label.1 pos then probe vis polys pos e r bs else none
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
def declarationScope (file : String) (pos : Locate.Pos) (t : Locate.Located)
    (types : Ident → Nat := fun _ ↦ 0) : Scope :=
  let scope (e : Locate.Located) (r : Role := .term) (ls : List Symbol := []) : Scope :=
    termScope file pos e r ls types
  if Locate.headIs "data".toList t || Locate.headIs "tree-data".toList t then
    ((t.children.drop 2).flatMap (·.children.drop 1) |>.find?
      (fun f ↦ contains f.label.1 pos)).map (fun f ↦ scope f .type)
        |>.getD { active := false }
  else match t.children with
  | k :: _ :: ps :: res :: body :: [] =>
    if k.label.2 == some "defn".toList then
      if contains ps.label.1 pos then scope ps .binders
      else if contains res.label.1 pos then scope res .type
      else if contains body.label.1 pos then
        scope body .term (localBinders file ps |>.reverse)
      else { active := false }
    else scope t
  | k :: _ :: body :: [] =>
    scope body (if k.label.2 == some "deftype".toList then .type else .term)
  | [k, _, ps, res] =>
    if k.label.2 == some "defn".toList then
      if contains ps.label.1 pos then scope ps .binders
      else if after pos res.label.1.stop then { locals := (localBinders file ps).reverse }
      else scope res .type
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

/-- Gather preceding comments in document order, including comments attached through notes. -/
def documentProse (doc : Doc) : List (Ident × List Char) :=
  let block (rs : List (SExpr × (Ident → List (Ident × List Char)))) (pre : Ident) :=
    (rs.foldl (fun (pending, found) (t, nested) ↦
      if isNote t then (pending ++ t.label.1.lead, found) else
        let lines := pending ++ t.label.1.lead
        let own := if lines.isEmpty then [] else (declName? t).toList.map fun n ↦
          (qualify pre n, ['\n'].intercalate (lines.map fun line ↦
            if line.text.head? == some ' ' then line.text.drop 1 else line.text))
        ([], found ++ own ++ nested pre)) ([], [])).2
  let render := RoseTree.para (fun l rs pre ↦
    let t := RoseTree.node l (rs.map Prod.fst)
    if headIs kwModule t then block rs (qualify pre ((declName? t).getD []))
    else if headIs Authoring.kwProofs t then block (rs.drop 2) [] else [])
  block (doc.items.map fun t ↦ (t, render t)) []

/-- Add a named declaration to the index and recognize its name as its own target. -/
def addSymbol (src : Source) (pre : Ident) (t : Locate.Located) (st : State) : State :=
  match t.children with
  | k :: n :: _ => match k.label.2, Locate.declNameAtom n with
    | some kw, some a =>
      let name := qualify pre (a.label.2.getD [])
      let sym := Symbol.mk name (textOf kw) src.file t.label.1 a.label.1
        (signatureOf t) (src.prose.lookup name |>.getD [])
      { st.withSymbol sym with targets := ⟨src.file, a.label.1, fun _ ↦ some name⟩ :: st.targets }
    | _, _ => st
  | _ => st

/-- Traverse one source form, reusing the compiler's elaboration for imports and exports. -/
def step (depth : Nat) (rec : Source → Ident → State → Locate.Located →
    Except String State) (src : Source) (pre : Ident)
    (st : State) (t : Locate.Located) : Except String State := do
  if Locate.headIs kwNote t then return st
  let e := compilerForm t
  let mut out := st
  if let k :: n :: body := t.children then
    if let some name := (Locate.declNameAtom n).bind (·.label.2) then
      if !isKw (erase k) "module" then
        -- A declaration's type parameters are declared under its name, in scope in it alone.
        let params := if n.label.2.isNone then n.children.drop 1 else []
        for p in params do
          if let some sym := localSymbol src.file p p "type parameter" then
            let sym := { sym with name := qualify (qualify pre name) sym.name }
            out := { out.withSymbol sym with
              targets := ⟨src.file, p.label.1, fun _ ↦ some sym.name⟩ :: out.targets }
        let own := params.filterMap fun p ↦
          p.label.2.map fun a ↦ (a, qualify (qualify pre name) a)
        let vis := own ++ if isKw (erase k) "data" || isKw (erase k) "tree-data" then
            (name, qualify pre name) :: st.elaboration.vis else st.elaboration.vis
        let polys := st.elaboration.polys
        let types (s : Ident) : Nat :=
          match (vis.lookup s).bind fun fl ↦ polys.lookup fl with
          | some ref => ref.arity
          | none => 0
        let focus (p : Locate.Pos) : Focus :=
          let scope := declarationScope src.file p t types
          let localTarget := (atomAtPosition p t).bind fun atom ↦
            scope.locals.find? (·.name == atom)
          ⟨declarationTarget vis polys p t, scope, vis, localTarget⟩
        out := { out with sites := ⟨src.file, t.label.1, focus⟩ :: out.sites }
      if declHeads.contains (k.label.2.getD []) then out := addSymbol src pre t out
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
              nested := sym.toList.foldl State.withSymbol { nested with elaboration }
        for b in body.filter (!Locate.headIs "parameter".toList ·) do
          match rec src inner nested b with
          | .ok next => nested := next
          | .error e =>
            if src.incomplete then nested := { nested with errors := nested.errors ++ [e] }
            else throw e
        -- Exports may precede their declarations; the elaborator resolves them at block end.
        let vis := nested.elaboration.vis
        for b in body.filter (Locate.headIs "export".toList) do
          for n in b.children.drop 1 do
            nested := { nested with targets := ⟨src.file, n.label.1, fun _ ↦
              n.label.2.bind (vis.lookup ·)⟩ :: nested.targets }
        out := { out with
          symbols := nested.symbols, byName := nested.byName, origins := nested.origins,
          sites := nested.sites, targets := nested.targets, errors := nested.errors }
      if isKw (erase k) "data" || isKw (erase k) "tree-data" then
        for c in body do
          let ctor := RoseTree.node c.label
            (Locate.atomAt k.label.1 "constructor".toList :: c.children)
          out := addSymbol src pre ctor out
  if let some (p, _, as?) := importSpec e then
    if let some (.template params ..) := st.elaboration.reg.lookup p then
      out := { out with origins := out.origins ++ [(pre ++ '/' :: as?.getD p, p)] }
      let vis := st.elaboration.vis
      for (param, arg) in params.zip (t.children[1]?.toList.flatMap (·.children.drop 1)) do
        let role := if param.children[1]?.any (·.label.isSome) then Role.type else Role.term
        out := { out with targets := ⟨src.file, arg.label.1, fun pos ↦
          probe vis st.elaboration.polys pos arg role⟩ :: out.targets }
    if let some n := t.children[1]?.bind fun n ↦
        if n.label.2.isSome then some n else n.children.head? then
      out := { out with targets := ⟨src.file, n.label.1, fun _ ↦ some p⟩ :: out.targets }
  if Locate.headIs "export".toList t then
    let vis := st.elaboration.vis
    for n in t.children.drop 1 do
      out := { out with targets := ⟨src.file, n.label.1, fun _ ↦
        n.label.2.bind (vis.lookup ·)⟩ :: out.targets }
  match elabAt depth pre st.elaboration e with
  | .ok elaboration => return { out with elaboration }
  | .error error =>
    if src.incomplete then return { out with errors := out.errors ++ [error] }
    else throw error

/-- A bounded traversal of nested source modules. -/
def walk (depth : Nat) : Source → Ident → State → Locate.Located →
    Except String State :=
  Nat.rec (motive := fun _ ↦ Source → Ident → State → Locate.Located →
    Except String State) (fun _ _ _ _ ↦ .error "navigation nesting exhausted")
    (fun n rec ↦ step (n + 1) rec) depth

/-- The source name of a declaration elaborated in a template instance. -/
def sourceName (origins : List (Ident × Ident)) (name : Ident) : Ident :=
  origins.foldr (fun (inst, source) n ↦
    if (inst ++ ['.']).isPrefixOf n then source ++ n.drop inst.length else n) name

/-- A span in the host's one-based byte coordinates. -/
def spanJson (s : Locate.Span) : Lean.Json :=
  Lean.toJson #[s.start.line, s.start.col, s.stop.line, s.stop.col]

/-- Encode only the fields consumed by the requested operation. -/
def Symbol.json (s : Symbol) (operation := "all") : Lean.Json := Id.run do
  let mut fields := [("name", Lean.toJson (s.name.map Char.toNat)), ("kind", Lean.toJson s.kind)]
  unless operation == "completion" do
    fields := fields ++ [("file", Lean.toJson s.file), ("span", spanJson s.span),
      ("selection", spanJson s.selection)]
  unless operation == "workspace" || operation == "document" do
    fields := fields ++ [("signature", Lean.toJson (s.signature.map Char.toNat)),
      ("documentation", Lean.toJson (s.documentation.map Char.toNat))]
  if operation == "all" || operation == "completion" then
    fields := fields ++ [("insertText", Lean.toJson ((spellAtom s.name).map Char.toNat))]
  return Json.object fields

/-- Completion spellings resolved through the same visibility table as navigation. -/
def completions (st : State) (focus : Focus) : List Symbol :=
  if !focus.scope.active then [] else
    let globals := focus.available.filterMap fun (spelling, name) ↦
      (st.byName.get? (String.ofList (sourceName st.origins name))).map fun s ↦
        { s with name := spelling }
    let globals := if focus.scope.types then globals.filter fun s ↦
      ["deftype", "data", "tree-data", "type parameter"].contains s.kind else globals
    (focus.scope.locals ++ globals).foldl (fun out s ↦
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
    else if kw == "reduce-hypothesis" then added := namesAt 2 "hypothesis"; body := [5]
    else if kw == "obtain" then added := namesAt 1 "hypothesis"; body := [nodes.length - 1]
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
def proofDeclaration (src : Source) (st : State) (t : Locate.Located) : State := Id.run do
  unless Locate.headIs Authoring.kwTheorem t do return st
  let globals := st.elaboration.out
  let symbols := st.symbols
  let focus (p : Locate.Pos) : Focus := Id.run do
    let names := globals.filterMap fun e ↦ e.children[1]?.bind (·.label)
    let available := names.map (fun n ↦ (n, n)) ++
      (symbols.filter (·.kind == "theorem")).map (fun s ↦ (s.name, s.name))
    let formulas := (src.forms.find? (Locate.headIs Authoring.kwProofs)).any fun doc ↦
      ((doc.children[1]?.bind (·.label.2)) == some ['5'] ||
        (doc.children[1]?.bind (·.label.2)) == some ['6']) &&
        t.children[2]?.any (Locate.headIs "internal".toList)
    let locals := t.children[2]?.toList.flatMap (statementNames src.file formulas)
    let scope := if t.children[3]?.any (contains ·.label.1 p) then
        proofScope src.file p (t.children[3]?.getD t) locals false formulas
      else proofScope src.file p (t.children[2]?.getD t) [] true formulas
    let name := atomAtPosition p t
    let localTarget := if scope.active then
        name.bind (fun n ↦ scope.locals.find? (·.name == n)) else none
    let target := if scope.active then name.bind (available.lookup ·) else none
    return ⟨target, scope, available, localTarget⟩
  return addSymbol src [] t { st with sites := ⟨src.file, t.label.1, focus⟩ :: st.sites }

/-- Read bytes from the editor snapshot, or from the file when it has no snapshot. -/
def sourceBytes (file : String) (snapshots : List (String × String)) : IO ByteArray := do
  match snapshots.lookup file with
  | some text => pure text.toUTF8
  | none => IO.FS.readBinFile file

/-- Read one source with its locations, optionally recovering an unfinished prefix for editing. -/
def parseSource (file : String) (bytes : ByteArray) (recover : Bool) : IO Source := do
  let text := Command.chars bytes
  let scan := (text ++ ['\n']).foldl Locate.scanStep Locate.Scan.init
  let comments := (scan.lex.toks.zip scan.spans).filterMap fun (tok, span) ↦
    match tok with
    | .comment _ _ => some span
    | _ => none
  let src : Source ← match readDoc text, Locate.locate text with
  | some doc, .ok forms =>
    let errors ← match notesOf doc with
      | .ok _ => pure []
      | .error e => if recover then pure [e] else throw <| IO.userError e
    pure { file, doc, forms, comments, errors, incomplete := !errors.isEmpty }
  | _, _ =>
    unless recover do throw <| IO.userError s!"{file}: malformed source document"
    pure { file, doc := ⟨[], []⟩, forms := Locate.recover text, incomplete := true, comments }
  let modules := moduleCount (src.forms.map erase)
  return { src with bytes, modules, prose := documentProse src.doc }

/-- Read a manifest's sources, preferring editor snapshots at exactly their absolute paths. -/
def sourcePaths (manifest : System.FilePath) (snapshots : List (String × String)) :
    IO (List System.FilePath) := do
  let manifest ← IO.FS.realPath manifest
  let m ← match snapshots.lookup manifest.toString with
    | some text => IO.ofExcept (Manifest.parse (Command.chars text.toUTF8))
    | none => Manifest.read manifest
  return Manifest.sourcePaths manifest m

/-- The source documents of a manifest, in its recorded order. -/
def readSources (manifest : System.FilePath) (snapshots : List (String × String))
    (recover := false) : IO (List Source) := do
  (← sourcePaths manifest snapshots).mapM fun path ↦ do
    let real := (← IO.FS.realPath path).toString
    parseSource real (← sourceBytes real snapshots) recover

/-- Resolve proof imports in the proof runner's dependency order. Also keep the parsed inputs,
before attaching errors that depend on the presence or order of other files. -/
def readProofSources (proofs : String) (read : System.FilePath → IO Source) (recover : Bool) :
    IO (List Source × List Source) := do
  if proofs.isEmpty then return ([], [])
  let mut parsed := []
  let mut seen : List (Source × List String) := []
  let mut work := [proofs]
  for _ in [0:Authoring.documentLimit] do
    let p :: rest := work | break
    work := rest
    let file := (← IO.FS.realPath p).toString
    if seen.any (·.1.file == file) then continue
    let mut src ← try
        let raw ← read file
        parsed := raw :: parsed
        pure raw
      catch e =>
        unless recover do throw e
        pure { file, doc := ⟨[], []⟩, forms := [], incomplete := true, errors := [e.toString] }
    let doc : Doc := if src.incomplete then
        ⟨src.forms.map fun t ↦ (erase t).map (⟨⟨[], false, []⟩, ·⟩), []⟩ else src.doc
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
  return (ordered, parsed)

/-- The index through one file of the manifest or its proof imports. -/
structure Prefix where
  /-- The input, including import recovery errors. -/
  source : Source
  /-- Whether these forms are theorems. -/
  proof : Bool
  /-- The declarations and scopes through this file. -/
  state : State
  /-- Whether the elaborator recovered an error in this file. -/
  incomplete : Bool

/-- Parsed files and dependency-ordered checkpoints of the last successful request. -/
structure Cache where
  /-- Recovery mode is part of the parser's input. -/
  recover : Bool := false
  /-- The elaborator's depth bound is shared by all source files. -/
  depth : Nat := 0
  /-- The ordered index, whose unchanged prefix can be resumed. -/
  files : List Prefix := []
  /-- Documents before import resolution, reusable even beyond an invalidated prefix. -/
  parsed : List Source := []

/-- Update the index from the first changed input and resolve one editor operation. -/
def queryCached (old : Cache) (manifest : System.FilePath) (file : String)
    (pos : Locate.Pos) (snapshots : List (String × String)) (proofs operation : String)
    (recover : Bool) : IO (Lean.Json × Cache) := do
  let read (path : System.FilePath) : IO Source := do
    let real := (← IO.FS.realPath path).toString
    let bytes ← sourceBytes real snapshots
    match old.parsed.find? (fun s ↦ old.recover == recover &&
        s.file == real && s.bytes == bytes) with
      | some src => pure src
      | none => parseSource real bytes recover
  let sources ← (← sourcePaths manifest snapshots).mapM read
  let ((proofSources, parsedProofs), proofErrors) ← try
      pure (← readProofSources proofs read recover, [])
    catch e =>
      unless recover do throw e
      pure (([], []), [e.toString])
  let depth := (sources.map (·.modules)).sum + 1
  let mut previous := if old.depth == depth && old.recover == recover then old.files else []
  let mut files := []
  let mut st : State := {}
  for (src, proof) in sources.map (·, false) ++ proofSources.map (·, true) do
    if let h :: tail := previous then
      if h.proof == proof && h.source.file == src.file && h.source.bytes == src.bytes &&
          h.source.errors == src.errors && h.source.incomplete == src.incomplete then
        st := h.state
        files := h :: files
        previous := tail
        continue
    previous := []
    let errors := st.errors.length
    if proof then
      for root in src.forms.filter (Locate.headIs Authoring.kwProofs) do
        for t in root.children.drop 2 do st := proofDeclaration src st t
    else
      for t in src.forms do
        match walk depth { src with incomplete := recover || src.incomplete } [] st t with
        | .ok next => st := next
        | .error e =>
          unless recover do throw <| IO.userError e
          st := { st with errors := st.errors ++ [s!"{src.file}: {e}"] }
    files := ⟨src, proof, st, src.incomplete || st.errors.length != errors⟩ :: files
  let ordered := files.reverse
  let cache : Cache := ⟨recover, depth, ordered, sources ++ parsedProofs⟩
  let atCursor := ordered.find? (·.source.file == file)
  let atomSpan := if pos.line == 0 then none else
    atCursor.bind fun h ↦ h.source.forms.findSome? (completionSpan pos)
  let pos := match atomSpan with
    | some span => if contains span pos then pos else span.stop
    | none => pos
  let atSite {α : Type} (sites : List (Site α)) : Option α :=
    (sites.find? fun s ↦ s.file == file && contains s.span pos).map (fun s ↦ s.resolve pos)
  let focus := if atCursor.any (fun h ↦ h.source.comments.any (contains · pos)) then
      { scope := { active := false } }
    else
      let f := (atSite st.sites).getD {}
      { f with target := (atSite st.targets).getD f.target }
  let name := focus.target.map (sourceName st.origins)
  let target := focus.localTarget.orElse fun _ ↦ name.bind fun n ↦ st.byName.get? (String.ofList n)
  let symbols := if operation == "document" then st.symbols.filter (·.file == file)
    else if operation == "all" || operation == "workspace" then st.symbols else []
  let result := Json.object [("symbols", Lean.toJson (symbols.map (·.json operation))),
    ("target", if operation == "all" || operation == "target" then
      target.map (·.json operation) |>.getD .null else .null),
    ("completions", Lean.toJson (if operation == "all" || operation == "completion" then
      (completions st focus).map (·.json operation) else [])),
    ("atomSpan", atomSpan.map spanJson |>.getD .null),
    ("incomplete", Lean.toJson ((ordered.filter (·.incomplete)).map (·.source.file))),
    ("errors", Lean.toJson (proofErrors ++ (ordered.flatMap (·.source.errors)) ++ st.errors))]
  return (result, cache)

/-- A single query, independent of previous requests. -/
def query (manifest : System.FilePath) (file : String) (pos : Locate.Pos)
    (snapshots : List (String × String)) (proofs := "") (recover := false) : IO Lean.Json := do
  return (← queryCached {} manifest file pos snapshots proofs "all" recover).1

/-- Resolve a JSON request against the exact snapshots it carries. -/
def request (cache : Cache) (manifest : String) (input : String) : IO (Lean.Json × Cache) := do
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
  let op := (json.getObjValAs? String "operation").toOption.getD "all"
  queryCached cache manifest file ⟨line, column⟩ snapshots proofs op recover

/-- Read one JSON navigation request from standard input and write its JSON result. -/
def run (manifest : String) : IO UInt32 := do
  IO.println (← request {} manifest (← Json.readInput (← IO.getStdin))).1.compress
  return 0

/-- Serve newline-delimited JSON requests in order until the editor closes the stream. -/
def serve (manifest : String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  IO.iterate ({} : Cache) fun cache ↦ do
    let line ← stdin.getLine
    if line.isEmpty then return .inr 0
    let (answer, next) ← try request cache manifest line catch e =>
      pure (Json.object [("error", Lean.toJson e.toString)], cache)
    stdout.putStrLn answer.compress
    stdout.flush
    return .inl next

end GebHost.Navigation
