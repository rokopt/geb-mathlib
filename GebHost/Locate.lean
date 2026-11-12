/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Durable

set_option doc.verso true

/-!
# Source occurrences

The line and column of each S-expression of a source text, and of the declaration a name of the
flat program denotes, from which the drivers report where a rejected program fails.

A text's tokens are those of the document lexer, {name}`Geb.Kernel.Document.lexStep`, run a
character at a time beside a count of lines and columns, so that the spans are those of the
tokens the readers read and no second lexer is written. A span is a derived annotation: it is
computed from a source's bytes whenever a failure is reported, and nothing the compiler checks or
writes holds it.

## Main definitions

* {lit}`GebHost.Locate.Pos`, {lit}`GebHost.Locate.Span` — a position, and the span of an
  occurrence.
* {lit}`GebHost.Locate.Located` — an S-expression with the span of each node.
* {lit}`GebHost.Locate.locate` — the located S-expressions of a text, or where it does not read.
* {lit}`GebHost.Locate.findDeclarations`, {lit}`GebHost.Locate.findEnclosing` — the spans of the
  names of the declarations of a name, and of the declaration a name is written after.
* {lit}`GebHost.Locate.findReserved` — the span of an atom the implementation reserves.

## Implementation notes

Nothing here is trusted. The spans are checked against the lexer only in number: where the spans
counted differ in number from the tokens lexed, a text has no located S-expressions, and a
failure in it is reported without a position.

## Tags

diagnostics, source span, lexer, declaration
-/

open Geb Geb.Kernel Geb.Kernel.Document

public section

namespace GebHost.Locate

/-- A position in a text: its line and its column, each counted from one, a column counting the
bytes of its line. -/
@[ext] structure Pos where
  /-- The line, from one. -/
  line : Nat
  /-- The column, from one. -/
  col : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The position after a character at a position. -/
def Pos.next (p : Pos) (ch : Char) : Pos :=
  if ch == '\n' then ⟨p.line + 1, 1⟩ else ⟨p.line, p.col + 1⟩

/-- The first position of a text. -/
def Pos.first : Pos := ⟨1, 1⟩

/-- The span of an occurrence in a text: the positions of its first and of its last
character. -/
@[ext] structure Span where
  /-- The position of the first character. -/
  start : Pos
  /-- The position of the last character. -/
  stop : Pos
  deriving DecidableEq, Repr, Inhabited

/-- The span of one character. -/
def Span.at (p : Pos) : Span := ⟨p, p⟩

/-! ## The spans of tokens -/

/-- The lexer's state beside the positions it has reached. -/
structure Scan where
  /-- The lexer's state. -/
  lex : LexState
  /-- The position of the next character. -/
  pos : Pos
  /-- The position of the character before it. -/
  last : Pos
  /-- The position at which the token being read begins. -/
  start : Pos
  /-- The spans of the tokens read, the latest first. -/
  spans : List Span
  /-- The position of the first character at which the text is not well formed. -/
  bad : Option Pos

/-- The state before a text. -/
def Scan.init : Scan := ⟨.init, .first, .first, .first, [], none⟩

/-- Read one character: the lexer's step, and the spans of the tokens it completes. A token read
between tokens is its character; a token being read ends at the character before, or at the
character itself where that character closes it, a quoted string's, a verbatim atom's last, or a
hexadecimal or base-64 atom's; and a character that both ends a token and is one completes
two. -/
def scanStep (s : Scan) (ch : Char) : Scan :=
  if !s.lex.ok then s else
  let l := lexStep s.lex ch
  let p := s.pos
  let moved : Scan := { s with lex := l, pos := p.next ch, last := p }
  if !l.ok then { moved with bad := some p } else
  let k := l.toks.length - s.lex.toks.length
  let idleAfter := decide (l.mode = .idle)
  if decide (s.lex.mode = .idle) then
    if k == 0 then (if idleAfter then moved else { moved with start := p })
    else { moved with spans := .at p :: s.spans }
  else if k == 0 then moved
  else if k == 1 then
    if idleAfter then
      let closes := match s.lex.mode with
        | .verbatim _ => true
        | _ => !isSpace ch
      { moved with spans := ⟨s.start, if closes then p else s.last⟩ :: s.spans }
    else { moved with spans := ⟨s.start, s.last⟩ :: s.spans, start := p }
  else { moved with spans := .at p :: ⟨s.start, s.last⟩ :: s.spans }

/-- What rejects a text: the span of the occurrence, and why. -/
structure Fault where
  /-- The span of the occurrence. -/
  span : Span
  /-- Why the text is rejected there. -/
  message : String

/-- The tokens of a text, each with its span, or what rejects the text: the character the lexer
rejects, or the beginning of an atom the text ends inside. Where the spans counted are not as
many as the tokens, there are none. -/
def tokenSpans (text : List Char) : Except Fault (List (Tok × Span)) :=
  let s := text.foldl scanStep .init
  match s.bad with
  | some p => .error ⟨.at p, "the text is not well formed at this character"⟩
  | none =>
    match lexEnd s.lex with
    | none => .error ⟨.at s.start, "the text ends inside this atom"⟩
    | some toks =>
      let spans :=
        (if decide (s.lex.mode = .idle) then s.spans else ⟨s.start, s.last⟩ :: s.spans).reverse
      .ok (if spans.length == toks.length then toks.zip spans else [])

/-! ## Located S-expressions -/

/-- An S-expression with the span of each node: of an atom, or from a list's opening parenthesis
to its closing one. -/
abbrev Located : Type := RoseTree (Span × Option (List Char))

/-- A located atom. -/
def atomAt (sp : Span) (s : List Char) : Located := RoseTree.node (sp, some s) []

/-- A list being read: the position of its opening parenthesis, and its elements read so far,
the latest first. -/
structure Frame where
  /-- The position of the opening parenthesis. -/
  start : Pos
  /-- The elements read so far, the latest first. -/
  items : List Located

/-- A frame with an element added. -/
def Frame.push (f : Frame) (t : Located) : Frame := { f with items := t :: f.items }

/-- Read one token into a stack of lists under construction, the innermost first, as
{name}`Geb.Kernel.Document.readStep` does, a hole as its form at the hole's span and a comment
as nothing. -/
def readStep (st : Except Fault (List Frame)) (ts : Tok × Span) : Except Fault (List Frame) :=
  st.bind fun stack ↦
    match stack, ts.1 with
    | fs, .comment _ _ => .ok fs
    | fs, .lp _ => .ok (⟨ts.2.start, []⟩ :: fs)
    | f :: fs, .atom _ s => .ok (f.push (atomAt ts.2 s) :: fs)
    | f :: fs, .hole _ s =>
      .ok (f.push (RoseTree.node (ts.2, none) [atomAt ts.2 kwHole, atomAt ts.2 s]) :: fs)
    | f :: e :: fs, .rp =>
      .ok (e.push (RoseTree.node (⟨f.start, ts.2.stop⟩, none) f.items.reverse) :: fs)
    | _, _ => .error ⟨ts.2, "a closing parenthesis closes nothing"⟩

/-- The located S-expressions of a text, or what rejects it: what rejects its tokens, a closing
parenthesis that closes nothing, or the outermost list that is not closed. -/
def locate (text : List Char) : Except Fault (List Located) :=
  (tokenSpans text).bind fun toks ↦
    (toks.foldl readStep (.ok [⟨.first, []⟩])).bind fun stack ↦
      match stack.reverse with
      | [f] => .ok f.items.reverse
      | _ :: f :: _ => .error ⟨.at f.start, "a parenthesis is not closed"⟩
      | [] => .ok []

/-- Recover the readable prefix for editor inspection. Open lists are closed at the last
position solely to expose their completed children. The compiler never consumes this result. -/
def recover (text : List Char) : List Located := Id.run do
  let scan := text.foldl scanStep Scan.init
  let textPrefix :=  if scan.bad.isSome || (lexEnd scan.lex).isNone then
      (text.foldl (fun (p, cs) c ↦
        (p.next c, if p.line < scan.start.line ||
          (p.line == scan.start.line && p.col < scan.start.col) then c :: cs else cs))
        (Pos.first, [])).2.reverse
    else text
  let toks := (tokenSpans textPrefix).toOption.getD []
  let mut stack : List Frame := [⟨.first, []⟩]
  for tok in toks do
    match readStep (.ok stack) tok with
    | .ok fs => stack := fs
    | .error _ => break
  let stop := textPrefix.foldl Pos.next Pos.first
  let closed := stack.foldl (fun (child : Option Located) frame ↦
    let items := frame.items.reverse ++ child.toList
    some (RoseTree.node (⟨frame.start, stop⟩, none) items)) none
  return closed.toList.flatMap (·.children)

/-- Whether a located S-expression is a list headed by a given atom. -/
def headIs (k : List Char) (t : Located) : Bool :=
  t.label.2 == none && t.children.head?.any fun h ↦ h.label.2 == some k && h.children.isEmpty

/-- The forms of a source that the compilers read: its located S-expressions but its notes, which
the drivers erase before compiling. -/
def forms (items : List Located) : List Located := items.filter (!headIs kwNote ·)

/-! ## Declarations -/

/-- The declarations of a node, from its children's, each by its path from the node and with the
span of its name: a declaration's own, and a module's with those of its body under its name. -/
def declStep (l : Span × Option (List Char)) (rs : List (Located × List (Path × Span))) :
    List (Path × Span) :=
  match l.2, rs with
  | none, (k, _) :: (n, _) :: body =>
    match k.label.2, n.label.2 with
    | some kw, some name =>
      if k.children.isEmpty && n.children.isEmpty && declHeads.contains kw then
        ([name], n.label.1) ::
          if kw == kwModule then body.flatMap fun r ↦ r.2.map fun d ↦ (name :: d.1, d.2) else []
      else []
    | _, _ => []
  | _, _ => []

/-- The declarations of a source's located S-expressions, each by its path and with the span of
its name. -/
def declarations (items : List Located) : List (Path × Span) :=
  items.flatMap (RoseTree.para declStep)

/-- The name of a path in the flat program: its components joined by full stops. -/
def qualified (p : Path) : String := ".".intercalate (p.map String.ofList)

/-- The spans of the names of the declarations of a qualified name, in order. -/
def findDeclarations (items : List Located) (name : String) : List Span :=
  (declarations items).filterMap fun d ↦ if qualified d.1 == name then some d.2 else none

/-- The span of the name of the declaration whose qualified name is the longest prefix of a name
that ends before a full stop: what declares a name the elaboration writes after it, a datatype
its recognizer. -/
def findEnclosing (items : List Located) (name : String) : Option Span :=
  ((declarations items).foldl (fun (best : Option (String × Span)) d ↦
    let q := qualified d.1
    if (q ++ ".").toList.isPrefixOf name.toList && best.all (·.1.length < q.length) then
      some (q, d.2)
    else best) none).map Prod.snd

/-- The characters of the keyword of a quotation, {lit}`quote`. -/
def kwQuote : List Char := ['q', 'u', 'o', 't', 'e']

/-- The characters of the keyword of a datum, {lit}`datum`. -/
def kwDatum : List Char := ['d', 'a', 't', 'u', 'm']

/-- The span of the first atom of a node that begins with the percent sign, from its children's,
outside quotations and the data of datums, where the compiler reserves none. -/
def reservedStep (l : Span × Option (List Char)) (rs : List (Located × Option Span)) :
    Option Span :=
  match l.2 with
  | some s => if s.head? == some '%' then some l.1 else none
  | none =>
    let t : Located := RoseTree.node l (rs.map Prod.fst)
    if headIs kwQuote t then none
    else if headIs kwDatum t && rs.length == 3 then (rs.take 2).findSome? Prod.snd
    else rs.findSome? Prod.snd

/-- The span of the first atom of a source that the implementation reserves. -/
def findReserved (items : List Located) : Option Span :=
  items.findSome? (RoseTree.para reservedStep)

end GebHost.Locate

end
