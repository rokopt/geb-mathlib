/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Reader
public import Geb.Prototypes.RoseTree.Decorated

set_option doc.verso true in
/-!
# Source documents of the kernel's readable syntax

A source document is the text of a program read without loss of anything a person wrote but
the widths of its whitespace: its S-expressions, its comment lines and the empty lines between
its items. It is read into S-expressions with comments: rose trees whose labels are those of the
kernel's S-expressions, each node decorated with its trivia, the comment lines before it, each
with whether an empty line precedes it, whether an empty line precedes the node itself, and,
for a list, the comment lines before its closing parenthesis; the comment lines after the last
S-expression belong to the document. The decoration is that of
{name}`Geb.RoseTree.Decorated`, so the trivia, like every other annotation, is computed from
and into other decorations by redecoration. A comment is placed by its position alone, so
reading attaches no comment to the definition it documents; that attachment is a redecoration
of the trivia.

The reader {lit}`readDoc` is a conservative refinement of the kernel's reader
{name}`Geb.Kernel.readSExps`: erasing the decorations of what it reads gives what that reader
reads, at every text ({lit}`readDoc_erase`). The printer {lit}`print` is parameterized by a
layout, a choice at each token of whether a line break precedes it and of the indentation of
the new line, and the retraction law holds at every layout ({lit}`readDoc_print`): reading a
printed well-formed document gives the document back. A formatter, reading and printing with a
layout computed from the document, is therefore idempotent ({lit}`format_format`), whatever the
layout policy, so the policy is not part of what is proved.

## Main definitions

* {lit}`Line`, {lit}`Trivia`, {lit}`SExpr`, {lit}`Doc` — comment lines, the trivia an
  S-expression is decorated with, S-expressions with comments, and source documents.
* {lit}`lex`, {lit}`readDoc` — the lexer and reader keeping comments and empty lines.
* {lit}`sepFor`, {lit}`arrangeFrom`, {lit}`print` — the separators a layout chooses, and the
  printer.
* {lit}`defaultLayout`, {lit}`format` — a layout policy, and the formatter.

## Main statements

* {lit}`readDoc_erase` — the reader keeps what the kernel's reader reads.
* {lit}`readDoc_print` — the retraction law, at every layout.
* {lit}`format_format` — the formatter is idempotent.

## Implementation notes

The printer separates each token from the one before it by a separator determined by the two
tokens and the layout's choice ({lit}`sepFor`): an empty line before a token whose label records
one, a line break after a comment, which extends to the end of its line, and otherwise a line
break when the layout chooses one, nothing after an opening parenthesis or before a closing one,
and a space elsewhere. The lexer's correctness is proved for every sequence of separators so
formed, one token at a time, so the layout is an arbitrary function of the token's position.
The reader holds the comment lines read since the last S-expression on its stack, until the
S-expression after them, or the end of the list or of the text, takes them as its trivia.

## Tags

S-expression, comments, trivia, formatter, retraction, lossless syntax tree
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document

/-- A comment line: whether an empty line precedes it, and its characters after the semicolon
and before the end of the line. -/
@[ext] structure Line where
  /-- Whether an empty line precedes the comment line. -/
  gap : Bool
  /-- The characters of the comment. -/
  text : List Char
  deriving DecidableEq, Repr

/-- The trivia an S-expression is decorated with: the comment lines before it, whether an empty
line precedes it, and, for a list, the comment lines before its closing parenthesis. -/
@[ext] structure Trivia where
  /-- The comment lines before the S-expression. -/
  lead : List Line
  /-- Whether an empty line precedes the S-expression. -/
  gap : Bool
  /-- The comment lines before a list's closing parenthesis. -/
  close : List Line
  deriving DecidableEq, Repr

/-- An S-expression with comments: a rose tree whose labels are those of
{name}`Geb.Kernel.SExp`, an atom's characters or nothing for a list, each decorated with its
trivia. -/
abbrev SExpr : Type := RoseTree.Decorated Trivia (Option (List Char))

/-- A source document: its S-expressions with comments, and the comment lines after the
last. -/
@[ext] structure Doc where
  /-- The S-expressions. -/
  items : List SExpr
  /-- The comment lines after the last S-expression. -/
  trail : List Line

/-! ## Tokens and the lexer -/

/-- The tokens of a source document; each but a closing parenthesis records whether an empty
line precedes it. -/
inductive Tok where
  /-- An opening parenthesis. -/
  | lp (gap : Bool)
  /-- A closing parenthesis. -/
  | rp
  /-- An atom. -/
  | atom (gap : Bool) (s : List Char)
  /-- A comment line, without its semicolon and line break. -/
  | comment (gap : Bool) (s : List Char)
  deriving DecidableEq, Repr

/-- Whether an empty line precedes a token. -/
def Tok.gap : Tok → Bool
  | .lp g => g
  | .rp => false
  | .atom g _ => g
  | .comment g _ => g

/-- Whether a token is a comment. -/
def Tok.isComment : Tok → Bool
  | .comment _ _ => true
  | _ => false

/-- Whether a token is an opening parenthesis. -/
def Tok.isLp : Tok → Bool
  | .lp _ => true
  | _ => false

/-- The token of the kernel's reader a token erases to; a comment erases to nothing. -/
def Tok.erase : Tok → Option Token
  | .lp _ => some .lp
  | .rp => some .rp
  | .atom _ s => some (.atom s)
  | .comment _ _ => none

/-- Whether a character can occur in an atom: it is neither whitespace, a parenthesis nor the
semicolon that begins a comment. -/
def isAtomChar (c : Char) : Bool :=
  !(c == ';' || c == '(' || c == ')' || c.isWhitespace)

/-- Whether a token can be spelled and read back: an atom is a non-empty word of atom
characters, and a comment contains no line break. -/
def Tok.wf : Tok → Bool
  | .atom _ s => !s.isEmpty && s.all isAtomChar
  | .comment _ s => s.all (· != '\n')
  | _ => true

/-- The lexer's state. -/
structure LexState where
  /-- The tokens read, the latest first. -/
  toks : List Tok
  /-- The characters of the atom or comment being read, the latest first. -/
  cur : List Char
  /-- Whether a comment is being read. -/
  inComment : Bool
  /-- The line breaks since the last token began. -/
  breaks : ℕ
  /-- Whether an empty line precedes the atom or comment being read. -/
  gap : Bool

/-- End the atom being read, if any. -/
def endAtom (s : LexState) : LexState :=
  match s.cur with
  | [] => s
  | cs => ⟨.atom s.gap cs.reverse :: s.toks, [], false, s.breaks, false⟩

/-- Read one character. -/
def lexStep (s : LexState) (ch : Char) : LexState :=
  if s.inComment then
    if ch == '\n' then ⟨.comment s.gap s.cur.reverse :: s.toks, [], false, 1, false⟩
    else ⟨s.toks, ch :: s.cur, true, s.breaks, s.gap⟩
  else if ch == ';' then ⟨(endAtom s).toks, [], true, 0, decide (2 ≤ s.breaks)⟩
  else if ch == '(' then ⟨.lp (decide (2 ≤ s.breaks)) :: (endAtom s).toks, [], false, 0, false⟩
  else if ch == ')' then ⟨.rp :: (endAtom s).toks, [], false, 0, false⟩
  else if ch.isWhitespace then
    ⟨(endAtom s).toks, [], false, if ch == '\n' then s.breaks + 1 else s.breaks, false⟩
  else if s.cur.isEmpty then ⟨s.toks, [ch], false, 0, decide (2 ≤ s.breaks)⟩
  else ⟨s.toks, ch :: s.cur, false, 0, s.gap⟩

/-- The lexer's initial state. -/
def LexState.init : LexState := ⟨[], [], false, 0, false⟩

/-- The tokens of a text, from the lexer's state at its end. -/
def lexEnd (s : LexState) : List Tok :=
  if s.inComment then (.comment s.gap s.cur.reverse :: s.toks).reverse
  else (endAtom s).toks.reverse

/-- The tokens of a text. -/
def lex (text : List Char) : List Tok :=
  lexEnd (text.foldl lexStep LexState.init)

/-! ## The lexer refines the kernel's tokenizer -/

/-- The state of the kernel's tokenizer a lexer's state erases to: its tokens erased, and the
atom being read, a comment's characters being dropped. -/
def LexState.erase (s : LexState) : TokState :=
  (s.toks.filterMap Tok.erase, if s.inComment then [] else s.cur, s.inComment)

/-- One character read by the lexer and by the kernel's tokenizer from corresponding states
gives corresponding states. -/
theorem erase_lexStep (s : LexState) (ch : Char) : (lexStep s ch).erase = tokStep s.erase ch := by
  obtain ⟨ts, cs, c, n, g⟩ := s
  cases c <;> cases cs <;>
    simp only [lexStep, tokStep, LexState.erase, endAtom, flush, Bool.false_eq_true,
      ↓reduceIte, Tok.erase, List.isEmpty_nil, List.isEmpty_cons] <;>
    split_ifs <;> simp_all [Tok.erase, List.filterMap_cons]

/-- The kernel's tokenizer's tokens are the lexer's, erased. -/
theorem tokenize_eq (text : List Char) : tokenize text = (lex text).filterMap Tok.erase := by
  have h : text.foldl tokStep LexState.init.erase = (text.foldl lexStep LexState.init).erase :=
    List.foldl_hom _ fun s ch ↦ (erase_lexStep s ch).symm
  simp only [tokenize, lex, lexEnd]
  rw [show (([], [], false) : TokState) = LexState.init.erase from rfl, h]
  obtain ⟨ts, cs, c, n, g⟩ := text.foldl lexStep LexState.init
  cases c <;> cases cs <;> simp [LexState.erase, flush, endAtom, Tok.erase, List.filterMap_reverse]

/-! ## The reader -/

/-- A frame of the reader's stack: the comment lines before the list being read and whether an
empty line precedes it, its elements read so far, the latest first, and the comment lines read
since the last element, the latest first. -/
structure Frame where
  /-- The comment lines before the list. -/
  lead : List Line
  /-- Whether an empty line precedes the list. -/
  gap : Bool
  /-- The elements read so far, the latest first. -/
  items : List SExpr
  /-- The comment lines read since the last element, the latest first. -/
  pend : List Line

/-- The frame of a list beginning, with the comment lines before it. -/
def Frame.start (lead : List Line) (gap : Bool) : Frame := ⟨lead, gap, [], []⟩

/-- A frame with an element added, the comment lines read before it becoming its trivia. -/
def Frame.push (f : Frame) (t : SExpr) : Frame := ⟨f.lead, f.gap, t :: f.items, []⟩

/-- Read one token into a stack of lists under construction, the innermost first: a comment
line waits for the S-expression after it, or for the end of the list or the text, whose trivia
it becomes. A comment read where no list is open leaves the empty stack as it is, as the
kernel's reader leaves it. -/
def readStep : Option (List Frame) → Tok → Option (List Frame)
  | some (f :: fs), .lp g => some (.start f.pend.reverse g :: { f with pend := [] } :: fs)
  | some (f :: fs), .atom g s =>
    some (f.push (RoseTree.node (⟨f.pend.reverse, g, []⟩, some s) []) :: fs)
  | some (f :: fs), .comment g s => some ({ f with pend := ⟨g, s⟩ :: f.pend } :: fs)
  | some (f :: e :: fs), .rp =>
    some (e.push (RoseTree.node (⟨f.lead, f.gap, f.pend.reverse⟩, none) f.items.reverse) :: fs)
  | some [], .lp g => some [.start [] g]
  | some [], .comment _ _ => some []
  | _, _ => none

/-- The source document of a text, or nothing when its parentheses do not balance. -/
def readDoc (text : List Char) : Option Doc :=
  match (lex text).foldl readStep (some [.start [] false]) with
  | some [f] => some ⟨f.items.reverse, f.pend.reverse⟩
  | _ => none

/-- The stack of the kernel's reader a stack of frames erases to. -/
def eraseStack : Option (List Frame) → Option (List (List SExp)) :=
  Option.map (List.map fun f ↦ f.items.map RoseTree.erase)

/-- A node erases to the node of its label over its children erased. -/
theorem erase_node (l : Trivia × Option (List Char)) (cs : List SExpr) :
    RoseTree.erase (RoseTree.node l cs) = RoseTree.node l.2 (cs.map RoseTree.erase) :=
  RoseTree.map_node _ _ _

/-- One token read by the reader and, erased, by the kernel's reader from corresponding stacks
gives corresponding stacks. -/
theorem eraseStack_readStep (st : Option (List Frame)) (t : Tok) :
    eraseStack (readStep st t) =
      match t.erase with
      | none => eraseStack st
      | some u => parseStep (eraseStack st) u := by
  rcases st with _ | _ | ⟨f, _ | ⟨e, fs⟩⟩ <;> cases t <;>
    simp [readStep, parseStep, eraseStack, Tok.erase, Frame.push, Frame.start, erase_node,
      List.map_reverse]

/-- Reading tokens, erased, by the kernel's reader from an erased stack gives the erasure of
reading them from the stack. -/
theorem foldl_readStep (toks : List Tok) :
    ∀ st, eraseStack (toks.foldl readStep st) =
      (toks.filterMap Tok.erase).foldl parseStep (eraseStack st) :=
  List.rec (fun _ ↦ rfl) (fun t rest ih st ↦ by
    rw [List.foldl_cons, ih, eraseStack_readStep]
    cases h : t.erase <;> simp [h]) toks

/-- The reader keeps what the kernel's reader reads: erasing the decorations of the
S-expressions of a text gives the text's S-expressions. -/
theorem readDoc_erase (text : List Char) :
    (readDoc text).map (·.items.map RoseTree.erase) = readSExps text := by
  have h := foldl_readStep (lex text) (some [.start [] false])
  rw [readSExps, tokenize_eq,
    show (some [[]] : Option (List (List SExp))) = eraseStack (some [.start [] false]) from rfl,
    ← h, readDoc]
  rcases (lex text).foldl readStep (some [.start [] false]) with _ | _ | ⟨f, _ | ⟨_, _⟩⟩ <;>
    simp [eraseStack, List.map_reverse]

/-! ## The printer -/

/-- A separator before a token. -/
inductive Sep where
  /-- Nothing. -/
  | none
  /-- A space. -/
  | space
  /-- A line break, and the indentation of the new line. -/
  | line (indent : ℕ)
  /-- An empty line, and the indentation of the line after it. -/
  | blank (indent : ℕ)

/-- A separator's characters. -/
def Sep.render : Sep → List Char
  | .none => []
  | .space => [' ']
  | .line k => '\n' :: List.replicate k ' '
  | .blank k => '\n' :: '\n' :: List.replicate k ' '

/-- A token's characters. -/
def Tok.render : Tok → List Char
  | .lp _ => ['(']
  | .rp => [')']
  | .atom _ s => s
  | .comment _ s => ';' :: s

/-- Whether a token is a closing parenthesis. -/
def Tok.isRp : Tok → Bool
  | .rp => true
  | _ => false

/-- The separator before a token, given the token before it, if any, and a layout's choice of
whether to break the line there and of the indentation of the new line: an empty line where the
token records one; a line break after a comment, which extends to the end of its line, or where
the layout breaks the line; nothing at the start, after an opening parenthesis and before a
closing one; and a space elsewhere. -/
def sepFor (prev : Option Tok) (t : Tok) (brk : Bool) (k : ℕ) : Sep :=
  if t.gap then .blank k
  else if prev.any Tok.isComment || brk then .line k
  else if prev.all Tok.isLp || t.isRp then .none
  else .space

/-- Tokens, each with the separator before it, given a layout, a choice at each position of the
text, and the token before the first and the first's position. -/
def arrangeFrom (L : ℕ → Bool × ℕ) (toks : List Tok) : Option Tok → ℕ → List (Sep × Tok) :=
  List.rec (motive := fun _ ↦ Option Tok → ℕ → List (Sep × Tok)) (fun _ _ ↦ [])
    (fun t _ ih prev i ↦ (sepFor prev t (L i).1 (L i).2, t) :: ih (some t) (i + 1)) toks

/-- The characters of tokens with their separators. -/
def render (ps : List (Sep × Tok)) : List Char :=
  ps.flatMap fun p ↦ p.1.render ++ p.2.render

/-- The token of a comment line. -/
def Line.tok (l : Line) : Tok := .comment l.gap l.text

/-- The tokens of an S-expression: the comment lines before it, then an atom, or a list's
parentheses around the tokens of its elements and the comment lines before its end. -/
def tokensOf : SExpr → List Tok :=
  RoseTree.elim fun l rs ↦
    l.1.lead.map Line.tok ++
      match l.2 with
      | some s => [.atom l.1.gap s]
      | none => .lp l.1.gap :: rs.flatten ++ l.1.close.map Line.tok ++ [.rp]

/-- The tokens of a document. -/
def Doc.tokens (d : Doc) : List Tok := d.items.flatMap tokensOf ++ d.trail.map Line.tok

/-- A document's characters, laid out by a layout, a choice at each position of the document's
tokens; the text ends with a line break. -/
def print (L : ℕ → Bool × ℕ) (d : Doc) : List Char :=
  render (arrangeFrom L d.tokens none 0) ++ ['\n']

/-! ## Lexing what the printer writes -/

/-- The line breaks a separator writes. -/
def Sep.breaks : Sep → ℕ
  | .none => 0
  | .space => 0
  | .line _ => 1
  | .blank _ => 2

/-- The token a token leaves pending, an atom or a comment, whose end the lexer has not yet
read. -/
def pendOf : Option Tok → Option Tok
  | some (.atom g s) => some (.atom g s)
  | some (.comment g s) => some (.comment g s)
  | _ => none

/-- The lexer's state after tokens, the latest first, and a pending token. -/
def state (done : List Tok) : Option Tok → LexState
  | some (.atom g s) => ⟨done, s.reverse, false, 0, g⟩
  | some (.comment g s) => ⟨done, s.reverse, true, 0, g⟩
  | _ => ⟨done, [], false, 0, false⟩

/-- The tokens the lexer emits as soon as it reads a token: a parenthesis. -/
def Tok.emitted (t : Tok) : List Tok := if t.isLp || t.isRp then [t] else []

/-- Spaces leave a state between tokens as it is. -/
theorem foldl_spaces (d : List Tok) (n : ℕ) (k : ℕ) :
    (List.replicate k ' ').foldl lexStep ⟨d, [], false, n, false⟩ = ⟨d, [], false, n, false⟩ :=
  Nat.rec rfl (fun k ih ↦ by
    rw [List.replicate_succ, List.foldl_cons]
    exact (congrArg (fun s ↦ (List.replicate k ' ').foldl lexStep s)
      (by simp [lexStep, endAtom])).trans ih) k

/-- A line break between tokens is counted. -/
theorem lexStep_newline (d : List Tok) (n : ℕ) :
    lexStep ⟨d, [], false, n, false⟩ '\n' = ⟨d, [], false, n + 1, false⟩ :=
  rfl

/-- A separator read between tokens counts its line breaks. -/
theorem foldl_sep (sep : Sep) (d : List Tok) :
    sep.render.foldl lexStep ⟨d, [], false, 0, false⟩ = ⟨d, [], false, sep.breaks, false⟩ := by
  cases sep with
  | none => rfl
  | space => simp [Sep.render, Sep.breaks, lexStep, endAtom]
  | line k => simp only [Sep.render, List.foldl_cons, lexStep_newline, foldl_spaces, Sep.breaks]
  | blank k => simp only [Sep.render, List.foldl_cons, lexStep_newline, foldl_spaces, Sep.breaks]

/-- The characters of an atom after its first extend the atom being read. -/
theorem foldl_atomChars (cs : List Char) (hcs : cs.all isAtomChar) :
    ∀ (d : List Tok) (b : List Char) (g : Bool), b ≠ [] →
      cs.foldl lexStep ⟨d, b, false, 0, g⟩ = ⟨d, cs.reverse ++ b, false, 0, g⟩ :=
  List.rec (motive := fun cs ↦ cs.all isAtomChar → ∀ (d : List Tok) (b : List Char) (g : Bool),
      b ≠ [] → cs.foldl lexStep ⟨d, b, false, 0, g⟩ = ⟨d, cs.reverse ++ b, false, 0, g⟩)
    (fun _ _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g hb ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hc, hall⟩ := hall
      simp only [isAtomChar, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      have hstep : lexStep ⟨d, b, false, 0, g⟩ c = ⟨d, c :: b, false, 0, g⟩ := by
        cases b with
        | nil => exact absurd rfl hb
        | cons x xs => simp [lexStep, h1, h2, h3, h4]
      rw [List.foldl_cons, hstep, ih hall d (c :: b) g (List.cons_ne_nil c b)]
      simp) cs hcs

/-- The characters of a comment extend the comment being read. -/
theorem foldl_commentChars (cs : List Char) (hcs : cs.all (· != '\n')) :
    ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, true, 0, g⟩ = ⟨d, cs.reverse ++ b, true, 0, g⟩ :=
  List.rec (motive := fun cs ↦ cs.all (· != '\n') → ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, true, 0, g⟩ = ⟨d, cs.reverse ++ b, true, 0, g⟩)
    (fun _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g ↦ by
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hall
      obtain ⟨hc, hall⟩ := hall
      have hstep : lexStep ⟨d, b, true, 0, g⟩ c = ⟨d, c :: b, true, 0, g⟩ := by
        simp [lexStep, hc]
      rw [List.foldl_cons, hstep, ih (by simpa using hall) d (c :: b) g]
      simp) cs hcs

/-- A token read between tokens, after a separator of as many line breaks as the token's record
of an empty line requires, is emitted, or left pending when it is an atom or a comment. -/
theorem foldl_tok (t : Tok) (d : List Tok) (n : ℕ) (ht : t.wf) (hg : t.gap = decide (2 ≤ n)) :
    t.render.foldl lexStep ⟨d, [], false, n, false⟩ = state (t.emitted ++ d) (pendOf (some t)) := by
  cases t with
  | lp g =>
    subst hg
    rfl
  | rp => rfl
  | atom g s =>
    simp only [Tok.wf, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at ht
    obtain ⟨hne, hall⟩ := ht
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hc, hall⟩ := hall
    simp only [isAtomChar, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    simp only [Tok.gap] at hg
    have hstep : lexStep ⟨d, [], false, n, false⟩ c = ⟨d, [c], false, 0, g⟩ := by
      simp [lexStep, h1, h2, h3, h4, ← hg]
    simp only [Tok.render, List.foldl_cons, hstep,
      foldl_atomChars cs hall d [c] g (List.cons_ne_nil c []), state, pendOf, Tok.emitted,
      Tok.isLp, Tok.isRp, Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      List.reverse_cons]
  | comment g s =>
    simp only [Tok.gap] at hg
    have hstep : lexStep ⟨d, [], false, n, false⟩ ';' = ⟨d, [], true, 0, g⟩ := by
      subst hg
      rfl
    simp only [Tok.render, List.foldl_cons, hstep, foldl_commentChars s ht d [] g, state, pendOf,
      Tok.emitted, Tok.isLp, Tok.isRp, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.append_nil]

/-- The separator {name}`sepFor` chooses writes an empty line exactly when the token records
one. -/
theorem gap_sepFor (prev : Option Tok) (t : Tok) (b : Bool) (k : ℕ) :
    t.gap = decide (2 ≤ (sepFor prev t b k).breaks) := by
  unfold sepFor
  split_ifs with h1 h2 h3 <;> simp_all [Sep.breaks]

/-- After an atom, {name}`sepFor` writes nothing only before a closing parenthesis. -/
theorem sepFor_atom_none {g : Bool} {a : List Char} {t : Tok} {b : Bool} {k : ℕ}
    (h : sepFor (some (.atom g a)) t b k = .none) : t = .rp := by
  unfold sepFor at h
  cases t <;> split_ifs at h <;> simp_all [Tok.isRp, Tok.isLp, Tok.isComment]

/-- After a comment, {name}`sepFor` writes a line break. -/
theorem sepFor_comment (g : Bool) (c : List Char) (t : Tok) (b : Bool) (k : ℕ) :
    sepFor (some (.comment g c)) t b k = .line k ∨
      sepFor (some (.comment g c)) t b k = .blank k := by
  unfold sepFor
  split_ifs <;> simp_all [Tok.isComment]

/-- A space after an atom emits it. -/
theorem lexStep_atom_space (d : List Tok) (a : List Char) (g : Bool) (ha : a ≠ []) :
    lexStep ⟨d, a.reverse, false, 0, g⟩ ' ' = ⟨.atom g a :: d, [], false, 0, false⟩ := by
  obtain ⟨x, xs, h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr ha)
  rw [h, ← List.reverse_reverse a, h]
  rfl

/-- A line break after an atom emits it and is counted. -/
theorem lexStep_atom_newline (d : List Tok) (a : List Char) (g : Bool) (ha : a ≠ []) :
    lexStep ⟨d, a.reverse, false, 0, g⟩ '\n' = ⟨.atom g a :: d, [], false, 1, false⟩ := by
  obtain ⟨x, xs, h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr ha)
  rw [h, ← List.reverse_reverse a, h]
  rfl

/-- A closing parenthesis after an atom emits the atom and the parenthesis. -/
theorem lexStep_atom_rp (d : List Tok) (a : List Char) (g : Bool) (ha : a ≠ []) :
    lexStep ⟨d, a.reverse, false, 0, g⟩ ')' = ⟨.rp :: .atom g a :: d, [], false, 0, false⟩ := by
  obtain ⟨x, xs, h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr ha)
  rw [h, ← List.reverse_reverse a, h]
  rfl

/-- A line break ends a comment and emits it. -/
theorem lexStep_comment_newline (d : List Tok) (c : List Char) (g : Bool) :
    lexStep ⟨d, c.reverse, true, 0, g⟩ '\n' = ⟨.comment g c :: d, [], false, 1, false⟩ := by
  rw [← List.reverse_reverse c, List.reverse_reverse c.reverse]
  rfl

/-- A token read after the separator {name}`sepFor` chooses, from the state its predecessor left,
emits the predecessor if it was pending and leaves the lexer in the state after the token. -/
theorem foldl_step (prev : Option Tok) (t : Tok) (b : Bool) (k : ℕ) (done : List Tok)
    (hp : prev.all Tok.wf) (ht : t.wf) :
    ((sepFor prev t b k).render ++ t.render).foldl lexStep (state done (pendOf prev)) =
      state (t.emitted ++ ((pendOf prev).toList ++ done)) (pendOf (some t)) := by
  have hg := gap_sepFor prev t b k
  rw [List.foldl_append]
  rcases prev with _ | ⟨_ | _ | ⟨g, a⟩ | ⟨g, c⟩⟩
  · simp only [pendOf, state, Option.toList_none, List.nil_append]
    rw [foldl_sep]
    exact foldl_tok t done _ ht hg
  · simp only [pendOf, state, Option.toList_none, List.nil_append]
    rw [foldl_sep]
    exact foldl_tok t done _ ht hg
  · simp only [pendOf, state, Option.toList_none, List.nil_append]
    rw [foldl_sep]
    exact foldl_tok t done _ ht hg
  · have ha : a ≠ [] := by
      simp only [Option.all_some, Tok.wf, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hp
      exact hp.1
    simp only [pendOf, state, Option.toList_some, List.singleton_append]
    cases hs : sepFor (some (.atom g a)) t b k with
    | none =>
      obtain rfl := sepFor_atom_none hs
      simp [Sep.render, Tok.render, lexStep_atom_rp _ _ _ ha, Tok.emitted, Tok.isRp]
    | space =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons, List.foldl_nil, lexStep_atom_space _ _ _ ha]
      exact foldl_tok t _ 0 ht hg
    | line j =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons, lexStep_atom_newline _ _ _ ha, foldl_spaces]
      exact foldl_tok t _ 1 ht hg
    | blank j =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons, lexStep_atom_newline _ _ _ ha, lexStep_newline,
        foldl_spaces]
      exact foldl_tok t _ 2 ht hg
  · simp only [pendOf, state, Option.toList_some, List.singleton_append]
    rcases sepFor_comment g c t b k with hs | hs <;> rw [hs] at hg ⊢
    · simp only [Sep.render, List.foldl_cons, lexStep_comment_newline, foldl_spaces]
      exact foldl_tok t _ 1 ht hg
    · simp only [Sep.render, List.foldl_cons, lexStep_comment_newline, lexStep_newline,
        foldl_spaces]
      exact foldl_tok t _ 2 ht hg

/-- The lexer reads back the tokens a layout arranges, after those already emitted and the
one pending, whatever the layout chooses. -/
theorem lexEnd_arrangeFrom (L : ℕ → Bool × ℕ) (toks : List Tok) (htoks : toks.all Tok.wf) :
    ∀ (prev : Option Tok) (i : ℕ) (done : List Tok), prev.all Tok.wf →
      lexEnd ((render (arrangeFrom L toks prev i) ++ ['\n']).foldl lexStep
        (state done (pendOf prev))) = done.reverse ++ (pendOf prev).toList ++ toks :=
  List.rec (motive := fun toks ↦ toks.all Tok.wf → ∀ (prev : Option Tok) (i : ℕ)
      (done : List Tok), prev.all Tok.wf →
      lexEnd ((render (arrangeFrom L toks prev i) ++ ['\n']).foldl lexStep
        (state done (pendOf prev))) = done.reverse ++ (pendOf prev).toList ++ toks)
    (fun _ prev _ done hp ↦ by
      change lexEnd (lexStep (state done (pendOf prev)) '\n') = _
      rcases prev with _ | ⟨_ | _ | ⟨g, a⟩ | ⟨g, c⟩⟩
      · simp only [pendOf, state, lexStep_newline, Option.toList_none, List.append_nil]
        rfl
      · simp only [pendOf, state, lexStep_newline, Option.toList_none, List.append_nil]
        rfl
      · simp only [pendOf, state, lexStep_newline, Option.toList_none, List.append_nil]
        rfl
      · have ha : a ≠ [] := by
          simp only [Option.all_some, Tok.wf, Bool.and_eq_true, Bool.not_eq_true',
            List.isEmpty_eq_false_iff] at hp
          exact hp.1
        simp only [pendOf, state, lexStep_atom_newline _ _ _ ha, Option.toList_some,
          List.append_nil]
        exact List.reverse_cons ..
      · simp only [pendOf, state, lexStep_comment_newline, Option.toList_some, List.append_nil]
        exact List.reverse_cons ..)
    (fun t rest ih hall prev i done hp ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hstep := foldl_step prev t (L i).1 (L i).2 done hp hall.1
      have harr : arrangeFrom L (t :: rest) prev i =
          (sepFor prev t (L i).1 (L i).2, t) :: arrangeFrom L rest (some t) (i + 1) := rfl
      rw [harr, render, List.flatMap_cons, ← render, List.append_assoc, List.foldl_append,
        hstep, ih hall.2 (some t) (i + 1) _ (by simpa using hall.1)]
      cases t <;> rcases hq : pendOf prev with _ | q <;>
        simp [Tok.emitted, Tok.isLp, Tok.isRp, pendOf]) toks htoks

/-- The lexer reads back the tokens a layout arranges, whatever the layout. -/
theorem lex_print (L : ℕ → Bool × ℕ) (toks : List Tok) (h : toks.all Tok.wf) :
    lex (render (arrangeFrom L toks none 0) ++ ['\n']) = toks := by
  have h' := lexEnd_arrangeFrom L _ h none 0 [] rfl
  simp only [pendOf, Option.toList_none, List.reverse_nil, List.nil_append] at h'
  exact h'

/-! ## Reading what the printer writes -/

/-- Whether a comment line can be printed and read back: it contains no line break. -/
def Line.wf (l : Line) : Bool := l.text.all (· != '\n')

/-- Whether an S-expression can be printed and read back: its comment lines are well formed,
and an atom is a non-empty word of atom characters without children or closing comment
lines. -/
def wf : SExpr → Bool :=
  RoseTree.elim fun l rs ↦
    l.1.lead.all Line.wf &&
      match l.2 with
      | some s => rs.isEmpty && l.1.close.isEmpty && (Tok.atom l.1.gap s).wf
      | none => l.1.close.all Line.wf && rs.all id

/-- Whether a document can be printed and read back. -/
def Doc.wf (d : Doc) : Bool := d.items.all Document.wf && d.trail.all Line.wf

/-- The tokens of an atom. -/
theorem tokensOf_atom (tr : Trivia) (s : List Char) (cs : List SExpr) :
    tokensOf (RoseTree.node (tr, some s) cs) = tr.lead.map Line.tok ++ [.atom tr.gap s] := by
  simp [tokensOf]

/-- The tokens of a list: its comment lines before it, and its parentheses around the tokens of
its elements and its comment lines before its end. -/
theorem tokensOf_list (tr : Trivia) (cs : List SExpr) :
    tokensOf (RoseTree.node (tr, none) cs) =
      tr.lead.map Line.tok ++ (.lp tr.gap :: cs.flatMap tokensOf ++ tr.close.map Line.tok ++
        [.rp]) := by
  simp [tokensOf, List.flatMap_def]

/-- A well-formed atom has no children and no closing comment lines. -/
theorem wf_atom (tr : Trivia) (s : List Char) (cs : List SExpr) :
    wf (RoseTree.node (tr, some s) cs) =
      (tr.lead.all Line.wf && (cs.isEmpty && tr.close.isEmpty && (Tok.atom tr.gap s).wf)) := by
  simp [wf]

/-- A list is well formed when its comment lines and its elements are. -/
theorem wf_list (tr : Trivia) (cs : List SExpr) :
    wf (RoseTree.node (tr, none) cs) =
      (tr.lead.all Line.wf && (tr.close.all Line.wf && cs.all wf)) := by
  simp [wf, List.all_map]

/-- The token of a well-formed comment line can be printed and read back. -/
theorem wf_tok {l : Line} (h : l.wf) : l.tok.wf := h

/-- The tokens of well-formed comment lines can be printed and read back. -/
theorem all_wf_toks {ls : List Line} (h : ls.all Line.wf) : (ls.map Line.tok).all Tok.wf := by
  simpa [List.all_map, Function.comp_def, Line.tok, Tok.wf, Line.wf] using h

/-- The tokens of a well-formed S-expression can be printed and read back. -/
theorem all_wf_tokensOf : ∀ t : SExpr, wf t → (tokensOf t).all Tok.wf :=
  RoseTree.ind fun l cs ih h ↦ by
    obtain ⟨tr, k⟩ := l
    cases k with
    | some s =>
      rw [wf_atom] at h
      simp only [Bool.and_eq_true] at h
      simp [tokensOf_atom, all_wf_toks h.1, h.2.2]
    | none =>
      rw [wf_list] at h
      simp only [Bool.and_eq_true] at h
      simp only [tokensOf_list, List.all_append, List.all_cons, List.all_flatMap, Tok.wf,
        all_wf_toks h.1, all_wf_toks h.2.1, Bool.true_and, List.all_nil, Bool.and_true,
        List.all_eq_true]
      exact fun c hc ↦ List.all_eq_true.mp (ih c hc (List.all_eq_true.mp h.2.2 c hc))

/-- Reading comment lines' tokens onto a frame adds them to its pending lines. -/
theorem foldl_readStep_lines (ls : List Line) :
    ∀ f fs, (ls.map Line.tok).foldl readStep (some (f :: fs)) =
      some ({ f with pend := ls.reverse ++ f.pend } :: fs) :=
  List.rec (fun f fs ↦ by simp) (fun l ls ih f fs ↦ by
    simp only [List.map_cons, List.foldl_cons, Line.tok, readStep]
    rw [ih]
    simp) ls

/-- Reading the tokens of well-formed S-expressions onto a frame with no pending lines adds the
S-expressions to it. -/
theorem foldl_readStep_items (cs : List SExpr)
    (ih : ∀ t ∈ cs, wf t → ∀ (f : Frame) fs, f.pend = [] →
      (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs))
    (hcs : ∀ c ∈ cs, wf c) :
    ∀ (f : Frame) fs, f.pend = [] → (cs.flatMap tokensOf).foldl readStep (some (f :: fs)) =
      some (⟨f.lead, f.gap, cs.reverse ++ f.items, []⟩ :: fs) :=
  List.rec (motive := fun cs ↦ (∀ t ∈ cs, wf t → ∀ (f : Frame) fs, f.pend = [] →
      (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs)) →
      (∀ c ∈ cs, wf c) → ∀ (f : Frame) fs, f.pend = [] →
      (cs.flatMap tokensOf).foldl readStep (some (f :: fs)) =
        some (⟨f.lead, f.gap, cs.reverse ++ f.items, []⟩ :: fs))
    (fun _ _ f fs hf ↦ by
      obtain ⟨a, b, c, d⟩ := f
      simp only at hf
      subst hf
      rfl)
    (fun c cs ihl ih hcs f fs hf ↦ by
      rw [List.flatMap_cons, List.foldl_append,
        ih c List.mem_cons_self (hcs c List.mem_cons_self) f fs hf,
        ihl (fun t ht ↦ ih t (List.mem_cons_of_mem c ht))
          (fun d hd ↦ hcs d (List.mem_cons_of_mem c hd)) _ fs rfl]
      simp [Frame.push]) cs ih hcs

/-- Reading the tokens of a well-formed S-expression onto a frame with no pending lines adds the
S-expression to it. -/
theorem foldl_readStep_tokensOf : ∀ t : SExpr, wf t → ∀ (f : Frame) fs, f.pend = [] →
    (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs) :=
  RoseTree.ind fun l cs ih h f fs hf ↦ by
    obtain ⟨tr, k⟩ := l
    cases k with
    | some s =>
      rw [wf_atom] at h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨-, ⟨rfl, hc⟩, -⟩ := h
      obtain ⟨lead, gap, close⟩ := tr
      simp only at hc
      subst hc
      rw [tokensOf_atom, List.foldl_append, foldl_readStep_lines]
      simp [readStep, hf, Frame.push]
    | none =>
      rw [wf_list] at h
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      rw [tokensOf_list, List.foldl_append, foldl_readStep_lines]
      simp only [List.foldl_cons, List.foldl_append, hf, List.append_nil, readStep]
      rw [foldl_readStep_items cs ih h.2.2 _ _ rfl, foldl_readStep_lines]
      simp [Frame.start, Frame.push]

/-- The retraction law: reading a document printed at any layout gives the document back, when
it is well formed. -/
theorem readDoc_print (L : ℕ → Bool × ℕ) (d : Doc) (h : d.wf) :
    readDoc (print L d) = some d := by
  simp only [Doc.wf, Bool.and_eq_true] at h
  have hw : ∀ c ∈ d.items, wf c := List.all_eq_true.mp h.1
  have htoks : d.tokens.all Tok.wf := by
    simp only [Doc.tokens, List.all_append, List.all_flatMap, all_wf_toks h.2, Bool.and_true,
      List.all_eq_true]
    exact fun c hc ↦ List.all_eq_true.mp (all_wf_tokensOf c (hw c hc))
  rw [readDoc, print, lex_print L d.tokens htoks, Doc.tokens, List.foldl_append,
    foldl_readStep_items d.items (fun t _ ↦ foldl_readStep_tokensOf t) hw _ [] rfl,
    foldl_readStep_lines]
  simp [Frame.start]

/-! ## A layout policy and the formatter -/

/-- A layout from the column an element's first character is written at and the number of
closing parentheses that follow the element on its line: it appends the choices for the
element's tokens after the first to those made before, and gives the column after the
element. -/
abbrev Plan : Type := ℕ → ℕ → Array (Bool × ℕ) → Array (Bool × ℕ) × ℕ

/-- An element of a list's layout, a comment line or an S-expression, each one token or more:
whether an empty line precedes it, whether it is a comment line or an atom, its width on one
line, if it can be written on one, and its layout. -/
structure Elem where
  /-- Whether an empty line precedes the element. -/
  gap : Bool
  /-- Whether the element is a comment line. -/
  isComment : Bool
  /-- Whether the element is an atom. -/
  isAtom : Bool
  /-- The element's width on one line, or nothing when it cannot be written on one. -/
  width : Option ℕ
  /-- The element's layout. -/
  plan : Plan

/-- The element of a comment line. -/
def Line.elem (l : Line) : Elem :=
  ⟨l.gap, true, false, none, fun c _ acc ↦ (acc, c + 1 + l.text.length)⟩

/-- The elements of a list: each element's comment lines before it and the element, then the
comment lines before the list's end. -/
def elemsOf (rs : List (List Line × Elem)) (close : List Line) : List Elem :=
  rs.flatMap (fun r ↦ r.1.map Line.elem ++ [r.2]) ++ close.map Line.elem

/-- The state of a list's layout between its elements: the current column, whether a line has
been broken before an element after the first, whether the element before was a comment, the
position of the next element, and the choices made. -/
structure PlanState where
  /-- The current column. -/
  col : ℕ
  /-- Whether a line was broken before an element after the first. -/
  broken : Bool
  /-- Whether the element before was a comment. -/
  afterComment : Bool
  /-- The position of the next element. -/
  pos : ℕ
  /-- The choices made for the tokens so far. -/
  out : Array (Bool × ℕ)

/-- Lay out one element of a list whose elements are indented to a column, within a line
width, given the list's number of elements and the closing parentheses that follow the list.
The element begins a line when the list does not fit on one, when it or the element before is
a comment, when a line was broken before an earlier element after the first, or when it and
the parentheses that follow it do not fit on the current line; the first element begins one
only when it or the element before is a comment. -/
def planElem (lim ind n trail : ℕ) (fits : Bool) (s : PlanState) (e : Elem) : PlanState :=
  let after := if s.pos + 1 == n then trail + 1 else 0
  let brk : Bool :=
    if fits || s.pos == 0 then e.isComment || s.afterComment
    else e.isComment || s.afterComment || s.broken ||
      match e.width with
      | some w => lim < s.col + 1 + w + after
      | none => true
  let start := if brk || e.gap || s.afterComment then ind else if s.pos == 0 then s.col
    else s.col + 1
  let (out, endCol) := e.plan start after (s.out.push (brk, ind))
  ⟨endCol, s.broken || (brk && s.pos != 0) || e.gap, e.isComment, s.pos + 1, out⟩

/-- An S-expression's comment lines before it and its element. A list that fits within the line
width is written on one line; otherwise its elements after the first fill the first line while
they fit, and the rest begin lines indented past the list's opening parenthesis, by two columns
after an atom at its head and by one otherwise, so that no line is indented beyond a
parenthesis closed at the end of the line before. A list holding a comment line, or an element
after an empty line, is not written on one line. -/
def planStep (lim : ℕ) (l : Trivia × Option (List Char)) (rs : List (List Line × Elem)) :
    List Line × Elem :=
  let es := elemsOf rs l.1.close
  let w : Option ℕ := match l.2 with
    | some s => some s.length
    | none =>
      if es.any (fun e : Elem ↦ e.gap) then none
      else (es.mapM fun e : Elem ↦ e.width).map fun w ↦ w.sum + w.length - 1 + 2
  (l.1.lead, ⟨l.1.gap, false, l.2.isSome, w, fun c trail acc ↦
    match l.2 with
    | some s => (acc, c + s.length)
    | none =>
      let fits := match w with
        | some w => decide (c + w + trail ≤ lim)
        | none => false
      let ind := c + if (es.head?.map (·.isAtom)).getD false then 2 else 1
      let s := es.foldl (planElem lim ind es.length trail fits) ⟨c + 1, false, false, 0, acc⟩
      let rpCol := if s.afterComment then ind else s.col
      (s.out.push (false, ind), rpCol + 1)⟩)

/-- The layout of a document within a line width, as the choices at the positions of its
tokens: each element after the first, an S-expression or a comment line, begins a line at the
first column, and each is laid out by {name}`planStep`. -/
def defaultLayout (lim : ℕ) (d : Doc) : Array (Bool × ℕ) :=
  (elemsOf (d.items.map (RoseTree.elim (planStep lim))) d.trail).foldl
    (fun (acc : Array (Bool × ℕ) × Bool) e ↦ ((e.plan 0 0 (acc.1.push (acc.2, 0))).1, true))
    (#[], false) |>.1

/-- A document printed at the choices of a layout, positions beyond them choosing no line
break. -/
def printAt (ds : Array (Bool × ℕ)) (d : Doc) : List Char :=
  print (fun i ↦ ds.getD i (false, 0)) d

/-- The formatter: a text read and printed within a line width, or nothing when its
parentheses do not balance. -/
def format (lim : ℕ) (text : List Char) : Option (List Char) :=
  (readDoc text).bind fun d ↦ if d.wf then some (printAt (defaultLayout lim d) d) else none

/-- The formatter is idempotent: formatting a formatted text gives it back. -/
theorem format_format (lim : ℕ) (text out : List Char) (h : format lim text = some out) :
    format lim out = some out := by
  unfold format at h
  obtain ⟨d, hr, hout⟩ := Option.bind_eq_some_iff.mp h
  by_cases hw : d.wf = true
  · simp only [hw, ↓reduceIte, Option.some.injEq] at hout
    subst hout
    simp only [format, printAt, readDoc_print _ d hw, Option.bind_some, hw, ↓reduceIte]
  · simp [hw] at hout

end Geb.Kernel.Document

end
