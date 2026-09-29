/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Reader

set_option doc.verso true in
/-!
# Source documents of the kernel's readable syntax

A source document is the text of a program read without loss of anything a person wrote but
the widths of its whitespace: its S-expressions, its comment lines and the empty lines between
its items. It is a list of items, each a rose tree whose label records whether an empty line
precedes the item and whether it is an atom, a list or a comment line, a list's items being its
children. Comments are items in document order rather than annotations of the nodes they
precede, as in the lossless syntax trees of formatters, so reading attaches no comment to any
node, and attaching one is a separate function of the document.

The reader {lit}`readDoc` is a conservative refinement of the kernel's reader
{name}`Geb.Kernel.readSExps`: erasing the comments of what it reads gives what that reader
reads, at every text ({lit}`readDoc_erase`). The printer {lit}`print` is parameterized by a
layout, a choice at each token of whether a line break precedes it and of the indentation of
the new line, and the retraction law holds at every layout ({lit}`readDoc_print`): reading a
printed well-formed document gives the document back. A formatter, reading and printing with a
layout computed from the document, is therefore idempotent ({lit}`format_format`), whatever the
layout policy, so the policy is not part of what is proved.

## Main definitions

* {lit}`Item` — the items of a source document.
* {lit}`lex`, {lit}`readDoc` — the lexer and reader keeping comments and empty lines.
* {lit}`sepFor`, {lit}`arrange`, {lit}`print` — the separators a layout chooses, and the
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

## Tags

S-expression, comments, formatter, retraction, lossless syntax tree
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document

/-- What an item of a source document is. -/
inductive Kind where
  /-- An atom, with its characters. -/
  | atom (s : List Char)
  /-- A list, whose elements are the item's children. -/
  | list
  /-- A comment line, with its characters after the semicolon and before the end of the line. -/
  | comment (s : List Char)
  deriving DecidableEq, Repr

/-- The label of an item: whether an empty line precedes it, and what it is. -/
@[ext] structure Lab where
  /-- Whether an empty line precedes the item. -/
  gap : Bool
  /-- What the item is. -/
  kind : Kind
  deriving DecidableEq, Repr

/-- An item of a source document. -/
abbrev Item : Type := RoseTree Lab

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

/-- A frame of the reader's stack: whether an empty line precedes the list being read, and its
items read so far, the latest first. -/
abbrev Frame : Type := Bool × List Item

/-- Read one token into a stack of lists under construction, the innermost first. A comment
read where no list is open leaves the empty stack as it is, as the kernel's reader leaves it. -/
def readStep : Option (List Frame) → Tok → Option (List Frame)
  | some fs, .lp g => some ((g, []) :: fs)
  | some ((g, f) :: fs), .atom h s => some ((g, RoseTree.node ⟨h, .atom s⟩ [] :: f) :: fs)
  | some ((g, f) :: fs), .comment h s => some ((g, RoseTree.node ⟨h, .comment s⟩ [] :: f) :: fs)
  | some ((g, f) :: (h, e) :: fs), .rp => some ((h, RoseTree.node ⟨g, .list⟩ f.reverse :: e) :: fs)
  | some [], .comment _ _ => some []
  | _, _ => none

/-- The items of a text, or nothing when its parentheses do not balance. -/
def readDoc (text : List Char) : Option (List Item) :=
  match (lex text).foldl readStep (some [(false, [])]) with
  | some [(_, f)] => some f.reverse
  | _ => none

/-- The S-expression an item erases to: an atom to itself and a list to the list of its
elements erased; a comment erases to nothing. -/
def eraseItem : Item → Option SExp :=
  RoseTree.elim fun l rs ↦
    match l.kind with
    | .atom s => some (RoseTree.node (some s) [])
    | .list => some (RoseTree.node none rs.reduceOption)
    | .comment _ => none

/-- The stack of the kernel's reader a stack of frames erases to. -/
def eraseStack : Option (List Frame) → Option (List (List SExp)) :=
  Option.map (List.map fun p ↦ p.2.filterMap eraseItem)

/-- The list of an item's erased elements, in order. -/
theorem eraseItem_list (g : Bool) (f : List Item) :
    eraseItem (RoseTree.node ⟨g, .list⟩ f.reverse) =
      some (RoseTree.node none (f.filterMap eraseItem).reverse) := by
  simp only [eraseItem, RoseTree.elim_node, List.reduceOption, List.filterMap_map,
    Function.comp_def, id, List.filterMap_reverse]

/-- An atom erases to itself. -/
theorem eraseItem_atom (g : Bool) (s : List Char) :
    eraseItem (RoseTree.node ⟨g, .atom s⟩ []) = some (RoseTree.node (some s) []) := by
  simp [eraseItem]

/-- A comment erases to nothing. -/
theorem eraseItem_comment (g : Bool) (s : List Char) :
    eraseItem (RoseTree.node ⟨g, .comment s⟩ []) = none := by
  simp [eraseItem]

/-- One token read by the reader and, erased, by the kernel's reader from corresponding stacks
gives corresponding stacks. -/
theorem eraseStack_readStep (st : Option (List Frame)) (t : Tok) :
    eraseStack (readStep st t) =
      match t.erase with
      | none => eraseStack st
      | some u => parseStep (eraseStack st) u := by
  rcases st with _ | _ | ⟨⟨g, f⟩, _ | ⟨⟨h, e⟩, fs⟩⟩ <;> cases t <;>
    simp [readStep, parseStep, eraseStack, Tok.erase, eraseItem_list, eraseItem_atom,
      eraseItem_comment]

/-- Reading tokens, erased, by the kernel's reader from an erased stack gives the erasure of
reading them from the stack. -/
theorem foldl_readStep (toks : List Tok) :
    ∀ st, eraseStack (toks.foldl readStep st) =
      (toks.filterMap Tok.erase).foldl parseStep (eraseStack st) :=
  List.rec (fun _ ↦ rfl) (fun t rest ih st ↦ by
    rw [List.foldl_cons, ih, eraseStack_readStep]
    cases h : t.erase <;> simp [h]) toks

/-- The reader keeps what the kernel's reader reads: erasing the comments of the items of a
text gives the text's S-expressions. -/
theorem readDoc_erase (text : List Char) :
    (readDoc text).map (·.filterMap eraseItem) = readSExps text := by
  have h := foldl_readStep (lex text) (some [(false, [])])
  simp only [eraseStack, Option.map_some, List.map_cons, List.filterMap_nil, List.map_nil] at h
  simp only [readDoc, readSExps, tokenize_eq, ← h]
  rcases (lex text).foldl readStep (some [(false, [])]) with _ | _ | ⟨⟨g, f⟩, _ | ⟨_, _⟩⟩ <;>
    simp [List.filterMap_reverse]

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

/-- The tokens of an item. -/
def tokensOf : Item → List Tok :=
  RoseTree.elim fun l rs ↦
    match l.kind with
    | .atom s => [.atom l.gap s]
    | .comment s => [.comment l.gap s]
    | .list => .lp l.gap :: rs.flatten ++ [.rp]

/-- A document's characters, laid out by a layout, a choice at each position of the document's
tokens; the text ends with a line break. -/
def print (L : ℕ → Bool × ℕ) (items : List Item) : List Char :=
  render (arrangeFrom L (items.flatMap tokensOf) none 0) ++ ['\n']

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

/-- The lexer reads back the tokens of a printed document, whatever the layout. -/
theorem lex_print (L : ℕ → Bool × ℕ) (items : List Item)
    (h : (items.flatMap tokensOf).all Tok.wf) :
    lex (print L items) = items.flatMap tokensOf := by
  have h' := lexEnd_arrangeFrom L _ h none 0 [] rfl
  simp only [pendOf, Option.toList_none, List.reverse_nil, List.nil_append] at h'
  exact h'

/-! ## Reading what the printer writes -/

/-- Whether an item can be printed and read back: every atom is a non-empty word of atom
characters and has no children, and every comment contains no line break and has no
children. -/
def wf : Item → Bool :=
  RoseTree.elim fun l rs ↦
    match l.kind with
    | .atom s => rs.isEmpty && (Tok.atom l.gap s).wf
    | .comment s => rs.isEmpty && (Tok.comment l.gap s).wf
    | .list => rs.all id

/-- The tokens of an atom. -/
theorem tokensOf_atom (g : Bool) (s : List Char) (cs : List Item) :
    tokensOf (RoseTree.node ⟨g, .atom s⟩ cs) = [.atom g s] := by
  simp [tokensOf]

/-- The tokens of a comment. -/
theorem tokensOf_comment (g : Bool) (s : List Char) (cs : List Item) :
    tokensOf (RoseTree.node ⟨g, .comment s⟩ cs) = [.comment g s] := by
  simp [tokensOf]

/-- The tokens of a list: its parentheses around the tokens of its elements. -/
theorem tokensOf_list (g : Bool) (cs : List Item) :
    tokensOf (RoseTree.node ⟨g, .list⟩ cs) = .lp g :: cs.flatMap tokensOf ++ [.rp] := by
  simp [tokensOf, List.flatMap_def]

/-- A list is well formed when its elements are. -/
theorem wf_list (g : Bool) (cs : List Item) :
    wf (RoseTree.node ⟨g, .list⟩ cs) = cs.all wf := by
  simp [wf, List.all_map]

/-- A well-formed atom has no children. -/
theorem wf_atom (g : Bool) (s : List Char) (cs : List Item) :
    wf (RoseTree.node ⟨g, .atom s⟩ cs) = (cs.isEmpty && (Tok.atom g s).wf) := by
  simp [wf]

/-- A well-formed comment has no children. -/
theorem wf_comment (g : Bool) (s : List Char) (cs : List Item) :
    wf (RoseTree.node ⟨g, .comment s⟩ cs) = (cs.isEmpty && (Tok.comment g s).wf) := by
  simp [wf]

/-- The tokens of a well-formed item can be printed and read back. -/
theorem all_wf_tokensOf : ∀ t : Item, wf t → (tokensOf t).all Tok.wf :=
  RoseTree.ind fun l cs ih h ↦ by
    obtain ⟨g, kind⟩ := l
    cases kind with
    | atom s =>
      rw [wf_atom, Bool.and_eq_true] at h
      simp [tokensOf_atom, h.2]
    | comment s =>
      rw [wf_comment, Bool.and_eq_true] at h
      simp [tokensOf_comment, h.2]
    | list =>
      rw [wf_list, List.all_eq_true] at h
      simp only [tokensOf_list, List.all_cons, List.all_append, List.all_flatMap, Tok.wf,
        Bool.true_and, List.all_nil, Bool.and_true, List.all_eq_true]
      exact fun c hc ↦ List.all_eq_true.mp (ih c hc (h c hc))

/-- Reading the tokens of well-formed items onto a frame adds the items to it. -/
theorem foldl_readStep_items (cs : List Item)
    (ih : ∀ t ∈ cs, wf t → ∀ g f fs,
      (tokensOf t).foldl readStep (some ((g, f) :: fs)) = some ((g, t :: f) :: fs))
    (hcs : ∀ c ∈ cs, wf c) :
    ∀ g f fs, (cs.flatMap tokensOf).foldl readStep (some ((g, f) :: fs)) =
      some ((g, cs.reverse ++ f) :: fs) :=
  List.rec (motive := fun cs ↦ (∀ t ∈ cs, wf t → ∀ g f fs,
      (tokensOf t).foldl readStep (some ((g, f) :: fs)) = some ((g, t :: f) :: fs)) →
      (∀ c ∈ cs, wf c) → ∀ g f fs,
      (cs.flatMap tokensOf).foldl readStep (some ((g, f) :: fs)) =
        some ((g, cs.reverse ++ f) :: fs))
    (fun _ _ _ _ _ ↦ rfl)
    (fun c cs ihl ih hcs g f fs ↦ by
      rw [List.flatMap_cons, List.foldl_append,
        ih c List.mem_cons_self (hcs c List.mem_cons_self),
        ihl (fun t ht ↦ ih t (List.mem_cons_of_mem c ht))
          (fun d hd ↦ hcs d (List.mem_cons_of_mem c hd))]
      simp) cs ih hcs

/-- Reading the tokens of a well-formed item onto a frame adds the item to it. -/
theorem foldl_readStep_tokensOf : ∀ t : Item, wf t → ∀ g f fs,
    (tokensOf t).foldl readStep (some ((g, f) :: fs)) = some ((g, t :: f) :: fs) :=
  RoseTree.ind fun l cs ih h g f fs ↦ by
    obtain ⟨gap, kind⟩ := l
    cases kind with
    | atom s =>
      rw [wf_atom, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨rfl, -⟩ := h
      simp [tokensOf_atom, readStep]
    | comment s =>
      rw [wf_comment, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨rfl, -⟩ := h
      simp [tokensOf_comment, readStep]
    | list =>
      rw [wf_list, List.all_eq_true] at h
      have hlp : readStep (some ((g, f) :: fs)) (.lp gap) = some ((gap, []) :: (g, f) :: fs) :=
        rfl
      rw [tokensOf_list, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, hlp]
      rw [foldl_readStep_items cs ih h gap [] ((g, f) :: fs)]
      simp [readStep]

/-- The retraction law: reading a document printed at any layout gives the document back,
when its items are well formed. -/
theorem readDoc_print (L : ℕ → Bool × ℕ) (items : List Item) (h : items.all wf) :
    readDoc (print L items) = some items := by
  have hw : ∀ c ∈ items, wf c := List.all_eq_true.mp h
  have htoks : (items.flatMap tokensOf).all Tok.wf := by
    simp only [List.all_flatMap, List.all_eq_true]
    exact fun c hc ↦ List.all_eq_true.mp (all_wf_tokensOf c (hw c hc))
  rw [readDoc, lex_print L items htoks,
    foldl_readStep_items items (fun t _ ↦ foldl_readStep_tokensOf t) hw false [] []]
  simp

/-! ## A layout policy and the formatter -/

/-- Whether an item is a comment. -/
def Lab.isComment (l : Lab) : Bool :=
  match l.kind with
  | .comment _ => true
  | _ => false

/-- Whether an item is an atom. -/
def Lab.isAtom (l : Lab) : Bool :=
  match l.kind with
  | .atom _ => true
  | _ => false

/-- The width of an item printed on one line, or nothing when it cannot be: when it contains
a comment, or an item after an empty line. -/
def flatWidthStep (l : Lab) (ws : List (Lab × Option ℕ)) : Option ℕ :=
  match l.kind with
  | .atom s => some s.length
  | .comment _ => none
  | .list =>
    if ws.any (fun p : Lab × Option ℕ ↦ p.1.gap) then none
    else (ws.mapM fun p : Lab × Option ℕ ↦ p.2).map fun w ↦ w.sum + w.length - 1 + 2

/-- A layout from the column an item's first character is written at and the number of
closing parentheses that follow the item on its line: it appends the choices for the item's
tokens after the first to those made before, and gives the column after the item. -/
abbrev Plan : Type := ℕ → ℕ → Array (Bool × ℕ) → Array (Bool × ℕ) × ℕ

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
width, given the list's number of elements and the closing parentheses that follow the list,
and the element's label, width on one line and own layout. The element begins a line when the
list does not fit on one, when it or the element before is a comment, when a line was broken
before an earlier element after the first, or when it and the parentheses that follow it do
not fit on the current line; the first element begins one only when it or the element before
is a comment. -/
def planElem (lim ind n trail : ℕ) (fits : Bool) (s : PlanState) (e : Lab × Option ℕ × Plan) :
    PlanState :=
  let (l, w, plan) := e
  let after := if s.pos + 1 == n then trail + 1 else 0
  let brk : Bool :=
    if fits || s.pos == 0 then l.isComment || s.afterComment
    else l.isComment || s.afterComment || s.broken ||
      match w with
      | some w => lim < s.col + 1 + w + after
      | none => true
  let start := if brk || l.gap || s.afterComment then ind else if s.pos == 0 then s.col
    else s.col + 1
  let (out, endCol) := plan start after (s.out.push (brk, ind))
  ⟨endCol, s.broken || (brk && s.pos != 0) || l.gap, l.isComment, s.pos + 1, out⟩

/-- An item's label, its width on one line, and its layout. A list that fits within the line
width is written on one line; otherwise its elements after the first fill the first line while
they fit, and the rest begin lines indented past the list's opening parenthesis, by two columns
after an atom at its head and by one otherwise, so that no line is indented beyond a
parenthesis closed at the end of the line before. -/
def planStep (lim : ℕ) (l : Lab) (rs : List (Lab × Option ℕ × Plan)) : Lab × Option ℕ × Plan :=
  let w := flatWidthStep l (rs.map fun r ↦ (r.1, r.2.1))
  (l, w, fun c trail acc ↦
    match l.kind with
    | .atom s => (acc, c + s.length)
    | .comment s => (acc, c + 1 + s.length)
    | .list =>
      let fits := match w with
        | some w => decide (c + w + trail ≤ lim)
        | none => false
      let ind := c + if (rs.head?.map (·.1.isAtom)).getD false then 2 else 1
      let s := rs.foldl (planElem lim ind rs.length trail fits) ⟨c + 1, false, false, 0, acc⟩
      let rpCol := if s.afterComment then ind else s.col
      (s.out.push (false, ind), rpCol + 1))

/-- The layout of a document within a line width, as the choices at the positions of its
tokens: each item after the first begins a line at the first column, and each is laid out by
{name}`planStep`. -/
def defaultLayout (lim : ℕ) (items : List Item) : Array (Bool × ℕ) :=
  (items.foldl (fun (acc : Array (Bool × ℕ) × Bool) t ↦
      (((RoseTree.elim (planStep lim) t).2.2 0 0 (acc.1.push (acc.2, 0))).1, true))
    (#[], false)).1

/-- A document printed at the choices of a layout, positions beyond them choosing no line
break. -/
def printAt (ds : Array (Bool × ℕ)) (items : List Item) : List Char :=
  print (fun i ↦ ds.getD i (false, 0)) items

/-- The formatter: a text read and printed within a line width, or nothing when its
parentheses do not balance. -/
def format (lim : ℕ) (text : List Char) : Option (List Char) :=
  (readDoc text).bind fun items ↦
    if items.all wf then some (printAt (defaultLayout lim items) items) else none

/-- The formatter is idempotent: formatting a formatted text gives it back. -/
theorem format_format (lim : ℕ) (text out : List Char) (h : format lim text = some out) :
    format lim out = some out := by
  unfold format at h
  obtain ⟨items, hr, hout⟩ := Option.bind_eq_some_iff.mp h
  by_cases hw : items.all wf = true
  · simp only [hw, ↓reduceIte, Option.some.injEq] at hout
    subst hout
    simp only [format, printAt, readDoc_print _ items hw, Option.bind_some, hw, ↓reduceIte]
  · simp [hw] at hout

end Geb.Kernel.Document

end
