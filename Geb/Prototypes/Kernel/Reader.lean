/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Basic

set_option doc.verso true in
/-!
# The kernel's readable syntax

A program is a sequence of definitions written as S-expressions, {lit}`(def name term)`, each
term referring to the definitions before it by name, and of type abbreviations
{lit}`(deftype name type)`, each in force after it. Reading has two stages: a text is read
as S-expressions, a rose tree whose leaves carry atoms and whose other nodes are lists; each
S-expression is then resolved into a kernel term, variable names becoming de Bruijn indices,
definition names references, and keywords the kernel's constructors. Loading type-checks
and evaluates the definitions in order, each in the global environment of those before it.

The forms of a term:

* a numeral {lit}`n` is the quoted leaf of label {lit}`n`; {lit}`unit` is the unit value;
  a bound name is a variable, a defined name a reference, and a primitive's name the
  primitive;
* {lit}`(lam (x A) body)` is an abstraction binding {lit}`x` of type {lit}`A`, and
  {lit}`(lam ((x₁ A₁) … (xₙ Aₙ)) body)` the nested abstractions binding each in turn;
  {lit}`(let x A e body)` is the abstraction binding {lit}`x` in {lit}`body` applied to
  {lit}`e`;
  {lit}`(pair a b)`, {lit}`(fst p)`, {lit}`(snd p)`, {lit}`(if c a b)` and
  {lit}`(quote d)` are the corresponding constructors, a datum being a numeral or a list
  {lit}`(n d₁ … dₖ)` of a label and children;
* {lit}`(nil A)` is the empty list of elements of type {lit}`A` and {lit}`(cons x xs)` the
  list of a head and a tail;
* {lit}`(fold A x₁ … xₖ)`, {lit}`(iter A x₁ … xₖ)`, {lit}`(foldr A B x₁ … xₖ)` and
  {lit}`(lcase A B x₁ … xₖ)` apply the fold of trees, the iteration, the right fold of lists
  and the case analysis of lists at the given types to their arguments, and any other list
  {lit}`(f x₁ … xₖ)` applies {lit}`f` to its arguments in turn.

Types are {lit}`T`, {lit}`Unit`, {lit}`(Prod A B)`, {lit}`(Arrow A B)`,
{lit}`(List A)` and the names of type abbreviations. A semicolon begins a comment that
extends to the end of its line.

## Main definitions

* {lit}`SExp`, {lit}`readSExps` — S-expressions and the reader of a text.
* {lit}`resolve` — the resolution of an S-expression into a kernel term.
* {lit}`readProgram`, {lit}`load` — a program's definitions as named terms, and their
  meanings.
* {lit}`runMain` — the application of a program's last definition to an input tree.

## Implementation notes

Both stages are folds: the tokenizer and the parser fold over the text with an explicit
stack, and resolution is a fold over the S-expression whose result is a function of the
names in scope. Text is a list of characters and atoms are lists of characters, compared
with keywords through {name}`String.ofList`: core's {lit}`String.toList`, and the numeral
parser built on it, depend on {lit}`Classical.choice`, which this module avoids.

## Tags

bootstrap, kernel, S-expression, reader, name resolution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

/-- An S-expression: a leaf carries an atom, and a node without a label is a list. -/
abbrev SExp : Type := RoseTree (Option (List Char))

/-- The tokens of S-expression text. -/
inductive Token
  /-- An opening parenthesis. -/
  | lp
  /-- A closing parenthesis. -/
  | rp
  /-- An atom. -/
  | atom (s : List Char)

/-- The tokenizer's state: the tokens read, the atom being read, and whether a comment is
being skipped, the first two in reverse. -/
abbrev TokState : Type := List Token × List Char × Bool

/-- End the atom being read, if any. -/
def flush : TokState → TokState
  | (ts, [], c) => (ts, [], c)
  | (ts, cs, c) => (.atom cs.reverse :: ts, [], c)

/-- Read one character. -/
def tokStep (s : TokState) (ch : Char) : TokState :=
  if s.2.2 then (s.1, s.2.1, ch != '\n')
  else if ch == ';' then let (ts, cs, _) := flush s; (ts, cs, true)
  else if ch == '(' then let (ts, cs, c) := flush s; (.lp :: ts, cs, c)
  else if ch == ')' then let (ts, cs, c) := flush s; (.rp :: ts, cs, c)
  else if ch.isWhitespace then flush s
  else (s.1, ch :: s.2.1, false)

/-- The tokens of a text. -/
def tokenize (text : List Char) : List Token :=
  (flush (text.foldl tokStep ([], [], false))).1.reverse

/-- Read one token into a stack of lists under construction, the innermost first and each
list's elements in reverse. -/
def parseStep : Option (List (List SExp)) → Token → Option (List (List SExp))
  | some fs, .lp => some ([] :: fs)
  | some (f :: fs), .atom s => some ((RoseTree.node (some s) [] :: f) :: fs)
  | some (f :: g :: fs), .rp => some ((RoseTree.node none f.reverse :: g) :: fs)
  | _, _ => none

/-- The S-expressions of a text, or nothing when its parentheses do not balance. -/
def readSExps (text : List Char) : Option (List SExp) :=
  match (tokenize text).foldl parseStep (some [[]]) with
  | some [f] => some f.reverse
  | _ => none

/-- The label a numeral denotes: a non-empty list of decimal digits. -/
def numeral? (s : List Char) : Option ℕ :=
  if s.isEmpty then none
  else s.foldl (fun n c ↦ n.bind fun n ↦
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- The names of the primitives, in the order of {name}`prims`. -/
def primNames : List String :=
  ["label", "arity", "child", "node", "children", "add", "sub", "mul", "div", "mod", "eq",
   "lt", "equal", "log2"]

/-- Type abbreviations: names with the types they abbreviate, the latest first. -/
abbrev TypeNames : Type := List (List Char × Tree)

/-- An S-expression read as a type, given the type abbreviations in force, with its atom if it
is one. -/
def readType (tys : TypeNames) : SExp → Option Tree :=
  fun e ↦ (RoseTree.elim (β := Option String × Option Tree) (fun a rs ↦
    match a.map String.ofList, rs with
    | some "T", _ => (some "T", some tT)
    | some "Unit", _ => (some "Unit", some tUnit)
    | some s, _ => (some s, a.bind fun n ↦ List.lookup n tys)
    | none, [(some "Prod", _), (_, some A), (_, some B)] => (none, some (tProd A B))
    | none, [(some "Arrow", _), (_, some A), (_, some B)] => (none, some (tArrow A B))
    | none, [(some "List", _), (_, some A)] => (none, some (tList A))
    | none, _ => (none, none)) e).2

/-- An S-expression read as a quoted datum: a numeral is a leaf, and a list of a numeral and
data is a node. -/
def readDatum : SExp → Option Tree :=
  fun e ↦ (RoseTree.elim (β := Option ℕ × Option Tree) (fun a rs ↦
    match a, rs with
    | some s, _ => ((numeral? s), (numeral? s).map leaf)
    | none, (some l, _) :: ds => (none, (ds.mapM Prod.snd).map (RoseTree.node l))
    | _, _ => (none, none)) e).2

/-- A node of the kernel over a list of children. -/
abbrev mk (l : ℕ) (cs : List Tree) : Tree := RoseTree.node l cs

/-- A term applied to arguments in turn. -/
def apps (f : Tree) (xs : List Tree) : Tree := xs.foldl (fun g x ↦ mk 10 [g, x]) f

/-- The binders of an abstraction: one binder {lit}`(x A)`, or a list of them. -/
def binders (b : SExp) : List SExp :=
  match b.children with
  | [x, _] => if x.label.isSome then [b] else b.children
  | bs => bs

/-- Resolve one S-expression node: its atom or its elements, each with its resolution as a
function of the names bound around it. -/
def resolveStep (tys : TypeNames) (defs : List (List Char)) (a : Option (List Char))
    (cs : List (SExp × (List (List Char) → Option Tree))) (scope : List (List Char)) :
    Option Tree :=
  let args (xs : List (SExp × (List (List Char) → Option Tree))) := xs.mapM (·.2 scope)
  match a, cs with
  | some s, _ =>
    match numeral? s, scope.idxOf? s, defs.idxOf? s, primNames.idxOf? (String.ofList s) with
    | some n, _, _, _ => some (mk 15 [leaf n])
    | _, some i, _, _ => some (mk 8 [leaf i])
    | _, _, some j, _ => some (mk 23 [leaf j])
    | _, _, _, some k => some (mk 22 [leaf k])
    | _, _, _, _ => if String.ofList s == "unit" then some (mk 11 []) else none
  | none, (h, rh) :: rest =>
    match h.label.map String.ofList, rest with
    | some "lam", [(b, _), (_, body)] => do
      let bs ← (binders b).mapM fun c ↦
        match c.children with
        | [x, A] => do some (← x.label, ← readType tys A)
        | _ => none
      if bs.isEmpty then none
      else
        let t ← body ((bs.map Prod.fst).reverse ++ scope)
        some (bs.foldr (fun p u ↦ mk 9 [p.2, u]) t)
    | some "let", [(x, _), (A, _), (_, e), (_, body)] => do
      let name ← x.label
      some (mk 10 [mk 9 [← readType tys A, ← body (name :: scope)], ← e scope])
    | some "pair", _ => (args rest).map (mk 12)
    | some "fst", _ => (args rest).map (mk 13)
    | some "snd", _ => (args rest).map (mk 14)
    | some "if", _ => (args rest).map (mk 16)
    | some "quote", [(d, _)] => (readDatum d).map fun t ↦ mk 15 [t]
    | some "cons", _ => (args rest).map (mk 20)
    | some "nil", [(A, _)] => (readType tys A).map fun A ↦ mk 19 [A]
    | some "fold", (A, _) :: xs => do apps (mk 17 [← readType tys A]) (← args xs)
    | some "iter", (A, _) :: xs => do apps (mk 18 [← readType tys A]) (← args xs)
    | some "foldr", (A, _) :: (B, _) :: xs => do
      apps (mk 21 [← readType tys A, ← readType tys B]) (← args xs)
    | some "lcase", (A, _) :: (B, _) :: xs => do
      apps (mk 24 [← readType tys A, ← readType tys B]) (← args xs)
    | _, _ => do apps (← rh scope) (← args rest)
  | none, [] => none

/-- Resolve an S-expression into a kernel term, given the type abbreviations in force, the
names of the definitions before it and the names bound around it. -/
def resolve (tys : TypeNames) (defs : List (List Char)) (e : SExp) (scope : List (List Char)) :
    Option Tree :=
  RoseTree.para (resolveStep tys defs) e scope

/-- The definitions of a program, as names with kernel terms; type abbreviations are expanded
where they are used. -/
def readProgram (text : List Char) : Option (List (List Char × Tree)) := do
  let es ← readSExps text
  let step (acc : Option (TypeNames × List (List Char × Tree))) (e : SExp) :
      Option (TypeNames × List (List Char × Tree)) := do
    let (tys, ds) ← acc
    match e.children with
    | [kw, n, body] => do
      let name ← n.label
      match kw.label.map String.ofList with
      | some "def" => some (tys, ds ++ [(name, ← resolve tys (ds.map Prod.fst) body [])])
      | some "deftype" => some ((name, ← readType tys body) :: tys, ds)
      | _ => none
    | _ => none
  (es.foldl step (some ([], []))).map Prod.snd

/-- The meanings of a program's definitions, each checked and evaluated in the global
environment of those before it. -/
def load (ds : List Tree) : Option (List Glob) :=
  ds.foldl (fun acc t ↦ do
    let G ← acc
    let m ← infer G [] t
    some (G ++ [⟨m.1, m.2 ()⟩])) (some [])

/-- Apply the last definition of a program, of type {lit}`T → T`, to an input tree. -/
def runMain (text : List Char) (input : Tree) : Option Tree := do
  let ds ← readProgram text
  let G ← load (ds.map Prod.snd)
  (← G.getLast?).apply input

end Geb.Kernel

end
