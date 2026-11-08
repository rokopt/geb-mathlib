/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Modules
public import Geb.Prototypes.Kernel.Printer
public import Geb.Prototypes.Kernel.Strict
public import Geb.Prototypes.Kernel.Subst
public import Geb.Prototypes.RoseTree.Unify
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Checking a program with holes

A hole is the form {lit}`(hole name)`, written {lit}`?name`, at the position of a term. A hole
of a program stands for a term in the context of its declaring occurrence, the first in the
program's order, whose binders are its context: a hole is a metavariable of contextual modal
type theory {cite}`NanevskiPfenningPientka2008`, whose occurrences carry explicit substitutions
from its context. Every occurrence of a named hole is one obligation, and an occurrence elsewhere
than the declaring one substitutes, for each variable of the hole's context, the variable of the
same name in its own scope.

The checker lifts the holes out of the program. The occurrence of a hole whose context binds
{lit}`x₁ … xₖ`, the outermost first, becomes the application {lit}`(?name x₁ … xₖ)` of a
variable bound around every definition, so that the hole stands for a function of its context,
and the kernel's resolution of names makes each definition a kernel term in which the holes are
the outermost free variables. A hole's expected type is a metavariable, and its variable's type
the function type from its context's types to it. The typing of the kernel's terms is then a
list of equations between types, solved by unification {cite}`Wand1987`
{cite}`Robinson1965`: each application, projection, conditional and list a term builds requires
an equation, and a definition's type is a type with metavariables, which the definitions after it
constrain further. The equations that mention a hole's metavariable are the checks its unknown
filling suspends, and their solution is the hole's goal.

A program is accepted with its holes when the equations unify within a budget of steps and its
completion loads: each hole replaced by the closure over its context of a term of its expected
type, each remaining metavariable read as {lit}`T`, and the program checked by
{name}`Geb.Kernel.load`, the trusted checker, which this module leaves unchanged. Every accepted
program therefore has a completion that the kernel accepts, so the holes it reports are
obligations that can be met, and a program with holes is accepted exactly when one completion of
its lambda-lifting checks. A program without holes is its own completion, and is reported as
complete; a program with an open hole is not.

## Main definitions

* {lit}`Scope`, {lit}`Decl` — the binders around a position, and a hole with its context.
* {lit}`occStep`, {lit}`liftStep` — the search for holes and the lifting of their occurrences.
* {lit}`gen` — the equations of a term's typing, with metavariables for the types the kernel's
  terms do not annotate.
* {lit}`dflt`, {lit}`closure`, {lit}`completeTerm` — a term of each type, the closure of a term
  over a context, and the replacement of a program's holes by closures.
* {lit}`Hole`, {lit}`Report`, {lit}`check` — the obligations of a program and their check.
* {lit}`Report.render` — the display of the obligations, a hole as {lit}`?name` and a type
  that no equation determines with its metavariables, each {lit}`(meta i)`.

## Main statements

* {lit}`load_completion` — the completion of every accepted program loads.

## Implementation notes

The work the holes suspend is the list of equations, a finite list of items each of which
unification resumes as the metavariables it mentions are assigned, within a budget whose
exhaustion is reported apart from ill-typing. The kernel's types are simple, so the type at a
hole's position never depends on the term that fills it, and no check suspended on a hole is more
than an equation between types.

A hole's name lifted is {lit}`?name`, which no name the reader reads begins with, since
{lit}`?` begins the token of a hole; the checker rejects a program naming a binder or a
definition by a quoted atom beginning with {lit}`?`, which would capture a lifted hole.

## References

* {cite}`NanevskiPfenningPientka2008`
* {cite}`Wand1987`
* {cite}`Robinson1965`

## Tags

typed hole, metavariable, contextual modal type theory, type inference, unification, kernel
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Holes

open scoped FinEnum
open RoseTree (Meta mvar embed MSubst substM ground unify)

/-! ## Holes and their contexts -/

/-- The binders around a position: their names with their types, the innermost first. -/
abbrev Scope : Type := List (List Char × Tree)

/-- A hole: its name, and the binders around its declaring occurrence. -/
structure Decl where
  /-- The hole's name. -/
  name : List Char
  /-- The binders around the hole's declaring occurrence, the innermost first. -/
  context : Scope

/-- The name of the form of a hole, {lit}`(hole name)`. -/
def holeName? (e : SExp) : Option (List Char) :=
  match e.label, e.children with
  | none, [h, n] => if isKw h "hole" then n.label else none
  | _, _ => none

/-- Whether a name begins with {lit}`?`, as the lifted name of a hole does. -/
def isLifted (s : List Char) : Bool := s.head? == some '?'

/-- The binders of an abstraction as names with their types, given the type abbreviations in
force, when each is a name not beginning with {lit}`?` and a type. -/
def readBinders (tys : TypeNames) (b : SExp) : Option Scope :=
  (binders b).mapM fun c ↦
    match c.label, c.children with
    | none, [x, A] => do
      let s ← x.label
      if isLifted s then none else some (s, ← readType tys A)
    | _, _ => none

/-- One node of the search for holes: an atom contributes none, and is rejected when it begins
with {lit}`?`; a quotation contributes none; a hole contributes itself in the scope around it; an
abstraction and a binding contribute the holes of their parts, each in the scope the reader
resolves it in; every other list contributes its elements' holes. -/
def occStep (tys : TypeNames) (a : Option (List Char))
    (cs : List (SExp × (Scope → Option (List Decl)))) (scope : Scope) : Option (List Decl) :=
  let all := (cs.mapM (m := Option) fun c ↦ c.2 scope).map List.flatten
  match a, cs with
  | some s, _ => if isLifted s then none else some []
  | none, (h, _) :: rest =>
    if isKw h "quote" then some []
    else if isKw h "hole" then
      match rest with
      | [(n, _)] => n.label.map fun s ↦ [⟨s, scope⟩]
      | _ => none
    else if isKw h "lam" then
      match rest with
      | [(b, _), (_, body)] => do
        let bs ← readBinders tys b
        body (bs.reverse ++ scope)
      | _ => all
    else if isKw h "let" then
      match rest with
      | [(x, _), (A, _), (_, e), (_, body)] => do
        let s ← x.label
        if isLifted s then none
        else some ((← e scope) ++ (← body ((s, ← readType tys A) :: scope)))
      | _ => all
    else all
  | none, [] => some []

/-- The holes of a definition's body, in the order of their occurrences, each with its scope. -/
def occurrences (tys : TypeNames) (body : SExp) : Option (List Decl) :=
  RoseTree.para (occStep tys) body []

/-- The declarations of a program's holes: each name at its first occurrence. -/
def declare (occs : List Decl) : List Decl :=
  occs.foldl (fun ds o ↦ if ds.any (·.name == o.name) then ds else ds ++ [o]) []

/-- The lifted name of a hole. -/
def holeAtom (s : List Char) : List Char := '?' :: s

/-- One node of the lifting of holes: a hole becomes the application of its lifted name to the
names of its context, the outermost first, and a quotation is kept. -/
def liftStep (decls : List Decl) (a : Option (List Char)) (rs : List (SExp × SExp)) : SExp :=
  let orig := RoseTree.node a (rs.map Prod.fst)
  match holeName? orig, rs.head? with
  | some s, _ =>
    match decls.find? (·.name == s) with
    | some d => listS (atomS (holeAtom s) :: d.context.reverse.map fun p ↦ atomS p.1)
    | none => orig
  | none, some (h, _) =>
    if a.isNone && isKw h "quote" then orig else RoseTree.node a (rs.map Prod.snd)
  | none, none => RoseTree.node a (rs.map Prod.snd)

/-- A definition's body with its holes lifted. -/
def lift (decls : List Decl) : SExp → SExp := RoseTree.para (liftStep decls)

/-! ## Reading a program with holes -/

/-- A definition before resolution: its name, its body with numeral abbreviations expanded, and
the type abbreviations and the names of the definitions in force at it. -/
structure Pending where
  /-- The definition's name. -/
  name : List Char
  /-- The body, its numeral abbreviations expanded. -/
  body : SExp
  /-- The type abbreviations in force. -/
  tys : TypeNames
  /-- The names of the definitions before it. -/
  defs : List (List Char)

/-- One form of a program read after those before it, as {name}`Geb.Kernel.readFormStep` reads
it, a definition kept unresolved; a name beginning with {lit}`?` is rejected. -/
def pendStep (acc : Option (TypeNames × NumNames × List Pending)) (e : SExp) :
    Option (TypeNames × NumNames × List Pending) := do
  let (tys, nums, ps) ← acc
  match e.children with
  | [kw, n, body] => do
    let name ← n.label
    let taken := tys.map Prod.fst ++ nums.map Prod.fst ++ ps.map (·.name)
    guard (!isLifted name && isFresh taken name)
    match kw.label with
    | some ['d', 'e', 'f'] =>
      some (tys, nums, ps ++ [⟨name, expandNums nums body, tys, ps.map (·.name)⟩])
    | some ['d', 'e', 'f', 't', 'y', 'p', 'e'] =>
      some ((name, ← readType tys body) :: tys, nums, ps)
    | some ['d', 'e', 'f', 'n', 'u', 'm'] =>
      some (tys, (name, ← numOf nums body) :: nums, ps)
    | _ => none
  | _ => none

/-! ## The equations of a term's typing -/

/-- A node of a type with metavariables. -/
def con (l : ℕ) (cs : List (Meta ℕ)) : Meta ℕ := RoseTree.node (.inl l) cs

/-- The type of trees, with metavariables. -/
def mT : Meta ℕ := con Label.tyTree []

/-- The function type, with metavariables. -/
def mArrow (A B : Meta ℕ) : Meta ℕ := con Label.tyArrow [A, B]

/-- The product type, with metavariables. -/
def mProd (A B : Meta ℕ) : Meta ℕ := con Label.tyProd [A, B]

/-- The list type, with metavariables. -/
def mList (A : Meta ℕ) : Meta ℕ := con Label.tyList [A]

/-- Equations between types with metavariables. -/
abbrev Eqns : Type := List (Meta ℕ × Meta ℕ)

/-- The typing of a term, as a function of the types of the globals, the types of the context
and the next fresh metavariable: the term's type, the equations it requires, and the next fresh
metavariable after those it takes. -/
abbrev Gen : Type := List (Meta ℕ) → List (Meta ℕ) → ℕ → Option (Meta ℕ × Eqns × ℕ)

/-- One node of the typing, the rules of {name}`Geb.Kernel.inferStep` with an equation in place
of each comparison of types and a fresh metavariable for each type it reads from another. -/
def genStep (l : ℕ) (cs : List (Tree × Gen)) : Gen := fun GT Γ k ↦
  match l, cs with
  | Label.var, [(n, _)] => Γ[n.label]?.map fun A ↦ (A, [], k)
  | Label.lam, [(A, _), (_, b)] =>
    if Ty.IsTy A then (b GT (embed A :: Γ) k).map fun (B, es, k') ↦ (mArrow (embed A) B, es, k')
    else none
  | Label.app, [(_, f), (_, x)] => do
    let (F, e₁, k₁) ← f GT Γ k
    let (X, e₂, k₂) ← x GT Γ k₁
    some (mvar k₂, (F, mArrow X (mvar k₂)) :: e₁ ++ e₂, k₂ + 1)
  | Label.unit, [] => some (con Label.tyUnit [], [], k)
  | Label.pair, [(_, a), (_, b)] => do
    let (A, e₁, k₁) ← a GT Γ k
    let (B, e₂, k₂) ← b GT Γ k₁
    some (mProd A B, e₁ ++ e₂, k₂)
  | Label.fst, [(_, p)] => do
    let (P, e, k₁) ← p GT Γ k
    some (mvar k₁, (P, mProd (mvar k₁) (mvar (k₁ + 1))) :: e, k₁ + 2)
  | Label.snd, [(_, p)] => do
    let (P, e, k₁) ← p GT Γ k
    some (mvar (k₁ + 1), (P, mProd (mvar k₁) (mvar (k₁ + 1))) :: e, k₁ + 2)
  | Label.quote, [_] => some (mT, [], k)
  | Label.cond, [(_, c), (_, a), (_, b)] => do
    let (C, e₁, k₁) ← c GT Γ k
    let (A, e₂, k₂) ← a GT Γ k₁
    let (B, e₃, k₃) ← b GT Γ k₂
    some (A, (C, mT) :: (B, A) :: e₁ ++ e₂ ++ e₃, k₃)
  | Label.fold, [(A, _)] => if Ty.IsTy A then some (embed (foldTy A), [], k) else none
  | Label.iter, [(A, _)] => if Ty.IsTy A then some (embed (iterTy A), [], k) else none
  | Label.nil, [(A, _)] => if Ty.IsTy A then some (embed (tList A), [], k) else none
  | Label.cons, [(_, x), (_, xs)] => do
    let (X, e₁, k₁) ← x GT Γ k
    let (L, e₂, k₂) ← xs GT Γ k₁
    some (mList X, (L, mList X) :: e₁ ++ e₂, k₂)
  | Label.foldr, [(A, _), (B, _)] =>
    if Ty.IsTy A && Ty.IsTy B then some (embed (foldrTy A B), [], k) else none
  | Label.prim, [(n, _)] => prims[n.label]?.map fun g ↦ (embed g.1, [], k)
  | Label.ref, [(n, _)] => GT[n.label]?.map fun A ↦ (A, [], k)
  | Label.lcase, [(A, _), (B, _)] =>
    if Ty.IsTy A && Ty.IsTy B then some (embed (lcaseTy A B), [], k) else none
  | Label.para, [(A, _)] => if Ty.IsTy A then some (embed (foldTy A), [], k) else none
  | _, _ => none

/-- The typing of a term. -/
def gen (t : Tree) : Gen := RoseTree.para genStep t

/-- The type of a hole's lifted variable: the function type from its context's types, the
outermost first, to its expected type. -/
def varTy (d : Decl) (target : Meta ℕ) : Meta ℕ :=
  d.context.foldl (fun B p ↦ mArrow (embed p.2) B) target

/-! ## Completion -/

/-- One node of a term of each type: the quoted leaf of label zero, the unit value, a pair, an
abstraction over a term of its codomain, and the empty list. -/
def dfltStep (l : ℕ) (rs : List (Tree × Tree)) : Tree :=
  match l, rs with
  | Label.tyUnit, [] => mk Label.unit []
  | Label.tyProd, [(_, a), (_, b)] => mk Label.pair [a, b]
  | Label.tyArrow, [(A, _), (_, b)] => mk Label.lam [A, b]
  | Label.tyList, [(A, _)] => mk Label.nil [A]
  | _, _ => mk Label.quote [leaf 0]

/-- A closed term of a type. -/
def dflt : Tree → Tree := RoseTree.para dfltStep

/-- The closure of a term over a context: the abstraction over each of its binders, the
innermost innermost. -/
def closure (ctx : Scope) (t : Tree) : Tree := ctx.foldl (fun u p ↦ mk Label.lam [p.2, u]) t

/-- The replacement of a variable under binders: a bound variable is kept, and the variable of a
hole becomes that hole's closed term. -/
def fillVar (cs : List Tree) (k j : ℕ) : Tree :=
  if j < k then Tm.var j else (cs[j - k]?).getD (Tm.var j)

/-- A lifted definition with each hole replaced by a closed term. -/
def completeTerm (cs : List Tree) (t : Tree) : Tree := trav (fillVar cs) t 0

/-! ## The report of a program's holes -/

/-- A hole's obligation: its name, its context, and its expected type. -/
structure Hole where
  /-- The hole's name. -/
  name : List Char
  /-- The binders around its declaring occurrence, the innermost first. -/
  context : Scope
  /-- The type of the term it stands for, with the metavariables no equation determines. -/
  target : Meta ℕ

/-- The report of a program: its holes, the type of each definition, and the completion that the
kernel accepts. -/
structure Report where
  /-- The program's holes, in the order of their declaring occurrences. -/
  holes : List Hole
  /-- Each definition's name with its type. -/
  types : List (List Char × Meta ℕ)
  /-- The definitions with each hole replaced by the closure of a term of its type. -/
  completion : List Tree

/-- Whether a report is of a complete program, one without holes. -/
def Report.complete (r : Report) : Bool := r.holes.isEmpty

/-- The first definition that fails, by its name, or the results of all of them. -/
def eachDef {β : Type} (ps : List Pending) (f : Pending → Option β) (what : String) :
    Except String (List β) :=
  ps.mapM fun p ↦
    match f p with
    | some b => Except.ok b
    | none => Except.error s!"{String.ofList p.name} {what}"

/-- The typing of a program's lifted definitions in order, each in the types of those before it
and of the holes: the definitions' types and the equations, or the first definition that is
ill-typed. -/
def genProgram (holeTys : List (Meta ℕ)) (ps : List Pending) (ts : List Tree) (k : ℕ) :
    Except String (List (Meta ℕ) × Eqns) :=
  let step (acc : List (Meta ℕ) × Eqns × ℕ) (pt : Pending × Tree) :
      Except String (List (Meta ℕ) × Eqns × ℕ) :=
    match gen pt.2 acc.1 holeTys acc.2.2 with
    | some (A, e, k') => Except.ok (acc.1 ++ [A], acc.2.1 ++ e, k')
    | none => Except.error s!"{String.ofList pt.1.name} is ill-typed"
  ((ps.zip ts).foldlM step ([], [], k)).map fun r ↦ (r.1, r.2.1)

/-- The obligations of a program with holes, before the check of its completion: its holes with
their contexts and expected types, its definitions' types, and its completion; or the first
failure, of reading, of elaborating modules, of the forms, of resolving or typing a definition,
or of unifying within the budget. -/
def obligations (budget : ℕ) (text : List Char) : Except String Report := do
  let some es := readSExps text
    | .error "the text is not well formed or its parentheses do not balance"
  let fs := dropGeneric (← elabModules es)
  let some (_, _, ps) := fs.foldl pendStep (some ([], [], []))
    | .error "a form is not a def, a deftype nor a defnum, or its name is reserved, declared \
        before, or begins with ?"
  let occs ← eachDef ps (fun p ↦ occurrences p.tys p.body)
    "names an atom or a binder beginning with ?, a hole not by an atom, or a binder's type that \
      does not read"
  let decls := declare occs.flatten
  let ts ← eachDef ps (fun p ↦ resolve p.tys p.defs (lift decls p.body)
    (decls.map (holeAtom ·.name))) "does not resolve"
  let n := decls.length
  let (GT, es) ← genProgram (decls.zipIdx.map fun (d, i) ↦ varTy d (mvar i)) ps ts n
  match unify budget es with
  | .exhausted => .error "the budget of unification is spent"
  | .clash _ _ => .error "the program is ill-typed: two types it equates differ"
  | .solved θ =>
    let holes : List Hole := decls.zipIdx.map fun (d, i) ↦ ⟨d.name, d.context, substM θ (mvar i)⟩
    let cs := holes.map fun h ↦ closure h.context (dflt (ground tT h.target))
    .ok ⟨holes, (ps.map (·.name)).zip (GT.map (substM θ)), ts.map (completeTerm cs)⟩

/-- Accept a report whose completion the kernel's checker loads. -/
def validate (r : Report) : Except String Report :=
  if (load r.completion).isSome then .ok r
  else .error "the kernel rejects the completion of the holes"

/-- The check of a program with holes: its obligations, accepted when their completion loads. -/
def check (budget : ℕ) (text : List Char) : Except String Report :=
  obligations budget text >>= validate

/-- The completion of every accepted program loads. -/
theorem load_completion {budget : ℕ} {text : List Char} {r : Report}
    (h : check budget text = .ok r) : (load r.completion).isSome := by
  unfold check at h
  cases ho : obligations budget text with
  | error e => rw [ho] at h; cases h
  | ok r₀ =>
    rw [ho] at h
    change validate r₀ = .ok r at h
    unfold validate at h
    split at h
    · cases h; assumption
    · cases h

/-! ## Display -/

/-- The metavariables of a type, in the order of their first occurrences. -/
def metasOf (t : Meta ℕ) : List ℕ :=
  (RoseTree.elim (fun l (rs : List (List ℕ)) ↦
    match l with
    | .inl _ => rs.flatten
    | .inr x => [x]) t).foldl (fun xs x ↦ if xs.contains x then xs else xs ++ [x]) []

/-- A type with metavariables written as the reader writes types, a metavariable as
{lit}`(meta i)`, its position {lit}`i` in a list of the metavariables displayed. -/
def showType (ms : List ℕ) : Meta ℕ → SExp :=
  RoseTree.elim fun l rs ↦
    match l with
    | .inl a => printTypeStep a rs
    | .inr x => listS [atomS ['m', 'e', 't', 'a'], numeralS ((ms.idxOf? x).getD x)]

/-- An S-expression's text, laid out by the formatter within a line width of a hundred. -/
def textOf (e : SExp) : List Char :=
  let d : Document.Doc := ⟨[Document.plain e], []⟩
  Document.printAt (Document.defaultLayout .profile 100 d) d

/-- A hole's obligation displayed, given the metavariables displayed: the hole and its expected
type, then each binder of its context with its type, the outermost first. -/
def Hole.render (ms : List ℕ) (h : Hole) : List Char :=
  textOf (listS [listS [atomS ['h', 'o', 'l', 'e'], atomS h.name], showType ms h.target]) ++
    h.context.reverse.flatMap fun (x, A) ↦
      [' ', ' '] ++ textOf (listS [atomS x, printType A])

/-- A report displayed: each hole's obligation, its metavariables numbered in the order they
first occur, or that the program is complete. -/
def Report.render (r : Report) : List Char :=
  if r.complete then ['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', '\n']
  else
    let ms := (r.holes.flatMap fun h ↦ metasOf h.target).foldl
      (fun xs x ↦ if xs.contains x then xs else xs ++ [x]) []
    r.holes.flatMap (Hole.render ms)

end Geb.Kernel.Holes

end
