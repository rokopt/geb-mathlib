/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Image
public import Geb.Prototypes.Kernel.Modules
public import GebHost.Locate
public import GebBoot

set_option doc.verso true

/-!
# Located failures of the datatype language's typing, and the obligations of its holes

An untrusted explanation of a rejection by the compiled typing of the datatype language
({lit}`bootstrap/stage1/typing.geb`). The typing synthesizes the type of a term from the types of
its subterms and says of a definition only whether it has one. This pass follows the form the
expansion writes for the definition, node by node: each node's type is the one the compiled typing
gives it ({lit}`Typing.synAtom`, {lit}`Typing.synList`, {lit}`Typing.synCase`,
{lit}`Typing.synCata`), from its subterms' types in the contexts the compiled typing binds around
them, so that no typing decision is made here. Beside the type, the pass carries downwards the
type a form requires of a subterm, where the form determines it: a binding's declared type, a
function's domain, a conditional's other branch, a case analysis's result. A subterm whose type
differs from the one required is the failure reported, with the two types, as they are before the
erasure of datatypes; a node that has no type though its subterms have theirs is reported with
what its form requires.

A hole, {lit}`(hole name)` or {lit}`(hole name TYPE)`, has no type for the compiled typing, so a
definition holding one does not check. Here it has the type it declares or, without one, the type
required of it, and its obligation is reported: that type, and the variables bound around it with
their types. The terms around a hole are typed with it at that type, so that the other holes and
the failures of the definition are found as well.

The failure's vertex is a path in the form the expansion writes, which {lit}`occurrences` follows
in the source: the nested bindings and conditionals that module elaboration writes for
{lit}`let*` and {lit}`cond`, the abstractions over one binder for an abstraction over several,
the parts of a case analysis and of a structural recursion, and the abstraction and the binding of
the result that a {lit}`defn` is. Module elaboration writes a use of a declaration with type
parameters as the atom of its instance's name, so the arguments of an application of an instance
follow its type arguments in the source ({lit}`sourcePath`).

## Main definitions

* {lit}`failing` — the first form the typing rejects, with the environment it is checked in.
* {lit}`explain` — the failure and the holes of a rejected form.
* {lit}`occurrences` — the source spans of a vertex of a definition's expanded form.
* {lit}`sourcePath` — a path of an expanded form as a path of the form the source writes.

## Tags

datatype language, typing, diagnostics, typed holes, source span
-/

open Geb Geb.Kernel GebHost.Locate

public section

namespace GebHost.DatatypeTyping

/-- The typing's environment: the type abbreviations and the definitions, each a name with a
type, the names of the datatypes, of the sorts and of the numeral abbreviations, and the
markers. -/
abbrev Env : Type :=
  List Tree × (List Tree × (List Tree × (List Tree × (List Tree × List Tree))))

/-- A failed vertex of a form and what the typing requires there. -/
structure Fault where
  /-- The path from the form's root, in child indices. -/
  path : List Nat
  /-- What the typing requires at the vertex. -/
  message : String

/-- A hole's obligation. -/
structure Hole where
  /-- The hole's name. -/
  name : String
  /-- The path of the hole from the form's root. -/
  path : List Nat
  /-- The type required of the hole, where it is determined. -/
  type : Option String
  /-- The variables bound around the hole, innermost first, each with its type. -/
  context : List (String × String)

/-- What the pass finds of a term in a context: its type, where it has one; the first failure in
it; its holes; and whether it has no type only for want of a hole's. -/
structure Out where
  /-- The term's type. -/
  type : Option Tree
  /-- The first failure in the term. -/
  fault : Option Fault
  /-- The term's holes. -/
  holes : List Hole
  /-- Whether the term lacks a type only because a hole in it has none. -/
  unknown : Bool

/-- A term's findings as a function of the type required of it and of its context. -/
abbrev Syn : Type := Option Tree → Ctx → Out

/-- The value of an optional tree as the compiled typing represents it. -/
def some? (t : Tree) : Option Tree := if t.label = 1 then t.children.head? else none

/-- An optional tree as the compiled typing represents it. -/
def optional (o : Option Tree) : Tree :=
  match o with
  | some a => mk 1 [a]
  | none => leaf 0

/-- Whether two trees are equal, as the kernel's primitive decides it. -/
def same (a b : Tree) : Bool := (Const.equal a b).label != 0

/-- Whether two contexts are equal. -/
def sameContext (a b : Ctx) : Bool := same (mk 0 a) (mk 0 b)

/-- The unit type, the type of functions and the type of lists, as the typing represents them. -/
def tyUnit : Tree := leaf 1

@[inherit_doc tyUnit]
def tyArrow (a b : Tree) : Tree := mk 3 [a, b]

@[inherit_doc tyUnit]
def tyList (a : Tree) : Tree := mk 4 [a]

/-- The domain and the codomain of a type of functions. -/
def arrowParts (A : Tree) : Option (Tree × Tree) :=
  match A.label, A.children with
  | 3, [a, b] => some (a, b)
  | _, _ => none

/-- The components of a product type. -/
def prodParts (A : Tree) : Option (Tree × Tree) :=
  match A.label, A.children with
  | 2, [a, b] => some (a, b)
  | _, _ => none

/-- The element type of a type of lists. -/
def listElem (A : Tree) : Option Tree :=
  match A.label, A.children with
  | 4, [a] => some a
  | _, _ => none

/-- The successive domains of a type of functions. -/
def domains : Tree → List Tree :=
  RoseTree.para fun l rs ↦
    match l, rs with
    | 3, [(d, _), (_, r)] => d :: r
    | _, _ => []

/-- The codomain of a type of functions after a number of arguments. -/
def codomainAfter (A : Tree) (n : Nat) : Option Tree :=
  (List.range n).foldl (fun a _ ↦ a.bind fun t ↦ (arrowParts t).map (·.2)) (some A)

/-- A name's characters: a source binder's without the prefix module elaboration gives it; a
name of a template's instance at opaque arguments, which module elaboration writes under a
prefix holding the reserved {lit}`%generic`, as the template writes it; and the type
abbreviation of a parameter of an instance of a declaration with type parameters, which module
elaboration writes after the instance's name, as the declaration writes the parameter. -/
def nameText (n : Tree) : String :=
  let cs := n.children.map fun c ↦ Char.ofNat c.label
  match cs with
  | '%' :: '%' :: rest => String.ofList rest
  | _ =>
    match useOf? cs with
    | some (_, _, c :: suffix) => String.ofList (c :: suffix)
    | _ =>
      match (String.ofList cs).splitOn "%generic." with
      | [whole] => whole
      | parts => parts.getLast?.getD (String.ofList cs)

/-- The name of an opaque sort in its source spelling: that of a type abbreviation of it among
those given, as a parameter is at opaque arguments, or else its own. -/
def sortText (aliases : List Tree) (n : Tree) : String :=
  match aliases.find? fun a ↦ (a.children[1]?.map (same · (mk 6 [n]))).getD false with
  | some a => nameText (a.children.getD 0 n)
  | none => nameText n

/-- A datatype's name in its source spelling: that of an instance of a declaration with type
parameters as its use, an opaque sort among its arguments by the name of a type abbreviation of
it. -/
def dataText (aliases : List Tree) (n : Tree) : String :=
  match useOf? (n.children.map fun c ↦ Char.ofNat c.label) with
  | some (f, args, []) =>
    let arg : SExp → String := RoseTree.elim fun a rs ↦
      match a with
      | some ('%' :: s) => sortText aliases (mk 0 (('%' :: s).map fun c ↦ leaf c.toNat))
      | some s => String.ofList s
      | none => "(" ++ " ".intercalate rs ++ ")"
    "(" ++ " ".intercalate (nameText (mk 0 (f.map fun c ↦ leaf c.toNat)) :: args.map arg) ++ ")"
  | _ => nameText n

/-- A type in its source spelling, a datatype by its name and an opaque sort by the name of a
type abbreviation of it among those given, as a template's parameter is at the template's opaque
arguments, or else by its own. -/
def typeText (aliases : List Tree) : Tree → String :=
  RoseTree.para fun l rs ↦
    match l, rs with
    | 0, [] => "T"
    | 1, [] => "Unit"
    | 2, [(_, a), (_, b)] => s!"(Prod {a} {b})"
    | 3, [(_, a), (_, b)] => s!"(Arrow {a} {b})"
    | 4, [(_, a)] => s!"(List {a})"
    | 5, [(n, _)] => dataText aliases n
    | 6, [(n, _)] => sortText aliases n
    | _, _ => "an unreadable type"

/-- The form of a type, which the typing reads back as the type. -/
def typeForm : Tree → Tree :=
  RoseTree.para fun l rs ↦
    let atom (s : String) : Tree := mk 1 (s.toList.map fun c ↦ leaf c.toNat)
    match l, rs with
    | 0, [] => atom "T"
    | 1, [] => atom "Unit"
    | 2, [(_, a), (_, b)] => mk 2 [atom "Prod", a, b]
    | 3, [(_, a), (_, b)] => mk 2 [atom "Arrow", a, b]
    | 4, [(_, a)] => mk 2 [atom "List", a]
    | 5, [(n, _)] => mk 1 n.children
    | 6, [(n, _)] => mk 1 n.children
    | _, _ => leaf 0

/-- The characters of an atom of a form. -/
def atomText (t : Tree) : Option String :=
  if t.label = 1 then some (String.ofList (t.children.map fun c ↦ Char.ofNat c.label)) else none

/-- The name of an atom of a form, as the typing binds it. -/
def atomName (t : Tree) : Tree := mk 0 t.children

/-- A name with a type, as the typing's contexts hold them. -/
def abbr (n A : Tree) : Tree := mk 0 [n, A]

/-- The variables of a context a source binds, each with its type, the innermost of a name
alone: the names the erasure binds, which begin with one percent sign, are left out. -/
def contextText (aliases : List Tree) (cx : Ctx) : List (String × String) :=
  (cx.filterMap fun a ↦
    match a.children with
    | [n, A] =>
      match n.children.map fun c ↦ Char.ofNat c.label with
      | '%' :: '%' :: _ => some (nameText n, typeText aliases A)
      | '%' :: _ => none
      | _ => some (nameText n, typeText aliases A)
    | _ => none).foldl (fun acc p ↦ if acc.any (·.1 == p.1) then acc else acc ++ [p]) []

/-- A subterm to visit: its position among a node's children, the type required of it and its
context. -/
structure Visit where
  /-- The position of the subterm. -/
  index : Nat
  /-- The type required of the subterm. -/
  expected : Option Tree
  /-- The context of the subterm. -/
  context : Ctx

/-- The findings of a node's child. -/
def childOut (kids : List (Tree × Syn)) (i : Nat) (e : Option Tree) (cx : Ctx) : Out :=
  match kids[i]? with
  | some (_, s) => s e cx
  | none => ⟨none, none, [], false⟩

/-- A subterm visited: the visit and the subterm's findings, which are computed once. -/
abbrev Visited : Type := Visit × Out

/-- Visit a subterm. -/
def visit (kids : List (Tree × Syn)) (v : Visit) : Visited :=
  (v, childOut kids v.index v.expected v.context)

/-- A node's children with their types as functions of the context, as the compiled typing takes
them: the type found of a child visited, where the context is the one it was visited in, and else
the child's type in the context given. -/
def results (kids : List (Tree × Syn)) (seen : List Visited) : List (Tree × (List Tree → Tree)) :=
  kids.mapIdx fun i (t, s) ↦
    (t, fun cx ↦
      match seen.find? (·.1.index == i) with
      | some (v, o) =>
        if sameContext cx v.context then optional o.type else optional (s v.expected cx).type
      | none => optional (s none cx).type)

/-- A node's findings: the first failure among the subterms visited and their holes; else, where
the node has no type, the failure the node's form gives, unless a hole's missing type accounts for
it; and else, where the node's type is not the one required, that difference. -/
def finish (aliases : List Tree) (seen : List Visited) (expected ty : Option Tree)
    (why : Unit → Fault) : Out :=
  let (f, hs, u) := seen.foldl (init := ((none : Option Fault), ([] : List Hole), false))
    fun (f, hs, u) (p, o) ↦
      (f <|> o.fault.map fun x ↦ { x with path := p.index :: x.path },
        hs ++ o.holes.map fun h ↦ { h with path := p.index :: h.path }, u || o.unknown)
  match f, ty, expected with
  | some _, _, _ => ⟨ty, f, hs, u⟩
  | none, none, _ => if u then ⟨none, none, hs, true⟩ else ⟨none, some (why ()), hs, false⟩
  | none, some B, some A =>
    if same A B then ⟨ty, none, hs, false⟩
    else ⟨ty, some ⟨[], s!"expected {typeText aliases A}, got {typeText aliases B}"⟩, hs, false⟩
  | none, some _, none => ⟨ty, none, hs, false⟩

/-- The visits of arguments from a position, each required to have the next domain of a type of
functions. -/
def arguments (fty : Option Tree) (first count : Nat) (cx : Ctx) : List Visit :=
  let ds := (fty.map domains).getD []
  (List.range count).map fun j ↦ ⟨first + j, ds[j]?, cx⟩

/-- The context a clause's body is typed in, read from the compiled typing: the clause is typed
with a body whose type is a datatype named by the context it is given. -/
def clauseContext (specs : List Tree) (parts : Tree)
    (fields : Tree → Tree → (List Tree → Tree) → List Tree → Tree) (inner : Ctx) : Option Ctx :=
  let r := GebBoot.«Typing.clauseTy» specs parts fields
    (leaf 0, fun cx ↦ mk 1 [mk 5 [mk 0 cx]]) inner
  match some? r with
  | some t => if t.label = 5 then t.children.head?.map (·.children) else none
  | none => none

/-- The findings of a case analysis or a structural recursion, given the positions of its
scrutinee, of its clauses' parts and of its first body, the type required of each body, the
context the erasure binds around the clauses, and the compiled typing of a clause's fields and of
the node. -/
def clausesOut (aliases : List Tree) (kids : List (Tree × Syn)) (scrutinee parts first : Nat)
    (data : Option Tree)
    (specs : List Tree) (fields : Tree → Tree → (List Tree → Tree) → List Tree → Tree)
    (inner cx : Ctx) (bodyType expected : Option Tree)
    (node : List (Tree × (List Tree → Tree)) → Tree) : Out :=
  let metas := ((kids[parts]?.map (·.1.children)).getD [])
  let contexts : List (Option Ctx) :=
    (metas.map fun m ↦ clauseContext specs m fields inner) ++
      (List.replicate (kids.length - first - metas.length) (some inner))
  match contexts.findIdx? (·.isNone) with
  | some j =>
    ⟨none, some ⟨[parts, j], "the clause's constructor is not one of the datatype's, or its \
      variables are not those of the constructor's fields"⟩, [], false⟩
  | none =>
    let bodies : List Visited := (contexts.filterMap id).foldl (init := []) fun acc c ↦
      let required := bodyType <|> (acc.head?.bind (·.2.type))
      acc ++ [visit kids ⟨first + acc.length, required, c⟩]
    let seen := visit kids ⟨scrutinee, data, cx⟩ :: bodies
    finish aliases seen expected (some? (node (results kids seen))) fun _ ↦
      ⟨[], "the clauses do not cover the datatype's constructors, or the datatype is not \
        declared before"⟩

/-- A list's findings, by its head: a hole; the kernel's forms and those of the datatype
language, each visiting its subterms at the types it requires of them; and an application, its
arguments at the domains of the function's type. -/
def listOut (E : Env) (kids : List (Tree × Syn)) (expected : Option Tree) (cx : Ctx) : Out :=
  let fs := kids.map (·.1)
  let k := fs.length
  let f (i : Nat) : Tree := fs.getD i (leaf 0)
  let text := typeText E.1
  let see (v : Visit) : Visited := visit kids v
  let found (v : Visited) : String := (v.2.type.map text).getD "none"
  let done (seen : List Visited) (why : Unit → Fault) : Out :=
    finish E.1 seen expected (some? (GebBoot.«Typing.synList» E fs (results kids seen) cx)) why
  let malformed : Unit → Fault := fun _ ↦ ⟨[], "the form is not well formed"⟩
  let readTy (i : Nat) : Option Tree := some? (GebBoot.«Typing.readTy» E (f i))
  let undeclared (i : Nat) : Unit → Fault := fun _ ↦ ⟨[i], "the type is not declared before"⟩
  let constant (fty : Option Tree) (first : Nat) : Out :=
    done ((arguments fty first (k - first) cx).map see) fun _ ↦
      match fty with
      | none => ⟨[1], "the type is not declared before"⟩
      | some F => ⟨[], s!"the constant of type {text F} is given too many arguments"⟩
  match atomText (f 0), k with
  | some "hole", 2 =>
    ⟨expected, none,
      [⟨(atomText (f 1)).getD "", [], expected.map text, contextText E.1 cx⟩], expected.isNone⟩
  | some "hole", 3 =>
    match readTy 2, expected with
    | none, _ => ⟨none, some (undeclared 2 ()), [], false⟩
    | some A, some B =>
      if same A B then ⟨some A, none, [⟨(atomText (f 1)).getD "", [], some (text A),
        contextText E.1 cx⟩], false⟩
      else ⟨some A, some ⟨[], s!"expected {text B}, got {text A}"⟩, [], false⟩
    | some A, none =>
      ⟨some A, none, [⟨(atomText (f 1)).getD "", [], some (text A), contextText E.1 cx⟩], false⟩
  | some "lam", 3 =>
    let ps := GebBoot.«Typing.bindersOf» E (f 1)
    if ps.1.label = 0 ∨ ps.2.isEmpty then
      ⟨none, some ⟨[1], "a binder is not a name with a type declared before, or its name may \
        not name a variable"⟩, [], false⟩
    else
      done [see ⟨2, expected.bind (codomainAfter · ps.2.length), ps.2.reverse ++ cx⟩] malformed
  | some "let", 5 =>
    match readTy 2 with
    | none => ⟨none, some (undeclared 2 ()), [], false⟩
    | some A =>
      done [see ⟨3, some A, cx⟩, see ⟨4, expected, abbr (atomName (f 1)) A :: cx⟩] fun _ ↦
        ⟨[1], "the name may not name a variable"⟩
  | some "if", 4 =>
    let first := see ⟨2, expected, cx⟩
    done [see ⟨1, some tT, cx⟩, first, see ⟨3, expected <|> first.2.type, cx⟩] malformed
  | some "pair", 3 =>
    let parts := expected.bind prodParts
    done [see ⟨1, parts.map (·.1), cx⟩, see ⟨2, parts.map (·.2), cx⟩] malformed
  | some "fst", 2 | some "snd", 2 =>
    let p := see ⟨1, none, cx⟩
    done [p] fun _ ↦ ⟨[1], s!"expected a product type, got {found p}"⟩
  | some "cons", 3 =>
    let x := expected.bind listElem
    let head := see ⟨1, x, cx⟩
    let tail := see ⟨2, (expected.filter fun A ↦ (listElem A).isSome) <|> head.2.type.map tyList,
      cx⟩
    done [head, tail] fun _ ↦ ⟨[2], s!"expected a list type, got {found tail}"⟩
  | some "nil", 2 => done [] (undeclared 1)
  | some "quote", 2 => done [] malformed
  | some "datum", 3 =>
    done [] fun _ ↦ ⟨[2], "the datum is not a member of the datatype, or the datatype is not \
      declared before and named by its own name"⟩
  | some "rep", 2 =>
    let v := see ⟨1, none, cx⟩
    done [v] fun _ ↦ ⟨[1], s!"expected a datatype, got {found v}"⟩
  | some "decode", 5 =>
    let inner := abbr (nameTree "%e".toList) tT :: cx
    let default := see ⟨4, expected, inner⟩
    let g := match readTy 1, expected <|> default.2.type with
      | some D, some c => some (tyArrow D c)
      | _, _ => none
    done [see ⟨2, some tT, cx⟩, default, see ⟨3, g, inner⟩] fun _ ↦
      ⟨[1], "the datatype is not declared before, or is not named by its own name"⟩
  | some "fold", _ | some "para", _ => constant ((readTy 1).map GebBoot.«Typing.foldTyOf») 2
  | some "iter", _ => constant ((readTy 1).map GebBoot.«Typing.iterTyOf») 2
  | some "foldr", _ =>
    constant ((readTy 1).bind fun A ↦ (readTy 2).map (GebBoot.«Typing.foldrTyOf» A)) 3
  | some "lcase", _ =>
    constant ((readTy 1).bind fun A ↦ (readTy 2).map (GebBoot.«Typing.lcaseTyOf» A)) 3
  | _, 0 => ⟨none, some (malformed ()), [], false⟩
  | _, _ =>
    if (GebBoot.«Typing.keywordTx» (f 0)).label ≠ 0 then ⟨none, some (malformed ()), [], false⟩
    else
      let head := see ⟨0, none, cx⟩
      done (head :: (arguments head.2.type 1 (k - 1) cx).map see) fun _ ↦
        ⟨[0], s!"expected a function of {k - 1} argument(s), got {found head}"⟩

/-- One node's findings, from its children's: an atom; a list; a coercion the expansion writes;
a case analysis; and a structural recursion. -/
def step (E : Env) (l : Nat) (kids : List (Tree × Syn)) : Syn := fun expected cx ↦
  let node := mk l (kids.map (·.1))
  let fs := kids.map (·.1)
  let f (i : Nat) : Tree := fs.getD i (leaf 0)
  let ms := GebBoot.«Typing.envMs» E
  match l with
  | 1 =>
    finish E.1 [] expected (some? (GebBoot.«Typing.synAtom» E node.children cx)) fun _ ↦
      if atomText node == some "hole" then
        ⟨[], "the qualified name is not visible: its module is not declared before, or does \
          not export it"⟩
      else ⟨[], s!"{nameText (atomName node)} is not declared before, or names no term"⟩
  | 2 => listOut E kids expected cx
  | 11 | 12 =>
    finish E.1 [visit kids ⟨1, none, cx⟩] expected (some? (GebBoot.«Typing.synIn» E cx node))
      fun _ ↦
      ⟨[], "the expansion's coercion does not check"⟩
  | 13 =>
    let mc := GebBoot.«Typing.markerCtors» ms (f 0)
    clausesOut E.1 kids 1 2 3 (some? (GebBoot.«Typing.readTy» E (f 0))) mc.2
      (fun c m b cx ↦ GebBoot.«Typing.caseFields» E c m b cx)
      (abbr (nameTree "%s".toList) tT :: cx) cx expected expected
      fun rs ↦ GebBoot.«Typing.synCase» E fs rs cx
  | 14 =>
    let mc := GebBoot.«Typing.markerCtors» ms (f 0)
    match some? (GebBoot.«Typing.readTy» E (f 1)) with
    | none => ⟨none, some ⟨[1], "the type is not declared before"⟩, [], false⟩
    | some R =>
      clausesOut E.1 kids 2 4 5 (some? (GebBoot.«Typing.readTy» E (f 0))) mc.2
        (fun c m b cx ↦ GebBoot.«Typing.cataFields» E (f 0) R c m b cx)
        (abbr (nameTree "%u".toList) tyUnit ::
          abbr (nameTree "%k".toList) (tyList (tyArrow tyUnit R)) ::
          abbr (nameTree "%o".toList) tT :: cx) cx (some R) expected
        fun rs ↦ GebBoot.«Typing.synCata» E fs rs cx
  | _ => ⟨none, some ⟨[], "the form is not a term"⟩, [], false⟩

/-- The findings of a term in an environment and a context. -/
def explainTerm (E : Env) (cx : Ctx) (t : Tree) : Out :=
  RoseTree.para (step E) t none cx

/-- The failure and the holes of a form the typing rejects, the paths from the form's root: of a
definition, those of its term; of a constant and of a type abbreviation, the type that is not
declared. -/
def explain (E : Env) (form : Tree) : Out :=
  let f (i : Nat) : Tree := form.children.getD i (leaf 0)
  match form.label, atomText (f 0), form.children.length with
  | 2, some "def", 3 =>
    let o := explainTerm E [] (f 2)
    { o with
      fault := o.fault.map fun x ↦ { x with path := 2 :: x.path }
      holes := o.holes.map fun h ↦ { h with path := 2 :: h.path } }
  | 2, some "deftype", 3 | 2, some "%postulate", 3 =>
    ⟨none, some ⟨[2], "the type is not declared before"⟩, [], false⟩
  | 2, some "defnum", 3 =>
    ⟨none, some ⟨[1], "a numeral abbreviation is not named by a numeral"⟩, [], false⟩
  | _, _, _ => ⟨none, none, [], false⟩

/-- The state of the check of a program's forms over supports, as
{lit}`bootstrap/stage1/expansion.geb` declares it. -/
abbrev State : Type := Tree × ((Tree × Tree) × List Tree)

/-- A rejected form: the environment it is checked in, the form, and the pass's findings. -/
abbrev Rejected : Type := Env × Tree × Out

/-- The forms of a list that a check rejects, each with the pass's findings, from a state of the
check: the check goes on past a definition in which the pass finds holes and no failure and whose
type the holes' types determine, with the definition declared a constant of that type, and stops
after any other rejected form. The check is given by its step, whether a state is rejected, and
the environment a form is checked in. -/
def rejectedFrom {σ : Type} (next : σ → Tree → σ) (failed : σ → Bool) (env : σ → Tree → Env)
    (forms : List Tree) (init : σ) : σ × List Rejected × Bool :=
  forms.foldl (init := (init, ([] : List Rejected), false)) fun (s, acc, stop) f ↦
    if stop then (s, acc, stop)
    else if !failed (next s f) then (next s f, acc, false)
    else
      let E := env s f
      let o := explain E f
      match o.fault, o.type, o.holes.isEmpty, f.children with
      | none, some A, false, [_, n, _] =>
        let s' := next s (mk 2 [mk 1 ("%postulate".toList.map fun c ↦ leaf c.toNat), n, typeForm A])
        if failed s' then (s, acc ++ [(E, f, o)], true) else (s', acc ++ [(E, f, o)], false)
      | _, _, _, _ => (s, acc ++ [(E, f, o)], true)

/-- The forms of a program, as module elaboration writes them, that the typing rejects, each
with the environment it is checked in, that of the declarations of its support and every marker,
and the pass's findings: the first rejected form and, while the forms rejected hold only holes
whose types determine the definitions' types, those after them. Within a template's instance at
opaque arguments, the forms are the instance's, with the instance's declarations before them. -/
def failing (es : List Tree) : List Rejected :=
  if (GebBoot.«Typing.Tx.member» (mk 2 es)).label = 0 then []
  else
    let r := GebBoot.«Datatype.expandTyped» es
    if r.1.label = 0 then []
    else
      let env (s : State) (f : Tree) : Env :=
        let l := GebBoot.«Expansion.listsOf» (GebBoot.«Expansion.supportOf» s.2.1 f)
        (l.1, l.2.1, l.2.2.1, l.2.2.2.1, l.2.2.2.2, s.2.2)
      ((GebBoot.«Datatype.markersFirst» r.2).foldl
        (init := ((GebBoot.«Expansion.start» : State), ([] : List Rejected), false))
        fun (s, acc, stop) f ↦
          if stop then (s, acc, stop)
          else if f.label = 15 then
            if (GebBoot.«Expansion.checkStep» s f).1.label ≠ 1 then (s, acc, false)
            else
              let inner := rejectedFrom GebBoot.«Typing.checkStep» (·.2.label = 1) (fun t _ ↦ t.1)
                f.children (env s f, leaf 0)
              (s, acc ++ inner.2.1, inner.2.2)
          else
            let one := rejectedFrom GebBoot.«Expansion.checkStep» (·.1.label = 1) env [f] s
            (one.1, acc ++ one.2.1, one.2.2)).2.1

/-! ## The source of a vertex of an expanded form -/

/-- Where a vertex of a definition's expanded form is in the source: at a source expression;
at one of the nested forms written for a source form, the binding of a position of a sequence of
bindings, the conditional of a clause of guarded clauses, the abstraction over one binder of an
abstraction or of a definition by {lit}`defn`, and that binder's list; at the binding of a
definition's result; and at the parts of the clauses of a case analysis or a structural
recursion. -/
inductive Place where
  /-- A source expression. -/
  | plain (t : Located)
  /-- The binding of a position of a {lit}`let*`. -/
  | binding (t : Located) (j : Nat)
  /-- The conditional of a clause of a {lit}`cond`. -/
  | clause (t : Located) (j : Nat)
  /-- The abstraction over the binder of a position, of binders at a child of a form. -/
  | abstraction (t : Located) (at_ j : Nat)
  /-- The list of the one binder of an abstraction. -/
  | binder (b : Located)
  /-- The binding of the result of a {lit}`defn`. -/
  | result (t : Located)
  /-- The parts of the clauses of a form, the first clause at a child of the form. -/
  | parts (t : Located) (first : Nat)

/-- The binders of an abstraction: one binder, or a list of them. -/
def binderList (b : Located) : List Located :=
  match b.children with
  | [x, _] => if x.label.2.isSome then [b] else b.children
  | cs => cs

/-- The child of a located S-expression at a position. -/
def at? (t : Located) (i : Nat) : Option Located := t.children[i]?

/-- The place of the body after the abstraction over a binder: the next abstraction, or the body
of an abstraction and the binding of the result of a definition. -/
def afterBinder (t : Located) (at_ j : Nat) : Option Place :=
  let n := ((at? t at_).map binderList).getD [] |>.length
  if j + 1 < n then some (.abstraction t at_ (j + 1))
  else if at_ = 1 then (at? t 2).map .plain
  else some (.result t)

/-- The place of the form written at a source expression: the first binding of a sequence of
bindings, the first conditional of guarded clauses, the first abstraction of an abstraction, and
else the expression itself. A sequence of no bindings and guarded clauses of the default alone,
for which the body and the default are written, have no place below them. -/
def enter (t : Located) : Place :=
  if headIs "let*".toList t ∧ ((at? t 1).map (·.children.length)).getD 0 > 0 then .binding t 0
  else if headIs "cond".toList t ∧ t.children.length > 2 then .clause t 0
  else if headIs "lam".toList t ∧ t.children.length = 3 then .abstraction t 1 0
  else .plain t

/-- The place of a child of the form written at a place: at an expression, the scrutinee, the
parts and the bodies of a case analysis and of a structural recursion, and else the expression's
child. -/
def Place.child (p : Place) (i : Nat) : Option Place :=
  match p with
  | .plain t =>
    if headIs "let*".toList t ∨ headIs "cond".toList t then none
    else if headIs "case".toList t then
      match i with
      | 1 => (at? t 1).map .plain
      | 2 => some (.parts t 2)
      | _ => ((at? t (i - 1)).bind (at? · 1)).map .plain
    else if headIs "cata".toList t then
      match i with
      | 0 => (at? t 1).map .plain
      | 1 => (at? t 2).map .plain
      | 2 => (at? t 3).map .plain
      | 3 => none
      | 4 => some (.parts t 4)
      | _ => ((at? t (i - 1)).bind (at? · 1)).map .plain
    else (at? t i).map .plain
  | .binding t j =>
    let b := (at? t 1).bind (at? · j)
    match i with
    | 4 =>
      if j + 1 < ((at? t 1).map (·.children.length)).getD 0 then some (.binding t (j + 1))
      else (at? t 2).map .plain
    | 0 => none
    | _ => (b.bind (at? · (i - 1))).map .plain
  | .clause t j =>
    let c := at? t (j + 1)
    match i with
    | 1 => (c.bind (at? · 0)).map .plain
    | 2 => (c.bind (at? · 1)).map .plain
    | 3 =>
      if j + 3 = t.children.length then ((at? t (j + 2)).bind (at? · 1)).map .plain
      else some (.clause t (j + 1))
    | _ => none
  | .abstraction t at_ j =>
    match i with
    | 1 => (((at? t at_).map binderList).bind (·[j]?)).map .binder
    | 2 => afterBinder t at_ j
    | _ => none
  | .binder b => if i = 0 then some (.plain b) else none
  | .result t =>
    match i with
    | 2 => (at? t 3).map .plain
    | 3 => (at? t 4).map .plain
    | _ => none
  | .parts t first => ((at? t (first + i)).bind (at? · 0)).map .plain

/-- The span of the source at a place. -/
def Place.span (p : Place) : Span :=
  match p with
  | .plain t => t.label.1
  | .binding t j => (((at? t 1).bind (at? · j)).getD t).label.1
  | .clause t j => ((at? t (j + 1)).getD t).label.1
  | .abstraction t _ _ => t.label.1
  | .binder b => b.label.1
  | .result t => ((at? t 4).getD t).label.1
  | .parts t _ => t.label.1

/-- The place of the term of a declaration's expanded form: of a definition, its body; of a
definition by {lit}`defn`, the abstraction over its first binder, or the binding of its result. -/
def termPlace (t : Located) : Option Place :=
  if headIs "def".toList t then (at? t 2).map enter
  else if headIs "defn".toList t ∧ t.children.length = 5 then
    if ((at? t 2).map binderList).getD [] |>.isEmpty then some (.result t)
    else some (.abstraction t 2 0)
  else none

/-- The place of a path from the root of a declaration's expanded form, whose term is its third
child; the places of the form written at a source expression are entered at each step. -/
def placeOf (t : Located) (path : List Nat) : Option Place :=
  match path with
  | 2 :: rest =>
    rest.foldl (init := termPlace t) fun p i ↦
      (p.bind (·.child i)).map fun q ↦
        match q with
        | .plain s => enter s
        | q => q
  | _ => none

/-- A path in a form the expansion writes, as a path in the form with each use of a declaration
with type parameters as the source writes it: where a list's first element is the atom of an
instance's name, the list's other elements follow the instance's type arguments in the source. -/
def sourcePath (form : Tree) (path : List Nat) : List Nat :=
  (path.foldl (init := (some form, ([] : List Nat))) fun (u?, acc) i ↦
    match u? with
    | none => (none, acc ++ [i])
    | some u =>
      let types := if u.label = 2 then
          ((u.children.head?.bind atomText).bind fun h ↦
            (useOf? h.toList).map (·.2.1.length)).getD 0
        else 0
      (u.children[i]?, acc ++ [if i = 0 then 0 else i + types])).2

/-- The name a declaration's form declares: the atom after its keyword, or the atom that begins
the list there where the declaration takes type parameters. -/
def declaredAtom (t : Located) : List Char :=
  ((t.children[1]?.bind declNameAtom).bind (·.label.2)).getD []

/-- The source spans of a vertex of a declaration's expanded form, the declaration found by its
name in the flat program, within its modules. -/
def occurrences (items : List Located) (name : String) (path : List Nat) : List Span :=
  let visit : Located → List (List Char) → List Span :=
    RoseTree.para fun l cs pre ↦
      let t := RoseTree.node l (cs.map Prod.fst)
      let n := declaredAtom t
      let here := pre ++ [n]
      if headIs "module".toList t then (cs.drop 2).flatMap fun (_, r) ↦ r here
      else if headIs "data".toList t then
        (t.children.drop 2).filterMap fun c ↦
          match c.children.head?.bind (·.label.2) with
          | some k => if qualified (pre ++ [k]) == name then some c.label.1 else none
          | none => none
      else if qualified here != name then []
      else ((placeOf t path).map (·.span)).toList
  items.flatMap fun t ↦ visit t []

/-- Whether the source at a vertex of a declaration's expanded form is a hole, where the vertex
has a source: module elaboration also writes the form of a hole for a qualified name that is not
visible, so that an application of such a name reads as a hole after it. -/
def holeAt (items : List Located) (name : String) (path : List Nat) : Option Bool :=
  let visit : Located → List (List Char) → List Bool :=
    RoseTree.para fun l cs pre ↦
      let t := RoseTree.node l (cs.map Prod.fst)
      let n := declaredAtom t
      let here := pre ++ [n]
      if headIs "module".toList t then (cs.drop 2).flatMap fun (_, r) ↦ r here
      else if qualified here != name then []
      else
        match placeOf t path with
        | some (.plain s) => [headIs "hole".toList s]
        | _ => []
  (items.flatMap fun t ↦ visit t []).head?

end GebHost.DatatypeTyping

end
