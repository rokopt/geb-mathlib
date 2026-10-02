/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Loading
public import Mathlib.Tactic.NormNum
public meta import Geb.Prototypes.Kernel.Image
public meta import Lean.Elab.Command

set_option doc.verso true in
/-!
# Declaring a program's loading, one definition at a time

A program's loading ({name}`Geb.Kernel.load`) is proved one definition at a time: each definition's
tree, the global it loads, the list of the globals after it and the step appending the global,
checked by the kernel's evaluation of the checker-evaluator {name}`Geb.Kernel.infer` on the
definition. {lit}`declareLoading` declares these for the definitions of a program not yet
declared, so that a long program's loading is declared over several modules, each continuing from
the globals the modules it imports declare, and a module whose definitions and imports do not
change is not checked again. The command {lit}`geb_load` declares them from a program's image.

Each global's type is the type the kernel computes ({name}`Geb.Kernel.defType`), rather than a
literal type tree: equating a computed type with a literal one makes the kernel evaluate the
checker-evaluator on every definition the one depends on. The trees, the globals and the lists of
globals are declared with their bodies exposed, since the steps of a later module unfold them.

## Main definitions

* {lit}`termExpr` — the expression of a definition's tree.
* {lit}`programName` — a program's name, from the current or the root namespace.
* {lit}`declareLoading` — the declarations of a program's loading beyond those already declared.

## Implementation notes

The commands' elaborators run in Lean's elaboration monads, whose definitions depend on
{lit}`Classical.choice`; they declare only kernel-checked definitions and reflexivity proofs,
which depend on no axiom.

## Tags

program, loading, kernel reduction, command
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.LoadCommand

open Lean Elab Command

/-- The expression of a list of expressions of a type. -/
meta def listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc ↦ mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- The expression of a tree, built by its constructor. -/
meta def treeExpr : Tree → Expr :=
  RoseTree.elim fun l cs ↦
    mkApp3 (mkConst ``RoseTree.node) (mkConst ``Nat) (mkRawNatLit l)
      (listExpr (mkConst ``Kernel.Tree) cs)

/-- The expression of a type, built by the kernel's constructors of types, as the checker
builds the types it computes, so that the two are equal by their constructors. -/
meta def typeExpr : Tree → Expr :=
  RoseTree.elim fun l cs ↦
    match l, cs with
    | Label.tyProd, [a, b] => mkApp2 (mkConst ``Kernel.tProd) a b
    | Label.tyArrow, [a, b] => mkApp2 (mkConst ``Kernel.tArrow) a b
    | Label.tyList, [a] => mkApp (mkConst ``Kernel.tList) a
    | _, [] => mkApp (mkConst ``Kernel.leaf) (mkRawNatLit l)
    | _, _ => mkApp3 (mkConst ``RoseTree.node) (mkConst ``Nat) (mkRawNatLit l)
        (listExpr (mkConst ``Kernel.Tree) cs)

/-- Whether the child of a term's node at a position is a type. -/
meta def typePosition (l i : ℕ) : Bool :=
  match l with
  | Label.lam | Label.fold | Label.iter | Label.nil => i == 0
  | Label.foldr | Label.lcase => i == 0 || i == 1
  | _ => false

/-- The expression of a term, its types built by {lit}`typeExpr` and its quoted trees by
{lit}`treeExpr`. -/
meta def termExpr : Tree → Expr :=
  RoseTree.para fun l cs ↦
    let kids := (List.range cs.length).zip cs |>.map fun (i, t, e) ↦
      if typePosition l i then typeExpr t else if l == Label.quote then treeExpr t else e
    mkApp3 (mkConst ``RoseTree.node) (mkConst ``Nat) (mkRawNatLit l)
      (listExpr (mkConst ``Kernel.Tree) kids)

/-- A program's name: an identifier beginning with {lit}`_root_` names it from the root
namespace, any other from the current namespace. -/
meta def programName (id : Name) : CommandElabM Name := do
  if id.getRoot == `_root_ then return id.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ id

/-- The name of a program's declaration: the program's name, then the declaration's kind followed
by an index. -/
meta def indexed (n : Name) (s : String) (k : ℕ) : Name := n ++ .mkSimple s!"{s}{k}"

/-- The declarations of the loading of the program {lit}`n`, whose definitions are {lit}`ds` with
their names and whose mirror is the namespace {lit}`m`, beyond those already declared: for each
definition, its tree {lit}`n.d`, its global {lit}`n.g` and the globals after it {lit}`n.pre`,
each followed by its index, and the step {lit}`n.step` appending its global, checked by the
kernel. A definition already declared must have the tree given. -/
meta def declareLoading (n m : Name) (ds : List (List Char × Tree)) : CoreM Unit := do
  let treeT := mkConst ``Kernel.Tree
  let globT := mkConst ``Kernel.Glob
  let listOf (t : Expr) : Expr := mkApp (mkConst ``List [0]) t
  let optOf (t : Expr) : Expr := mkApp (mkConst ``Option [0]) t
  let some' (t e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) t e
  let eqOf (t a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) t a b
  let nm := indexed n
  let defn (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl (forceExpose := true) <| .defnDecl
      { name := name, levelParams := [], type := tyE, value := valE,
        hints := .regular 0, safety := .safe }
    addDocStringCore name doc
  let thm (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl <| .thmDecl { name := name, levelParams := [], type := tyE, value := valE }
    addDocStringCore name doc
  unless (← getEnv).contains (nm "pre" 0) do
    defn (nm "pre" 0) "The globals before the program's first definition." (listOf globT)
      (mkApp (mkConst ``List.nil [0]) globT)
  for (k, (name, d)) in (List.range ds.length).zip ds do
    let dname := String.ofList name
    let tree := termExpr d
    if let some info := (← getEnv).find? (nm "d" k) then
      unless info.value? == some tree do
        throwError "the declared tree of the definition `{dname}` is not its tree"
      continue
    let pre := mkConst (nm "pre" k)
    defn (nm "d" k) s!"The tree of the program's definition `{dname}`." treeT tree
    defn (nm "g" k)
      s!"The global the program's definition `{dname}` loads: its type, and its mirror."
      globT (mkApp4 (mkConst ``Sigma.mk [0, 0]) treeT (mkConst ``Kernel.Ty.den)
      (mkApp2 (mkConst ``defType) pre (mkConst (nm "d" k)))
      (mkConst (m ++ .mkSimple dname)))
    let snoc := mkApp2 (mkConst ``snoc) pre (mkConst (nm "g" k))
    defn (nm "pre" (k + 1)) s!"The globals after the program's definition `{dname}`."
      (listOf globT) snoc
    let lhs := mkApp2 (mkConst ``loadStep) (some' (listOf globT) pre) (mkConst (nm "d" k))
    thm (nm "step" k) s!"The program's definition `{dname}` loads its global."
      (eqOf (optOf (listOf globT)) lhs (some' (listOf globT) snoc))
      (mkApp2 (mkConst ``Eq.refl [1]) (optOf (listOf globT)) lhs)

/-- The value of a hexadecimal digit. -/
meta def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

/-- The bytes a string of hexadecimal digits spells, two digits to a byte, the fold carrying the
bytes read and the high digit of the byte being read. -/
meta def hexBytes (s : String) : Option ByteArray :=
  (s.toList.foldl (fun (acc : Option (ByteArray × Option UInt8)) c ↦ do
      let (bs, hi) ← acc
      let d ← hexDigit c
      match hi with
      | none => some (bs, some d)
      | some h => some (bs.push (h * 16 + d), none))
    (some (ByteArray.empty, none))).bind fun (bs, hi) ↦ if hi.isNone then some bs else none

/-- {lit}`geb_load n mirror m image "…"` declares, by {lit}`declareLoading`, the loading of the
program {lit}`n` whose image the string spells in hexadecimal, its mirror the namespace
{lit}`m`, beyond the declarations of it already made. Its words {lit}`mirror` and {lit}`image` are
not reserved, so that a module importing the command may still use them as identifiers. -/
syntax (name := gebLoad) "geb_load " ident &" mirror " ident &" image " str : command

/-- The elaborator of {lit}`geb_load`. -/
@[command_elab gebLoad] meta def elabGebLoad : CommandElab := fun stx ↦ do
  let n ← programName stx[1].getId
  let m := stx[3].getId
  let some hex := stx[5].isStrLit? | throwError "the image is not a string"
  let some bytes := hexBytes hex | throwError "the image is not hexadecimal"
  let some b := readImage bytes | throwError "the image does not read"
  let some ds := unbundle b | throwError "the bundle does not unbundle"
  if (load (ds.map Prod.snd)).isNone then throwError "the program does not load"
  liftCoreM (declareLoading n m ds)

end Geb.Kernel.LoadCommand

end
