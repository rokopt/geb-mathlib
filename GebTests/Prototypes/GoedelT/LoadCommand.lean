/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.Load
public import Geb.Prototypes.Kernel.Reader
public import Mathlib.Tactic.NormNum
public meta import GebTests.Prototypes.Proofs -- shake: keep
public meta import Lean.Elab.Command

set_option doc.verso true in
/-!
# Commands embedding a Geb program in Lean

The command {lit}`geb_program` reads a Geb program's sources at elaboration, runs the stage-0
compiler's front end on them, and declares, for each of the program's definitions, its tree, its
global and the globals before it, each global's value the definition of the same name that the
bootstrap compiler's Lean backend emits from the program; it then declares the loading of the
program, one definition at a time, each step closed by reflexivity, which the kernel checks by
evaluating the checker-evaluator {name}`Geb.Kernel.infer` on the definition. The command
{lit}`kernel_rfl` declares a theorem proved by reflexivity, checked by the kernel alone.

Each global's type is the type the kernel computes,
{name}`GebTests.Prototypes.GoedelT.Load.defType`, rather than a literal type tree: equating a
computed type with a literal one makes the kernel evaluate the checker-evaluator on every
definition the one depends on.

## Implementation notes

The commands' elaborators run in Lean's elaboration monads, whose definitions depend on
{lit}`Classical.choice`; the module holds only the commands, so that the loading's lemmas and
its uses are held to the strict axiom set elsewhere.

## Tags

program, loading, kernel reduction, command
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.LoadCommand

open Geb Geb.Kernel Lean Elab Command GebTests.Prototypes.GoedelT.Load

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

/-- {lit}`geb_program n from "f" ... mirror m` embeds the program the files make, each followed
by a newline, as the host driver joins sources, read and expanded by the stage-0 compiler's front
end: {lit}`n` is the list of its definitions' trees, {lit}`n.d` followed by each index; {lit}`n.g`
followed by an index is the global its definition loads, at its type and the definition of that
name in the namespace {lit}`m`, the Lean the bootstrap compiler emits from the program;
{lit}`n.pre` followed by an index is the list of the globals before it; {lit}`n.step` followed by
an index states that the definition loads its global after them, checked by the kernel;
{lit}`n.load_eq` states that the program loads to its globals, composed from the steps; and
{lit}`n.last_heq` states that the last global's value is the last definition's mirror, the type the
kernel computes for the definition denoting the type the mirror declares, checked by the
kernel. -/
syntax (name := gebProgram) "geb_program " ident " from " str* " mirror " ident : command

/-- The elaborator of {lit}`geb_program`. -/
@[command_elab gebProgram] meta def elabGebProgram : CommandElab := fun stx ↦ do
  let n := (← getCurrNamespace) ++ stx[1].getId
  let paths := stx[3].getArgs.filterMap (·.isStrLit?)
  let m := stx[5].getId
  let mut text := ""
  for p in paths do
    text := text ++ (← IO.FS.readFile p) ++ "\n"
  let r ← match runMain GoedelT.ProofTests.bundler.toList (nameTree text.toList) with
    | some r => pure r
    | none => throwError "the front end does not run"
  let some b := (if r.label == 1 then r.children.head? else none)
    | throwError "the program does not read"
  let some ds := unbundle b | throwError "the bundle does not unbundle"
  let some G := load (ds.map Prod.snd) | throwError "the program does not load"
  let treeT := mkConst ``Kernel.Tree
  let globT := mkConst ``Kernel.Glob
  let listOf (t : Expr) : Expr := mkApp (mkConst ``List [0]) t
  let optOf (t : Expr) : Expr := mkApp (mkConst ``Option [0]) t
  let some' (t e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) t e
  let eqOf (t a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) t a b
  let nm (s : String) (k : ℕ) : Name := n ++ .mkSimple s!"{s}{k}"
  let defn (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl <| .defnDecl
      { name := name, levelParams := [], type := tyE, value := valE,
        hints := .regular 0, safety := .safe }
    addDocStringCore name doc
  let thm (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl <| .thmDecl { name := name, levelParams := [], type := tyE, value := valE }
    addDocStringCore name doc
  let count := ds.length
  liftCoreM do
    defn (nm "pre" 0) "The globals before the program's first definition." (listOf globT)
      (mkApp (mkConst ``List.nil [0]) globT)
    for (k, (name, d)) in (List.range count).zip ds do
      let pre := mkConst (nm "pre" k)
      let dname := String.ofList name
      defn (nm "d" k) s!"The tree of the program's definition `{dname}`." treeT (termExpr d)
      defn (nm "g" k)
        s!"The global the program's definition `{dname}` loads: its type, and its mirror."
        globT (mkApp4 (mkConst ``Sigma.mk [0, 0]) treeT (mkConst ``Kernel.Ty.den)
        (mkApp2 (mkConst ``defType) pre (mkConst (nm "d" k)))
        (mkConst (m ++ .mkSimple (String.ofList name))))
      let snoc := mkApp2 (mkConst ``snoc) pre (mkConst (nm "g" k))
      defn (nm "pre" (k + 1)) s!"The globals after the program's definition `{dname}`."
        (listOf globT) snoc
      let lhs := mkApp2 (mkConst ``loadStep) (some' (listOf globT) pre) (mkConst (nm "d" k))
      thm (nm "step" k) s!"The program's definition `{dname}` loads its global."
        (eqOf (optOf (listOf globT)) lhs (some' (listOf globT) snoc))
        (mkApp2 (mkConst ``Eq.refl [1]) (optOf (listOf globT)) lhs)
    defn n "The trees of the program's definitions." (listOf treeT)
      (listExpr treeT ((List.range count).map fun k ↦ mkConst (nm "d" k)))
    let final := mkConst (nm "pre" count)
    let base := mkApp2 (mkConst ``Eq.refl [1]) (optOf (listOf globT)) (some' (listOf globT) final)
    let chain := (List.range count).foldr (fun k acc ↦
        let rest := listExpr treeT (((List.range count).drop (k + 1)).map fun j ↦
          mkConst (nm "d" j))
        mkAppN (mkConst ``foldl_loadStep_cons)
          #[rest, mkConst (nm "d" k), mkConst (nm "pre" k), final, mkConst (nm "g" k),
            mkConst (nm "step" k), acc]) base
    thm (n ++ `load_eq) "The program loads to its globals."
      (eqOf (optOf (listOf globT)) (mkApp (mkConst ``Kernel.load) (mkConst n))
        (some' (listOf globT) final))
      chain
    let k := count - 1
    let mName := m ++ .mkSimple (String.ofList ((ds.map Prod.fst).getD k []))
    let some info := (← getEnv).find? mName | throwError "the last definition has no mirror"
    let gk := mkConst (nm "g" k)
    let fstE := mkApp3 (mkConst ``Sigma.fst [0, 0]) treeT (mkConst ``Kernel.Ty.den) gk
    let sndE := mkApp3 (mkConst ``Sigma.snd [0, 0]) treeT (mkConst ``Kernel.Ty.den) gk
    let tyLast := mkApp (mkConst ``Kernel.Ty.den) fstE
    thm (n ++ `last_heq) "The last global's value is the last definition's mirror."
      (mkApp4 (mkConst ``HEq [1]) tyLast sndE info.type (mkConst mName))
      (mkApp2 (mkConst ``HEq.refl [1]) tyLast sndE)

/-- {lit}`kernel_rfl n : lhs = rhs` declares the theorem {lit}`n` proved by reflexivity, the two
sides' definitional equality checked by the kernel alone; a heterogeneous equality
{lit}`HEq lhs rhs` is proved the same way, the kernel checking that the two sides' types are
equal as well. -/
syntax (name := kernelRfl) "kernel_rfl " ident " : " term : command

/-- The elaborator of {lit}`kernel_rfl`. -/
@[command_elab kernelRfl] meta def elabKernelRfl : CommandElab := fun stx ↦ do
  let n := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    let ty ← Term.elabType stx[3]
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let prf ← match ty.eq?, ty.heq? with
      | some (_, lhs, _), _ => Meta.mkEqRefl lhs
      | none, some (_, lhs, _, _) => Meta.mkHEqRefl lhs
      | none, none => throwError "not an equation"
    addDecl <| .thmDecl { name := n, levelParams := [], type := ty, value := prf }

end GebTests.Prototypes.GoedelT.LoadCommand

end
