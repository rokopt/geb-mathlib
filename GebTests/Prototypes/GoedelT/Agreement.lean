/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Reader
public import GebMirror.GoedelT
public meta import GebTests.Prototypes.Proofs -- shake: keep
public meta import Lean.Elab.Command

set_option doc.verso true in
/-!
# The agreement of the checker of Gödel's T written in Geb

Work in progress: the method of the proof.

## Tags

Gödel's T, checker, denotation, agreement
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.Agreement

open Geb Geb.Kernel Lean Elab Command

/-- The step of loading a program: a definition checked and evaluated in the globals before it,
and appended to them. -/
def loadStep (acc : Option (List Glob)) (t : Tree) : Option (List Glob) := do
  let G ← acc
  let m ← infer G [] t
  some (G ++ [⟨m.1, m.2 ()⟩])

/-- The type of a definition in the globals before it, or the type of trees where it is
ill-typed. -/
def defType (G : List Glob) (t : Tree) : Tree := ((infer G [] t).map (·.1)).getD tT

/-- A list of globals with one more appended. -/
def snoc (G : List Glob) (g : Glob) : List Glob := G ++ [g]

/-- Loading a program is the fold of its step over its definitions. -/
theorem load_eq_foldl (D : List Tree) : load D = D.foldl loadStep (some []) := rfl

/-- A step that appends a global, followed by the rest of the fold. -/
theorem foldl_loadStep_cons {D : List Tree} {t : Tree} {G G' : List Glob} {g : Glob}
    (h : loadStep (some G) t = some (G ++ [g]))
    (h' : D.foldl loadStep (some (G ++ [g])) = some G') :
    (t :: D).foldl loadStep (some G) = some G' := by
  rw [List.foldl_cons, h, h']

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
an index states that the definition loads its global after them, checked by the kernel; and
{lit}`n.load_eq` states that the program loads to its globals, composed from the steps. -/
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
  let defn (name : Name) (tyE valE : Expr) : CoreM Unit :=
    addDecl <| .defnDecl
      { name := name, levelParams := [], type := tyE, value := valE,
        hints := .regular 0, safety := .safe }
  let thm (name : Name) (tyE valE : Expr) : CoreM Unit :=
    addDecl <| .thmDecl { name := name, levelParams := [], type := tyE, value := valE }
  let count := ds.length
  liftCoreM do
    defn (nm "pre" 0) (listOf globT) (mkApp (mkConst ``List.nil [0]) globT)
    for (k, (name, d)) in (List.range count).zip ds do
      let pre := mkConst (nm "pre" k)
      defn (nm "d" k) treeT (termExpr d)
      defn (nm "g" k) globT (mkApp4 (mkConst ``Sigma.mk [0, 0]) treeT (mkConst ``Kernel.Ty.den)
        (mkApp2 (mkConst ``defType) pre (mkConst (nm "d" k)))
        (mkConst (m ++ .mkSimple (String.ofList name))))
      let snoc := mkApp2 (mkConst ``snoc) pre (mkConst (nm "g" k))
      defn (nm "pre" (k + 1)) (listOf globT) snoc
      let lhs := mkApp2 (mkConst ``loadStep) (some' (listOf globT) pre) (mkConst (nm "d" k))
      let t0 ← IO.monoMsNow
      try
        thm (nm "step" k) (eqOf (optOf (listOf globT)) lhs (some' (listOf globT) snoc))
          (mkApp2 (mkConst ``Eq.refl [1]) (optOf (listOf globT)) lhs)
      catch e => logInfo m!"step {k} fails: {e.toMessageData}"
      let t1 ← IO.monoMsNow
      if t1 - t0 > 200 then
        logInfo m!"step {k} ({String.ofList ((ds.map Prod.fst).getD k [])}): {t1 - t0} ms"
    defn n (listOf treeT) (listExpr treeT ((List.range count).map fun k ↦ mkConst (nm "d" k)))
    let final := mkConst (nm "pre" count)
    let base := mkApp2 (mkConst ``Eq.refl [1]) (optOf (listOf globT)) (some' (listOf globT) final)
    let chain := (List.range count).foldr (fun k acc ↦
        let rest := listExpr treeT (((List.range count).drop (k + 1)).map fun j ↦
          mkConst (nm "d" j))
        mkAppN (mkConst ``foldl_loadStep_cons)
          #[rest, mkConst (nm "d" k), mkConst (nm "pre" k), final, mkConst (nm "g" k),
            mkConst (nm "step" k), acc]) base
    let t0 ← IO.monoMsNow
    thm (n ++ `load_eq)
      (eqOf (optOf (listOf globT)) (mkApp (mkConst ``Kernel.load) (mkConst n))
        (some' (listOf globT) final))
      chain
    logInfo m!"load_eq: {(← IO.monoMsNow) - t0} ms"

/-- {lit}`kernel_rfl n : lhs = rhs` declares the theorem {lit}`n` proved by reflexivity, the two
sides' definitional equality checked by the kernel alone. -/
syntax (name := kernelRfl) "kernel_rfl " ident " : " term : command

/-- The elaborator of {lit}`kernel_rfl`. -/
@[command_elab kernelRfl] meta def elabKernelRfl : CommandElab := fun stx ↦ do
  let n := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    let ty ← Term.elabType stx[3]
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let some (_, lhs, _) := ty.eq? | throwError "not an equation"
    let prf ← Meta.mkEqRefl lhs
    addDecl <| .thmDecl { name := n, levelParams := [], type := ty, value := prf }

/-- The global of index {lit}`k` at the type {lit}`A`, where it has that type. -/
def globAt (G : List Glob) (k : ℕ) (A : Tree) : Option (Ty.den A) :=
  G[k]?.bind fun g ↦ if h : g.1 = A then some (cast (congrArg Ty.den h) g.2) else none

set_option Elab.async false in
geb_program prelude from "bootstrap/prelude.geb" mirror GebMirror.GoedelT

set_option Elab.async false in
geb_program checker from "bootstrap/prelude.geb" "bootstrap/reader.geb" "bootstrap/check.geb"
  "bootstrap/goedel-t/equations.geb" mirror GebMirror.GoedelT

end GebTests.Prototypes.GoedelT.Agreement

end
