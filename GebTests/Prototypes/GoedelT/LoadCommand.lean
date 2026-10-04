/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.LoadCommand
public import Mathlib.Tactic.NormNum
public meta import GebTests.Prototypes.Proofs -- shake: keep
public meta import Lean.Elab.Command

set_option doc.verso true in
/-!
# Commands embedding a Geb program in Lean

The command {lit}`geb_program` reads a Geb program's sources at elaboration, runs the stage-0
compiler's front end on them, and declares, by {name}`Geb.Kernel.LoadCommand.declareLoading`, for
each of the program's definitions not yet declared, its tree, its global and the globals before
it, each global's value the definition of the same name that the bootstrap compiler's Lean backend
emits from the program, and the step of loading it, closed by reflexivity, which the kernel checks
by evaluating the checker-evaluator {name}`Geb.Kernel.infer` on the definition, or stated as an
axiom, in the mode {name}`Geb.Kernel.LoadCommand.nativeLoading` reads. The definitions of a long
program are declared ahead of the command, a layer to a module, by the command {lit}`geb_load`
the generated modules of {lit}`GebMirror` run; {lit}`geb_program` then checks that the trees they
declared are the program's. It declares the loading of the whole program,
composed from the steps, and the equality of the exported globals with their mirrors. The command
{lit}`kernel_rfl` declares a theorem proved by reflexivity, checked by the kernel alone.

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

open Geb Geb.Kernel Geb.Kernel.LoadCommand Lean Elab Command

/-- {lit}`geb_program n from "f" ... mirror m` embeds the program the files make, each followed
by a newline, as the host driver joins sources, read and expanded by the stage-0 compiler's front
end: {lit}`n` is the list of its definitions' trees, {lit}`n.d` followed by each index; {lit}`n.g`
followed by an index is the global its definition loads, at its type and the definition of that
name in the namespace {lit}`m`, the Lean the bootstrap compiler emits from the program, cast along
{lit}`n.den` followed by the index, the equation of their types;
{lit}`n.pre` followed by an index is the list of the globals before it; {lit}`n.step` followed by
an index states that the definition loads its global after them, checked by the kernel;
{lit}`n.load_eq` states that the program loads to its globals, composed from the steps;
{lit}`n.globals` lists them one by one, so that the kernel reaches an entry in as many steps as
its index rather than unfolding the appends that build the last list of them, and
{lit}`n.load_globals` states that the program loads to that list;
{lit}`n.last_heq` states that the last global's value is the last definition's mirror, from that
equation;
and, for each name {lit}`x` after {lit}`exports`, {lit}`n.x_heq` states the same of the global of
the definition of that name. A name {lit}`n` beginning with {lit}`_root_` is taken from the root
namespace, and the declarations of {lit}`n` already made are checked rather than made again. -/
syntax (name := gebProgram)
  "geb_program " ident " from " str* " mirror " ident (" exports " ident+)? : command

/-- The elaborator of {lit}`geb_program`. -/
@[command_elab gebProgram] meta def elabGebProgram : CommandElab := fun stx ↦ do
  let n ← programName stx[1].getId
  let paths := stx[3].getArgs.filterMap (·.isStrLit?)
  let m := stx[5].getId
  let exported := if stx[6].isNone then #[] else stx[6][1].getArgs.map (·.getId)
  -- the sources are read as bytes, a character to a byte, as the hosts read them
  let mut text : List Char := []
  for p in paths do
    text := text ++ (← IO.FS.readBinFile p).data.toList.map (fun x ↦ Char.ofNat x.toNat) ++ ['\n']
  let r ← match runMain GoedelT.ProofTests.bundler.toList (nameTree text) with
    | some r => pure r
    | none => throwError "the front end does not run"
  let some b := (if r.label == 1 then r.children.head? else none)
    | throwError "the program does not read"
  let some ds := unbundle b | throwError "the bundle does not unbundle"
  if (load (ds.map Prod.snd)).isNone then throwError "the program does not load"
  let treeT := mkConst ``Kernel.Tree
  let globT := mkConst ``Kernel.Glob
  let listOf (t : Expr) : Expr := mkApp (mkConst ``List [0]) t
  let optOf (t : Expr) : Expr := mkApp (mkConst ``Option [0]) t
  let some' (t e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) t e
  let eqOf (t a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) t a b
  let nm := indexed n
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
    declareLoading n m ds (← nativeLoading)
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
    -- the last list of globals, built by appending, which the kernel unfolds once here, rather
    -- than at every lookup of an entry
    let globals := n ++ `globals
    defn globals "The program's globals, listed one by one." (listOf globT)
      (listExpr globT ((List.range count).map fun k ↦ mkConst (nm "g" k)))
    thm (n ++ `load_globals) "The program loads to its globals, listed one by one."
      (eqOf (optOf (listOf globT)) (mkApp (mkConst ``Kernel.load) (mkConst n))
        (some' (listOf globT) (mkConst globals)))
      (mkConst (n ++ `load_eq))
    -- the global of the definition of index k is its mirror, cast along the equation of their
    -- types, stated without elaborating the global's type, whose reduction evaluates the checker
    let heq (k : ℕ) (thmName : Name) (doc : String) : CoreM Unit := do
      let mName := m ++ .mkSimple (String.ofList ((ds.map Prod.fst).getD k []))
      let some info := (← getEnv).find? mName | throwError "the definition {mName} has no mirror"
      let gk := mkConst (nm "g" k)
      let fstE := mkApp3 (mkConst ``Sigma.fst [0, 0]) treeT (mkConst ``Kernel.Ty.den) gk
      let sndE := mkApp3 (mkConst ``Sigma.snd [0, 0]) treeT (mkConst ``Kernel.Ty.den) gk
      let tyK := mkApp (mkConst ``Kernel.Ty.den) fstE
      let den := mkApp (mkConst ``Kernel.Ty.den)
        (mkApp2 (mkConst ``defType) (mkConst (nm "pre" k)) (mkConst (nm "d" k)))
      thm thmName doc (mkApp4 (mkConst ``HEq [1]) tyK sndE info.type (mkConst mName))
        (mkApp4 (mkConst ``cast_heq [1]) info.type den (mkConst (nm "den" k)) (mkConst mName))
    heq (count - 1) (n ++ `last_heq) "The last global's value is the last definition's mirror."
    for x in exported do
      let some k := (ds.map Prod.fst).idxOf? x.getString!.toList
        | throwError "the program has no definition {x}"
      heq k (n ++ .mkSimple s!"{x.getString!}_heq")
        s!"The global of the definition `{x.getString!}` is its mirror."

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
