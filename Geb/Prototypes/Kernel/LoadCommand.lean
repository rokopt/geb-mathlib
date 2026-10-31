/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Loading
public import Geb.Prototypes.GoedelT.Equations
public import Mathlib.Tactic.NormNum
public import Lean.Exception
public import Lean.CoreM
public meta import Geb.Prototypes.Kernel.Image
public meta import Lean.Elab.Command

set_option doc.verso true in
/-!
# Declaring a program's loading, one definition at a time

A program's loading ({name}`Geb.Kernel.load`) is proved one definition at a time: each definition's
tree; the type computed for it; the global it loads, that type with the definition's mirror, whose
declared type is the type's denotation; the list of the globals after it; and the step appending
the global. {lit}`declareLoading` declares these for the definitions of a program not yet
declared, so that a long program's loading is declared over several modules, each continuing from
the globals the modules it imports declare, and a module whose definitions and imports do not
change is not checked again. The command {lit}`geb_load` declares them from a program's image.

The step states that the checker-evaluator {name}`Geb.Kernel.infer` gives the definition the
global's type and its mirror as its denotation. In the mode {lit}`proof` it is a theorem whose proof
applies the checker-evaluator's equation at each node of the definition ({lit}`proveNode`), its
type, its denotation and the proofs of its children's, which the kernel checks in time of the size
of the definition and of the distance from the last global of the globals it refers to, rather
than of its evaluation. In the mode {lit}`native` it is an axiom, declared after the program's
loading has been evaluated by the compiled checker-evaluator; the axioms are listed by
{lit}`#print axioms` for every declaration that depends on them, and the axiom linter permits them
in that mode alone ({lit}`GebMeta.loadingAxiomModules`). Both modes declare the same statements, so
a module depending on the loading is the same in either. {lit}`geb_load`, and the command
{lit}`geb_program` of the tests, read the mode from the environment variable {lit}`GEB_LOADING`,
{lit}`proof` when it is unset.

Each global's type is declared as a literal type tree, built by the kernel's constructors of types,
as the type annotations of the declared trees are ({lit}`typeExpr`), so that the kernel compares
the types the equations at the nodes state by their constructors, and admits a global's mirror at
its type by reducing the type's denotation. The trees, the types, the globals and the lists of
globals are declared with their bodies exposed, since the steps of a later module unfold them,
each at the height above its body's, as the elaborator declares a definition.

## Main definitions

* {lit}`termExpr` — the expression of a definition's tree.
* {lit}`programName` — a program's name, from the current or the root namespace.
* {lit}`proveNode`, {lit}`proveTerm` — the proof of a term's meaning from the checker-evaluator's
  equations at its nodes.
* {lit}`declareLoading` — the declarations of a program's loading beyond those already declared.
* {lit}`nativeLoading` — whether the environment selects the mode {lit}`native`.

## Implementation notes

The commands' elaborators run in Lean's elaboration monads, whose definitions depend on
{lit}`Classical.choice`; they declare kernel-checked definitions and proofs or, in the mode
{lit}`native`, the axioms stating the steps. Lake does not track the environment variable, so a
module built in one mode is not rebuilt when the mode changes; a build in the mode {lit}`proof`
after one in the mode {lit}`native` deletes the outputs of the modules declaring a loading and of
those depending on them ({lit}`scripts/pre-push.sh`).

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
  | Label.lam | Label.fold | Label.iter | Label.nil | Label.para => i == 0
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

/-- The application of a constant to the arguments its binders name, in their order, and the
statement the application proves. -/
meta def applyNamed (c : Name) (args : List (Name × Expr)) : CoreM (Expr × Expr) := do
  let mut ty := (← getConstInfo c).type
  let mut vals : Array Expr := #[]
  while ty.isForall do
    let .forallE x _ body _ := ty | throwError "`{c}` has no binder left"
    let some v := args.lookup x | throwError "no argument `{x}` for `{c}`"
    vals := vals.push v
    ty := body.instantiate1 v
  return (mkAppN (mkConst c) vals, ty)

/-- The denotation an equation {lit}`infer G Γ t = some ⟨A, f⟩` states, {lit}`f`. -/
meta def denOf (e : Expr) : Expr := e.appArg!.appArg!.appArg!

/-- The proof that {lit}`b = true`, for a Boolean the kernel evaluates to {lit}`true`. -/
meta def trueRefl : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- A term's proof of its meaning, from a context's types and the context's expression: the
proof of {lit}`infer G Γ t = some ⟨A, f⟩`, the type {lit}`A`, and the denotation {lit}`f`. -/
abbrev Prover : Type := List Tree → Expr → CoreM (Expr × Tree × Expr)

/-- The proof of a node's meaning from its children's, by the equation of the checker-evaluator
({name}`Geb.Kernel.infer`) at the node's form ({lit}`infer_app` and the others): in the globals
{lit}`G`, which are the list {lit}`R` of {lit}`k` globals reversed ({lit}`hG`, {lit}`hR`), of the
types {lit}`types` and the types' and mirrors' constants {lit}`globs`. A reference is proved by
{name}`Geb.Kernel.infer_ref_reverse`, which reaches a global in as many steps as it is far from
the last, rather than by unfolding the appends that build {lit}`G`, and denotes the mirror of the
global's definition, as the mirror of the definition referring to it does. Each type the node's
equation compares is one its children's equations state, so that the kernel compares types by
their constructors and evaluates no decision of equality. -/
meta def proveNode (G R hG hR : Expr) (k : ℕ) (types : Array Tree) (globs : Array (Expr × Expr))
    (l : ℕ) (cs : List (Tree × Expr × Prover)) : Prover := fun Γ ΓE ↦ do
  let base := [(`G, G), (`Γ, ΓE)]
  let use (c : Name) (args : List (Name × Expr)) (ty : Tree) : CoreM (Expr × Tree × Expr) := do
    let (p, s) ← applyNamed c (base ++ args)
    return (p, ty, denOf s)
  let parts (t : Tree) (lbl : ℕ) : CoreM (Tree × Tree) := match t.label == lbl, t.children with
    | true, [A, B] => pure (A, B)
    | _, _ => throwError "a type of the definition is not of the form its use requires"
  match l, cs with
  | Label.var, [(n, _)] => do
    let some A := Γ[n.label]? | throwError "a variable of the definition is unbound"
    use ``infer_var_get [(`i, mkRawNatLit n.label), (`h, trueRefl)] A
  | Label.lam, [(A, _), (_, b, pb)] => do
    let AE := typeExpr A
    let (hb, B, fb) ← pb (A :: Γ) (mkApp3 (mkConst ``List.cons [0]) (mkConst ``Kernel.Tree) AE ΓE)
    use ``infer_lam [(`A, AE), (`b, b), (`B, typeExpr B), (`fb, fb), (`hA, trueRefl), (`hb, hb)]
      (tArrow A B)
  | Label.app, [(_, f, pf), (_, x, px)] => do
    let (hf, F, ff) ← pf Γ ΓE
    let (hx, _, fx) ← px Γ ΓE
    let (A, B) ← parts F Label.tyArrow
    use ``infer_app [(`f, f), (`x, x), (`A, typeExpr A), (`B, typeExpr B), (`ff, ff), (`fx, fx),
      (`hf, hf), (`hx, hx)] B
  | Label.unit, [] => use ``infer_unit [] tUnit
  | Label.pair, [(_, a, pa), (_, b, pb)] => do
    let (ha, A, fa) ← pa Γ ΓE
    let (hb, B, fb) ← pb Γ ΓE
    use ``infer_pair [(`a, a), (`b, b), (`A, typeExpr A), (`B, typeExpr B), (`fa, fa), (`fb, fb),
      (`ha, ha), (`hb, hb)] (tProd A B)
  | Label.fst, [(_, p, pp)] | Label.snd, [(_, p, pp)] => do
    let (hp, P, fp) ← pp Γ ΓE
    let (A, B) ← parts P Label.tyProd
    use (if l == Label.fst then ``infer_fst else ``infer_snd)
      [(`p, p), (`A, typeExpr A), (`B, typeExpr B), (`fp, fp), (`hp, hp)]
      (if l == Label.fst then A else B)
  | Label.quote, [(t, _)] => use ``infer_quote [(`t, treeExpr t)] tT
  | Label.cond, [(_, c, pc), (_, a, pa), (_, b, pb)] => do
    let (hc, _, fc) ← pc Γ ΓE
    let (ha, A, fa) ← pa Γ ΓE
    let (hb, _, fb) ← pb Γ ΓE
    use ``infer_if [(`c, c), (`a, a), (`b, b), (`A, typeExpr A), (`fc, fc), (`fa, fa), (`fb, fb),
      (`hc, hc), (`ha, ha), (`hb, hb)] A
  | Label.fold, [(A, _)] => use ``infer_fold [(`A, typeExpr A), (`hA, trueRefl)] (foldTy A)
  | Label.para, [(A, _)] => use ``infer_para [(`A, typeExpr A), (`hA, trueRefl)] (foldTy A)
  | Label.iter, [(A, _)] => use ``infer_iter [(`A, typeExpr A), (`hA, trueRefl)] (iterTy A)
  | Label.nil, [(A, _)] => use ``infer_nil [(`A, typeExpr A), (`hA, trueRefl)] (tList A)
  | Label.cons, [(_, x, px), (_, xs, pxs)] => do
    let (hx, A, fx) ← px Γ ΓE
    let (hxs, _, fxs) ← pxs Γ ΓE
    use ``infer_cons [(`x, x), (`xs, xs), (`A, typeExpr A), (`fx, fx), (`fxs, fxs), (`hx, hx),
      (`hxs, hxs)] (tList A)
  | Label.foldr, [(A, _), (B, _)] =>
    use ``infer_foldr [(`A, typeExpr A), (`B, typeExpr B), (`hA, trueRefl), (`hB, trueRefl)]
      (foldrTy A B)
  | Label.lcase, [(A, _), (B, _)] =>
    use ``infer_lcase [(`A, typeExpr A), (`B, typeExpr B), (`hA, trueRefl), (`hB, trueRefl)]
      (lcaseTy A B)
  | Label.prim, [(i, _)] => do
    let some A := (prims.map (·.1))[i.label]?
      | throwError "a primitive of the definition is unknown"
    -- `i < prims.length`, which is `i + 1 ≤ prims.length`, by the kernel's evaluation of `Nat.ble`
    let len := mkApp2 (mkConst ``List.length [0]) (mkConst ``Kernel.Glob) (mkConst ``prims)
    use ``infer_prim [(`i, mkRawNatLit i.label),
      (`h, mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkRawNatLit (i.label + 1)) len trueRefl)] A
  | Label.ref, [(j, _)] => do
    let some A := types[j.label]? | throwError "a reference of the definition is unknown"
    let some (AE, a) := globs[j.label]? | throwError "a reference of the definition is unknown"
    -- `i + j + 1 = R.length`, from `R.length = k`, the two sides' numerals being equal
    let globT := mkConst ``Kernel.Glob
    let len := mkApp2 (mkConst ``List.length [0]) globT R
    let g := mkApp4 (mkConst ``Sigma.mk [0, 0]) (mkConst ``Kernel.Tree) (mkConst ``Kernel.Ty.den)
      AE a
    use ``infer_ref_reverse [(`R, R), (`i, mkRawNatLit (k - 1 - j.label)),
      (`j, mkRawNatLit j.label), (`A, AE), (`a, a), (`hG, hG),
      (`h, mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) len (mkRawNatLit k) hR),
      (`hg, mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) globT)
        (mkApp2 (mkConst ``Option.some [0]) globT g))] A
  | _, _ => throwError "a node of the definition has no meaning"

/-- The expression of a term, as {lit}`termExpr` builds it, and the proof of its meaning by
{lit}`proveNode` at each of its nodes. -/
meta def proveTerm (G R hG hR : Expr) (k : ℕ) (types : Array Tree) (globs : Array (Expr × Expr)) :
    Tree → Expr × Prover :=
  RoseTree.para fun l cs ↦
    let kids := (List.range cs.length).zip cs |>.map fun (i, t, e, _) ↦
      if typePosition l i then typeExpr t else if l == Label.quote then treeExpr t else e
    (mkApp3 (mkConst ``RoseTree.node) (mkConst ``Nat) (mkRawNatLit l)
      (listExpr (mkConst ``Kernel.Tree) kids),
      proveNode G R hG hR k types globs l cs)

/-- The declarations of the loading of the program {lit}`n`, whose definitions are {lit}`ds` with
their names and the types {lit}`types` computed for them, and whose mirror is the namespace
{lit}`m`, beyond those already declared: for each definition, its tree {lit}`n.d`, its type
{lit}`n.ty`, its global {lit}`n.g`, the type and the mirror, and the globals after it
{lit}`n.pre`, each followed by its index, and the step {lit}`n.step` appending its global. The
kernel admits the global where the mirror's declared type is the type's denotation, by the
reduction of that denotation. The globals are also listed in reverse ({lit}`n.rev`), with the
length of that list ({lit}`n.rev_length`) and its reversal's equation with them
({lit}`n.pre_rev`), from which a step's proof reaches a global. A step is a theorem whose proof
applies the checker-evaluator's equation at each node of the definition, which the kernel checks,
or an axiom when {lit}`native` holds. A definition already declared must have the tree given. -/
meta def declareLoading (n m : Name) (ds : List (List Char × Tree)) (types : List Tree)
    (native : Bool) : CoreM Unit := do
  let treeT := mkConst ``Kernel.Tree
  let globT := mkConst ``Kernel.Glob
  let natT := mkConst ``Nat
  let listOf (t : Expr) : Expr := mkApp (mkConst ``List [0]) t
  let optOf (t : Expr) : Expr := mkApp (mkConst ``Option [0]) t
  let some' (t e : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) t e
  let eqOf (t a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) t a b
  let lengthOf (l : Expr) : Expr := mkApp2 (mkConst ``List.length [0]) globT l
  let reverseOf (l : Expr) : Expr := mkApp2 (mkConst ``List.reverse [0]) globT l
  let nm := indexed n
  -- each definition at the height above its body's, as the elaborator declares one, so that the
  -- kernel, which unfolds the higher of two definitions first, unfolds a list of globals to the
  -- append that builds it rather than evaluating that append
  let defn (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl (forceExpose := true) <| .defnDecl
      { name := name, levelParams := [], type := tyE, value := valE,
        hints := .regular (getMaxHeight (← getEnv) valE + 1), safety := .safe }
    addDocStringCore name doc
  let thm (name : Name) (doc : String) (tyE valE : Expr) : CoreM Unit := do
    addDecl <| .thmDecl { name := name, levelParams := [], type := tyE, value := valE }
    addDocStringCore name doc
  let typesA := types.toArray
  -- the constants of each global's type and mirror, which a reference's proof denotes
  let globs := ((List.range ds.length).zip ds).toArray.map fun (k, name, _) ↦
    (mkConst (nm "ty" k), mkConst (m ++ .mkSimple (String.ofList name)))
  unless (← getEnv).contains (nm "pre" 0) do
    let nilG := mkApp (mkConst ``List.nil [0]) globT
    defn (nm "pre" 0) "The globals before the program's first definition." (listOf globT) nilG
    defn (nm "rev" 0) "The globals before the program's first definition, in reverse."
      (listOf globT) nilG
    thm (nm "rev_length" 0) "The number of the globals before the program's first definition."
      (eqOf natT (lengthOf (mkConst (nm "rev" 0))) (mkRawNatLit 0))
      (mkApp2 (mkConst ``Eq.refl [1]) natT (mkRawNatLit 0))
    thm (nm "pre_rev" 0)
      "The globals before the program's first definition are their list in reverse, reversed."
      (eqOf (listOf globT) (mkConst (nm "pre" 0)) (reverseOf (mkConst (nm "rev" 0))))
      (mkApp2 (mkConst ``Eq.refl [1]) (listOf globT) (mkConst (nm "pre" 0)))
  for (k, (name, d)) in (List.range ds.length).zip ds do
    let dname := String.ofList name
    let tree := termExpr d
    if let some info := (← getEnv).find? (nm "d" k) then
      unless info.value? == some tree do
        throwError "the declared tree of the definition `{dname}` is not its tree"
      continue
    let pre := mkConst (nm "pre" k)
    let dk := mkConst (nm "d" k)
    let mirror := m ++ .mkSimple dname
    unless (← getEnv).contains mirror do throwError "the definition `{dname}` has no mirror"
    let some T := typesA[k]? | throwError "the definition `{dname}` has no computed type"
    let ty := mkConst (nm "ty" k)
    defn (nm "d" k) s!"The tree of the program's definition `{dname}`." treeT tree
    defn (nm "ty" k) s!"The type computed for the program's definition `{dname}`." treeT
      (typeExpr T)
    let g := mkConst (nm "g" k)
    defn (nm "g" k)
      s!"The global the program's definition `{dname}` loads: its computed type, and its mirror."
      globT (mkApp4 (mkConst ``Sigma.mk [0, 0]) treeT (mkConst ``Kernel.Ty.den) ty
        (mkConst mirror))
    let snoc := mkApp2 (mkConst ``snoc) pre g
    defn (nm "pre" (k + 1)) s!"The globals after the program's definition `{dname}`."
      (listOf globT) snoc
    let rev := mkConst (nm "rev" k)
    let rev' := mkConst (nm "rev" (k + 1))
    defn (nm "rev" (k + 1)) s!"The globals after the program's definition `{dname}`, in reverse."
      (listOf globT) (mkApp3 (mkConst ``List.cons [0]) globT g rev)
    thm (nm "rev_length" (k + 1))
      s!"The number of the globals after the program's definition `{dname}`."
      (eqOf natT (lengthOf rev') (mkRawNatLit (k + 1)))
      (mkAppN (mkConst ``length_cons_of) #[rev, mkRawNatLit k, g, mkConst (nm "rev_length" k)])
    thm (nm "pre_rev" (k + 1))
      s!"The globals after the program's definition `{dname}` are their list in reverse, \
        reversed."
      (eqOf (listOf globT) (mkConst (nm "pre" (k + 1))) (reverseOf rev'))
      (mkAppN (mkConst ``snoc_reverse) #[pre, rev, g, mkConst (nm "pre_rev" k)])
    let stepTy := eqOf (optOf (listOf globT))
      (mkApp2 (mkConst ``loadStep) (some' (listOf globT) pre) dk) (some' (listOf globT) snoc)
    let step := nm "step" k
    let stepDoc := s!"The program's definition `{dname}` loads its global."
    if native then
      addDecl <| .axiomDecl { name := step, levelParams := [], type := stepTy, isUnsafe := false }
      addDocStringCore step stepDoc
    else
      let (_, prover) := proveTerm pre rev (mkConst (nm "pre_rev" k)) (mkConst (nm "rev_length" k))
        k typesA globs d
      let (h, A, f) ← prover [] (mkApp (mkConst ``List.nil [0]) treeT)
      unless A == T do
        throwError "the type proved for the definition `{dname}` is not its computed type"
      let (prf, _) ← applyNamed ``loadStep_of_infer
        [(`G, pre), (`t, dk), (`A, ty), (`f, f), (`h, h)]
      tryCatchRuntimeEx (thm step stepDoc stepTy prf) fun e ↦
        throwError "the step of the definition `{dname}`: {e.toMessageData}"

/-- Whether the environment variable {lit}`GEB_LOADING` selects the mode {lit}`native`; its other
value is {lit}`proof`, the mode when it is unset. -/
meta def nativeLoading : IO Bool := do
  match ← IO.getEnv "GEB_LOADING" with
  | some "native" => return true
  | none | some "proof" => return false
  | some s => throw <| IO.userError s!"GEB_LOADING is {s}, neither proof nor native"

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
{lit}`m`, beyond the declarations of it already made, in the mode {lit}`nativeLoading` reads.
Its words {lit}`mirror` and {lit}`image` are not reserved, so that a module importing the command
may still use them as identifiers. -/
syntax (name := gebLoad) "geb_load " ident &" mirror " ident &" image " str : command

/-- The elaborator of {lit}`geb_load`. -/
@[command_elab gebLoad] meta def elabGebLoad : CommandElab := fun stx ↦ do
  let n ← programName stx[1].getId
  let m := stx[3].getId
  let some hex := stx[5].isStrLit? | throwError "the image is not a string"
  let some bytes := hexBytes hex | throwError "the image is not hexadecimal"
  let some b := readImage bytes | throwError "the image does not read"
  let some ds := unbundle b | throwError "the bundle does not unbundle"
  let some globs := load (ds.map Prod.snd) | throwError "the program does not load"
  let native ← nativeLoading
  liftCoreM (declareLoading n m ds (globs.map (·.1)) native)

end Geb.Kernel.LoadCommand

end
