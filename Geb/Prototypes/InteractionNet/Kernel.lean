/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.Kernel.Eval
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The kernel's first-order interaction system

Kernel functions are defunctionalized closures: code and type attributes together with one
data port per captured environment entry. One application operation dispatches on these
closures and partially applied constants. A fold operation carries its source occurrence
as an attribute and has a rule for a tree constructor. It constructs recursive calls over
the children and applies the step to the resulting list. The paramorphism also reconstructs
the original node from its child wires; fans perform the required data copying.

The translation preserves the kernel's lazy conditional by capturing each branch in a
thunk. Selection forces only the chosen thunk. All dynamic values, including closures and
thunks, are first-order data and are copied constructor by constructor by the generic
translation. No rule calls the kernel's evaluator or denotation to compute its result.

## Main definitions

* {lit}`Constructor`, {lit}`Op` — runtime data and named operations.
* {lit}`compile` — kernel syntax to first-order expressions.
* {lit}`rewrite`, {lit}`program` — constructor-dispatch rules.
* {lit}`system`, {lit}`initial`, {lit}`readback`, {lit}`run` — executable nets and observation.

## References

* {cite}`MackiePintoVilaca2009`, for program-specific iterator agents.
* {cite}`HassanMackieSato2015`, Section 3, for configurations and interaction.

## Tags

bootstrap, kernel, interaction net, defunctionalization, closure, fold, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel
open FirstOrder

/-- First-order runtime constructors. Code and types are static attributes. -/
inductive Constructor
  /-- A rose-tree node. -/
  | tree (label children : ℕ)
  /-- The unit value. -/
  | unit
  /-- A pair of values. -/
  | pair
  /-- An empty list at its element type. -/
  | nil (type : Tree)
  /-- A list head and tail. -/
  | cons
  /-- A closure over a finite environment. -/
  | closure (site : List ℕ) (type body : Tree) (captures : ℕ)
  /-- An unevaluated conditional branch over a finite environment. -/
  | thunk (site : List ℕ) (body : Tree) (captures : ℕ)
  /-- A constant with the arguments already supplied. -/
  | partialApp (site : List ℕ) (head : Tree) (supplied : ℕ)

/-- The ports of each first-order value. -/
abbrev dataArity : Constructor → ℕ
  | .tree _ n => n
  | .unit | .nil _ => 0
  | .pair | .cons => 2
  | .closure _ _ _ n | .thunk _ _ n | .partialApp _ _ n => n

/-- Named operations. Fold attributes retain the originating kernel syntax. -/
inductive Op
  /-- Apply a closure or a partially applied constant. -/
  | apply
  /-- Project from a pair. -/
  | project (second : Bool)
  /-- Select a conditional's thunk. -/
  | choose
  /-- Force one selected thunk. -/
  | force
  /-- Load a program definition. -/
  | reference (index : ℕ)
  /-- Fold a tree at a source occurrence. -/
  | fold (source : List ℕ) (type : Tree)
  /-- Fold a tree with access to the original node. -/
  | para (source : List ℕ) (type : Tree)
  /-- Iterate over a tree's label. -/
  | iter (source : List ℕ)
  /-- Fold a list. -/
  | foldr (source : List ℕ)
  /-- Analyze a list. -/
  | lcase
  /-- Dispatch a primitive on its first tree. -/
  | primitive (index : ℕ)
  /-- Finish a binary numeric primitive after reading its first label. -/
  | numeric (index left : ℕ)
  /-- Select a child using the principal tree's label as index. -/
  | select
  /-- Build a tree from a list of children. -/
  | make (label : ℕ)
  /-- Prepend a child to a constructed tree. -/
  | prepend
  /-- Compare a second tree with a previously inspected constructor. -/
  | compare (label children : ℕ)
  /-- Conjoin two tree truth values. -/
  | and

/-- Kernel expressions in a finite context. -/
abbrev E (n : ℕ) := Expr (φ := Op) dataArity n

/-- Construct a runtime value from the correctly sized list of its fields. -/
def con {n : ℕ} (a : Constructor) (xs : List (E n)) (h : xs.length = dataArity a) : E n :=
  Expr.con a fun i ↦ xs[Fin.cast h.symm i]

/-- A tree constructor over expression children. -/
def tree {n : ℕ} (l : ℕ) (xs : List (E n)) : E n := con (.tree l xs.length) xs rfl

/-- A literal rose tree, containing no variables. -/
def literal {n : ℕ} : Tree → E n := RoseTree.elim tree

/-- An expression for the unit value. -/
def unit {n : ℕ} : E n := con .unit [] rfl

/-- An expression for a pair. -/
def pair {n : ℕ} (x y : E n) : E n := con .pair [x, y] rfl

/-- An expression for the empty list. -/
def nil {n : ℕ} (A : Tree) : E n := con (.nil A) [] rfl

/-- An expression for a list cell. -/
def cons {n : ℕ} (x xs : E n) : E n := con .cons [x, xs] rfl

/-- A list value over a given element type. -/
def list {n : ℕ} (A : Tree) (xs : List (E n)) : E n := xs.foldr cons (nil A)

/-- A first-order call. -/
abbrev call {n : ℕ} (f : Op) (x : E n) (xs : List (E n) := []) : E n := Expr.call f x xs

/-- A function applied to an argument. -/
def apply {n : ℕ} (f x : E n) : E n := call .apply f [x]

/-- Translate a source occurrence in an expression environment. Its path identifies the
definition and child positions, so distinct fold occurrences have distinct operation symbols.
Bodies of closures and conditional branches are stored as code. -/
def compileAt {n : ℕ} : Tree → List ℕ → List (E n) → Option (E n) :=
  RoseTree.para fun l rs site en ↦
    match l, rs with
    | Label.var, [(i, _)] => en[i.label]?
    | Label.lam, [(A, _), (b, _)] =>
      some (con (.closure (site ++ [1]) A b en.length) en rfl)
    | Label.app, [(_, f), (_, x)] =>
      do return apply (← f (site ++ [0]) en) (← x (site ++ [1]) en)
    | Label.unit, [] => some unit
    | Label.pair, [(_, a), (_, b)] =>
      do return pair (← a (site ++ [0]) en) (← b (site ++ [1]) en)
    | Label.fst, [(_, p)] => (p (site ++ [0]) en).map (call (.project false) ·)
    | Label.snd, [(_, p)] => (p (site ++ [0]) en).map (call (.project true) ·)
    | Label.quote, [(t, _)] => some (literal t)
    | Label.cond, [(_, c), (a, _), (b, _)] => do
      let c ← c (site ++ [0]) en
      return call .choose c [con (.thunk (site ++ [1]) a en.length) en rfl,
        con (.thunk (site ++ [2]) b en.length) en rfl]
    | Label.nil, [(A, _)] => some (nil A)
    | Label.cons, [(_, x), (_, xs)] =>
      do return cons (← x (site ++ [0]) en) (← xs (site ++ [1]) en)
    | Label.fold, [(A, _)] | Label.para, [(A, _)] | Label.iter, [(A, _)] =>
      some (con (.partialApp site (RoseTree.node l [A]) 0) [] rfl)
    | Label.foldr, [(A, _), (B, _)] | Label.lcase, [(A, _), (B, _)] =>
      some (con (.partialApp site (RoseTree.node l [A, B]) 0) [] rfl)
    | Label.prim, [(k, _)] =>
      some (con (.partialApp site (RoseTree.node Label.prim [leaf k.label]) 0) [] rfl)
    | Label.ref, [(i, _)] => some (call (.reference i.label) unit)
    | _, _ => none

/-- The entry expression occupies root zero; referenced definitions occupy roots one and up. -/
def compile {n : ℕ} (t : Tree) (en : List (E n)) : Option (E n) := compileAt t [0] en

/-- Dispatch a saturated constant into the corresponding first-order operation. -/
def saturated {n : ℕ} (site : List ℕ) (h : Tree) (args : List (E n)) : Option (E n) :=
  match h.label, h.children, args with
  | Label.fold, [A], [f, t] => some (call (.fold site A) t [f])
  | Label.para, [A], [f, t] => some (call (.para site A) t [f])
  | Label.iter, [_], [s, z, t] => some (call (.iter site) t [s, z])
  | Label.foldr, [_, _], [f, z, xs] => some (call (.foldr site) xs [f, z])
  | Label.lcase, [_, _], [xs, z, f] => some (call .lcase xs [z, f])
  | Label.prim, [k], x :: xs => some (call (.primitive k.label) x xs)
  | _, _, _ => none

/-- Numeric operations act on label attributes; no tree is traversed here. -/
def numeric (k a b : ℕ) : Option ℕ :=
  if k = Prim.add then some (a + b)
  else if k = Prim.sub then some (a - b)
  else if k = Prim.mul then some (a * b)
  else if k = Prim.div then some (a / b)
  else if k = Prim.mod then some (a % b)
  else if k = Prim.eq then some (if a = b then 1 else 0)
  else if k = Prim.lt then some (if a < b then 1 else 0)
  else none

/-- A primitive's first constructor rule. Tree children are variables, so returning or
discarding them is handled by the expression evaluator's fans. -/
def primitive {n : ℕ} (k l : ℕ) (cs rs : List (E n)) : Option (E n) :=
  match rs with
  | [] =>
    if k = Prim.label then some (tree l [])
    else if k = Prim.arity then some (tree cs.length [])
    else if k = Prim.children then some (list tT cs)
    else if k = Prim.log2 then some (tree l.log2 [])
    else none
  | [b] =>
    if k = Prim.child then some (call .select b cs)
    else if k = Prim.node then some (call (.make l) b)
    else if k = Prim.equal then some (call (.compare l cs.length) b cs)
    else some (call (.numeric k l) b)
  | _ => none

/-- The kernel's constructor-dispatch rules, over expression variables for the actual
fields and further arguments. This function cannot inspect the terms occupying those ports. -/
def rewrite {n : ℕ} (P : List Tree) (f : Op) (a : Constructor)
    (cs rs : List (E n)) : Option (E n) :=
  match f, a, cs, rs with
  | .apply, .closure site _ b _, cs, [x] => compileAt b site (x :: cs)
  | .apply, .partialApp site h _, cs, [x] =>
    let args := cs ++ [x]
    if args.length < Geb.Kernel.Eval.arity h then
      some (con (.partialApp site h args.length) args rfl)
    else saturated site h args
  | .project false, .pair, [x, _], [] => some x
  | .project true, .pair, [_, y], [] => some y
  | .choose, .tree l _, _, [a, b] => some (call .force (if l = 0 then b else a))
  | .force, .thunk site b _, cs, [] => compileAt b site cs
  | .reference i, .unit, [], [] => P[i]?.bind (compileAt · [i + 1] [])
  | .fold h A, .tree l _, cs, [f] =>
    some (apply (apply f (tree l [])) (list A (cs.map fun c ↦ call (.fold h A) c [f])))
  | .para h A, .tree l _, cs, [f] =>
    some (apply (apply f (tree l cs)) (list A (cs.map fun c ↦ call (.para h A) c [f])))
  | .iter h, .tree l _, _, [s, z] =>
    some (if l = 0 then z else apply s (call (.iter h) (tree (l - 1) []) [s, z]))
  | .foldr _, .nil _, [], [_, z] => some z
  | .foldr h, .cons, [x, xs], [f, z] =>
    some (apply (apply f x) (call (.foldr h) xs [f, z]))
  | .lcase, .nil _, [], [z, _] => some z
  | .lcase, .cons, [x, xs], [_, f] => some (apply (apply f x) xs)
  | .primitive k, .tree l _, cs, rs => primitive k l cs rs
  | .numeric k l, .tree r _, _, [] => (numeric k l r).map (tree · [])
  | .select, .tree i _, _, rs => some (rs[i]?.getD (tree 0 []))
  | .make l, .nil _, [], [] => some (tree l [])
  | .make l, .cons, [x, xs], [] => some (call .prepend (call (.make l) xs) [x])
  | .prepend, .tree l _, cs, [x] => some (tree l (x :: cs))
  | .compare l k, .tree r m, cs, rs =>
    if l = r ∧ k = m then
      some ((rs.zipWith (fun x y ↦ call (.primitive Prim.equal) x [y]) cs).foldr
        (fun x acc ↦ call .and x [acc]) (tree 1 []))
    else some (tree 0 [])
  | .and, .tree l _, _, [b] => some (if l = 0 then tree 0 [] else b)
  | _, _, _, _ => none

/-- The program specializes the dispatch rules to its loaded definitions. -/
def program (P : List Tree) : Program (φ := Op) dataArity where
  rewrite f others a :=
    rewrite P f a
      (List.ofFn fun i : Fin (dataArity a) ↦ Term.var (Fin.castAdd others i))
      (List.ofFn fun i : Fin others ↦ Term.var (Fin.natAdd (dataArity a) i))

/-- The program's executable interaction system. -/
def system (P : List Tree) : System (netArity (φ := Op) dataArity) :=
  FirstOrder.system dataArity (program P)

/-- Compile a closed function and apply it to an input tree. -/
def initial (t x : Tree) : Option (Config (netArity (φ := Op) dataArity)) :=
  (compile t []).map fun f ↦ FirstOrder.initial dataArity (apply f (literal x))

/-- Read a tree from a term containing only rose-tree constructors. Other values, unresolved
names, and control agents do not read back as trees. -/
def readback : Term (netArity (φ := Op) dataArity) ℕ → Option Tree :=
  PFunctor.FreeM.rec (fun _ ↦ none) fun a _ rs ↦
    match a with
    | .inl (.inl (.tree l _)) => (List.ofFn rs).mapM id |>.map (RoseTree.node l)
    | _ => none

/-- Execute a bounded run. A result is returned only after all equations have been consumed,
with exactly one observable tree. Exhaustion and stuck residual nets return no result. -/
def run (P : List Tree) (steps : ℕ) (t x : Tree) : Option Tree := do
  let c ← initial t x
  let d := (system P).run steps c
  if !d.equations.isEmpty then none else
    match d.interface with
    | [v] => readback v
    | _ => none

end Geb.InteractionNet.Kernel

end
