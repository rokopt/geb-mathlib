/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.Kernel.Basic
public import Geb.Prototypes.Metalogic.Equations

set_option doc.verso true in
/-!
# The translation of the kernel into the internal language

The kernel's types and terms ({name}`Geb.Kernel.infer`) translated into the Mitchell–Bénabou
language ({name}`Geb.FreeTopos.Internal.Term`). The base type of trees is the rose-tree object,
whose labels are the natural numbers object, and the unit, product, function and list types are
the terminal object, products, exponentials and list objects. A term former is the language's
former of the same name; a quoted tree is the construction of its nodes, each label a numeral,
the successor applied as many times as its value to zero; the conditional, the kernel's folds
and iteration, its case analysis of lists and its primitives are applications of definitions
of the language.

The language's folds take their start and their step in contexts of their own, so a fold whose
step uses a variable of the context folds into the exponential of that variable's type and is
applied to it, as the benchmark's appending does. The primitives are functions of the labels
and the children of trees, the labels' arithmetic by the folds of the natural numbers object,
in unary: a numeral of the language has the size of its value.

## Main definitions

* {lit}`Translation.ty` — the translation of a kernel type.
* {lit}`Translation.prims`, {lit}`Translation.lib` — the primitive arrows and the definitions
  the translation applies.
* {lit}`Translation.quoteT` — the translation of a quoted tree.
* {lit}`Translation.term` — the translation of a kernel term, with its kernel type.
* {lit}`Translation.globals` — the constants of a translated program.
* {lit}`Translation.thm` — the translation of a theorem of the computational core.

## Tags

internal language, System T, translation, rose tree, natural numbers object
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Prim Globals Definition)
open scoped FinEnum

/-! The translation of types. -/

/-- The translation of a kernel type: the base type to the rose-tree object, and the unit,
product, function and list types to the terminal object, products, exponentials and list
objects; nothing for a tree that is not a type. -/
def ty : Tree → Option Tree :=
  RoseTree.elim fun l rs ↦
    match l, rs with
    | Kernel.Label.tyTree, [] => some rose
    | Kernel.Label.tyUnit, [] => some one
    | Kernel.Label.tyProd, [a, b] => do pure (prod (← a) (← b))
    | Kernel.Label.tyArrow, [a, b] => do pure (exp (← a) (← b))
    | Kernel.Label.tyList, [a] => do pure (list (← a))
    | _, _ => none

/-! The primitive arrows and the terms built with them. -/

/-- The primitive arrows: zero, the successor, the empty list and construction, of an object
parameter, and the construction of a rose tree, by these indices. -/
def prims : List Prim :=
  [Internal.zeroPrim, Internal.succPrim, Internal.nilPrim, Internal.consPrim, Internal.nodePrim]

/-- Zero. -/
def zeroT : Term := Term.arr 0 [] Term.star

/-- The successor of a number. -/
def succT (n : Term) : Term := Term.arr 1 [] n

/-- The empty list of elements of the type {lit}`a`. -/
def nilT (a : Tree) : Term := Term.arr 2 [a] Term.star

/-- The list of an element of the type {lit}`a` before a list. -/
def consT (a : Tree) (h t : Term) : Term := Term.arr 3 [a] (Term.pair h t)

/-- The rose tree of a pair of a label and a list of children. -/
def nodeT (p : Term) : Term := Term.arr 4 [] p

/-- The leaf of a label. -/
def leafT (n : Term) : Term := nodeT (Term.pair n (nilT rose))

/-- The numeral of a natural number: the successor applied as many times as its value to
zero. -/
def numeral (n : ℕ) : Term := Nat.rec zeroT (fun _ r ↦ succT r) n

/-- The translation of a quoted tree: the construction of each node from its label's numeral
and the list of its children's translations. -/
def quoteT : Tree → Term :=
  RoseTree.elim fun l cs ↦ nodeT (Term.pair (numeral l) (cs.foldr (consT rose) (nilT rose)))

/-! The definitions. -/

/-- The variable of a de Bruijn index. -/
abbrev v (i : ℕ) : Term := Term.var i

/-- The application of the definition of an index at objects to arguments, the first first. -/
def call (k : ℕ) (θ : List Tree) (args : List Term) : Term := Term.defn k θ args.reverse

/-- A definition in object parameters from parameters of types, the first first, so that the
last is the variable of index zero in its body. -/
def mkDefn (arity : ℕ) (params : List Tree) (type : Tree) (body : Term) : Defn :=
  ⟨arity, params.reverse, type, body⟩

/-! The indices of the definitions, in the order of {lit}`lib`. -/

namespace D

/-- The label of a tree. -/
abbrev lab : ℕ := 0
/-- The label and the list of the children of a tree. -/
abbrev unnode : ℕ := 1
/-- The list of the children of a tree. -/
abbrev children : ℕ := 2
/-- The length of a list. -/
abbrev length : ℕ := 3
/-- Addition. -/
abbrev add : ℕ := 4
/-- The predecessor. -/
abbrev pred : ℕ := 5
/-- Truncated subtraction. -/
abbrev sub : ℕ := 6
/-- Multiplication. -/
abbrev mul : ℕ := 7
/-- Whether a number is zero, as one or zero. -/
abbrev isZero : ℕ := 8
/-- Whether two numbers are equal, as one or zero. -/
abbrev eqN : ℕ := 9
/-- Whether one number is less than another, as one or zero. -/
abbrev ltN : ℕ := 10
/-- The conditional on a number. -/
abbrev cond : ℕ := 11
/-- The quotient and the remainder. -/
abbrev divMod : ℕ := 12
/-- The base-two logarithm. -/
abbrev log2 : ℕ := 13
/-- The tail of a list. -/
abbrev tail : ℕ := 14
/-- The head of a list, or a default. -/
abbrev headD : ℕ := 15
/-- A list without its first elements. -/
abbrev drop : ℕ := 16
/-- The applications of a list of functions to one argument. -/
abbrev mapApp : ℕ := 17
/-- The conjunction of two numbers read as truth values. -/
abbrev and : ℕ := 18
/-- Whether a list of functions holds, elementwise, of a list of trees of the same length. -/
abbrev allZip : ℕ := 19
/-- Whether two trees are equal, as one or zero. -/
abbrev equal : ℕ := 20

end D

/-- The object variable of a definition's first object parameter. -/
abbrev X₀ : Tree := x 0

/-- The object variable of a definition's second object parameter. -/
abbrev X₁ : Tree := x 1

/-- The conditional on a number at the type {lit}`a`: the second term when the number is not
zero, the third when it is. -/
def condT (a : Tree) (c t u : Term) : Term := call D.cond [a] [c, t, u]

/-- The definitions the translation applies, by the indices of {lit}`D`, each over those
before it: the label, the children and the length, arithmetic, comparison and the conditional
on the natural numbers, the tail, head and dropping of lists, the applications of a list of
functions, and the equality of trees. -/
def lib : List Defn := [
  -- the label of a tree: the fold taking each node to its label
  mkDefn 0 [rose] nat (Term.roseRec nat (Term.fst (v 0)) (v 0)),
  -- the label and the children: the fold rebuilding each child from its own
  mkDefn 0 [rose] (prod nat (list rose))
    (Term.roseRec (prod nat (list rose))
      (Term.pair (Term.fst (v 0))
        (Term.listRec (nilT rose) (consT rose (nodeT (v 1)) (v 0)) (Term.snd (v 0))))
      (v 0)),
  -- the children
  mkDefn 0 [rose] (list rose) (Term.snd (call D.unnode [] [v 0])),
  -- the length of a list of the object parameter
  mkDefn 1 [list X₀] nat (Term.listRec zeroT (succT (v 0)) (v 0)),
  -- addition, by recursion on the second argument into functions of the first
  mkDefn 0 [nat, nat] nat
    (Term.app (Term.natRec (Term.lam nat (v 0)) (Term.lam nat (succT (Term.app (v 1) (v 0))))
      (v 0)) (v 1)),
  -- the predecessor: the first component of the pair of it and the number
  mkDefn 0 [nat] nat
    (Term.snd (Term.natRec (Term.pair zeroT zeroT)
      (Term.pair (succT (Term.fst (v 0))) (Term.fst (v 0))) (v 0))),
  -- truncated subtraction: the predecessor as many times as the second argument
  mkDefn 0 [nat, nat] nat
    (Term.app (Term.natRec (Term.lam nat (v 0))
      (Term.lam nat (call D.pred [] [Term.app (v 1) (v 0)])) (v 0)) (v 1)),
  -- multiplication, by recursion on the second argument into functions of the first
  mkDefn 0 [nat, nat] nat
    (Term.app (Term.natRec (Term.lam nat zeroT)
      (Term.lam nat (call D.add [] [Term.app (v 1) (v 0), v 0])) (v 0)) (v 1)),
  -- whether a number is zero
  mkDefn 0 [nat] nat (Term.natRec (succT zeroT) zeroT (v 0)),
  -- equality: both truncated differences zero
  mkDefn 0 [nat, nat] nat
    (call D.isZero [] [call D.add [] [call D.sub [] [v 1, v 0], call D.sub [] [v 0, v 1]]]),
  -- order: the truncated difference of the second and the first not zero
  mkDefn 0 [nat, nat] nat (call D.isZero [] [call D.isZero [] [call D.sub [] [v 0, v 1]]]),
  -- the conditional on a number, by its fold into functions of the two branches
  mkDefn 1 [nat, X₀, X₀] X₀
    (Term.app (Term.app (Term.natRec (Term.lam X₀ (Term.lam X₀ (v 0)))
      (Term.lam X₀ (Term.lam X₀ (v 1))) (v 2)) (v 1)) (v 0)),
  -- the quotient and the remainder, by recursion on the dividend into functions of the
  -- divisor: the remainder's successor reset at the divisor
  mkDefn 0 [nat, nat] (prod nat nat)
    (let st := Term.app (v 1) (v 0)
     Term.app (Term.natRec (Term.lam nat (Term.pair zeroT zeroT))
      (Term.lam nat (condT (prod nat nat) (call D.eqN [] [succT (Term.snd st), v 0])
        (Term.pair (succT (Term.fst st)) zeroT) (Term.pair (Term.fst st) (succT (Term.snd st)))))
      (v 1)) (v 0)),
  -- the base-two logarithm: the number of the powers of two from two on at most the number,
  -- counted by recursion on the number into functions of it
  mkDefn 0 [nat] nat
    (let st := Term.app (v 1) (v 0)
     let dbl := call D.add [] [Term.snd st, Term.snd st]
     Term.fst (Term.app (Term.natRec (Term.lam nat (Term.pair zeroT (succT (succT zeroT))))
      (Term.lam nat (condT (prod nat nat) (call D.isZero [] [call D.sub [] [Term.snd st, v 0]])
        (Term.pair (succT (Term.fst st)) dbl) (Term.pair (Term.fst st) dbl)))
      (v 0)) (v 0))),
  -- the tail of a list: the second component of the pair of the list and its tail
  mkDefn 1 [list X₀] (list X₀)
    (Term.snd (Term.listRec (Term.pair (nilT X₀) (nilT X₀))
      (Term.pair (consT X₀ (v 1) (Term.fst (v 0))) (Term.fst (v 0))) (v 0))),
  -- the head of a list, or the default for the empty list
  mkDefn 1 [X₀, list X₀] X₀
    (Term.app (Term.listRec (Term.lam X₀ (v 0)) (Term.lam X₀ (v 2)) (v 0)) (v 1)),
  -- a list without as many first elements as the number
  mkDefn 1 [list X₀, nat] (list X₀)
    (Term.app (Term.natRec (Term.lam (list X₀) (v 0))
      (Term.lam (list X₀) (call D.tail [X₀] [Term.app (v 1) (v 0)])) (v 0)) (v 1)),
  -- the applications of a list of functions to one argument
  mkDefn 2 [list (exp X₀ X₁), X₀] (list X₁)
    (Term.app (Term.listRec (Term.lam X₀ (nilT X₁))
      (Term.lam X₀ (consT X₁ (Term.app (v 2) (v 0)) (Term.app (v 1) (v 0)))) (v 1)) (v 0)),
  -- conjunction
  mkDefn 0 [nat, nat] nat (condT nat (v 1) (v 0) zeroT),
  -- whether a list of functions holds of a list of trees of its length, elementwise
  mkDefn 0 [list (exp rose nat), list rose] nat
    (Term.app (Term.listRec
      (Term.lam (list rose) (call D.isZero [] [call D.length [rose] [v 0]]))
      (Term.lam (list rose) (condT nat (call D.isZero [] [call D.length [rose] [v 0]]) zeroT
        (call D.and [] [Term.app (v 2) (call D.headD [rose] [leafT zeroT, v 0]),
          Term.app (v 1) (call D.tail [rose] [v 0])])))
      (v 1)) (v 0)),
  -- equality of trees: the fold into functions of the second tree, comparing the labels and
  -- the children elementwise
  mkDefn 0 [rose, rose] nat
    (Term.app (Term.roseRec (exp rose nat)
      (Term.lam rose (call D.and []
        [call D.eqN [] [Term.fst (v 1), call D.lab [] [v 0]],
          call D.allZip [] [Term.snd (v 1), call D.children [] [v 0]]])) (v 1)) (v 0))]

/-! The kernel's constants. -/

/-- The fold of trees at the result type {lit}`a`: the rose-tree fold into functions of the
step, each node's value the step at the leaf of its label and the list of its children's
values at the step. -/
def foldT (a : Tree) : Term :=
  let F := exp rose (exp (list a) a)
  Term.lam F (Term.lam rose (Term.app (Term.roseRec (exp F a)
    (Term.lam F (Term.app (Term.app (v 0) (leafT (Term.fst (v 1))))
      (call D.mapApp [F, a] [Term.snd (v 1), v 0]))) (v 0)) (v 1)))

/-- Iteration at the result type {lit}`a`: the fold of the tree's label into functions of the
pair of the step and the start. -/
def iterT (a : Tree) : Term :=
  let P := prod (exp a a) a
  Term.lam (exp a a) (Term.lam a (Term.lam rose (Term.app (Term.natRec
    (Term.lam P (Term.snd (v 0))) (Term.lam P (Term.app (Term.fst (v 0)) (Term.app (v 1) (v 0))))
    (call D.lab [] [v 0])) (Term.pair (v 2) (v 1)))))

/-- The right fold of lists of elements of the type {lit}`a` at the result type {lit}`b`: the
list fold into functions of the pair of the step and the start. -/
def foldrT (a b : Tree) : Term :=
  let P := prod (exp a (exp b b)) b
  Term.lam (exp a (exp b b)) (Term.lam b (Term.lam (list a) (Term.app (Term.listRec
    (Term.lam P (Term.snd (v 0)))
    (Term.lam P (Term.app (Term.app (Term.fst (v 0)) (v 2)) (Term.app (v 1) (v 0)))) (v 0))
    (Term.pair (v 2) (v 1)))))

/-- Case analysis of lists of elements of the type {lit}`a` at the result type {lit}`b`: the
list fold into functions of the pair of the two cases, whose value is the pair of the list and
the case's value, so that a construction's case receives the tail. -/
def lcaseT (a b : Tree) : Term :=
  let C := exp a (exp (list a) b)
  let P := prod b C
  let tl := Term.fst (Term.app (v 1) (v 0))
  Term.lam (list a) (Term.lam b (Term.lam C (Term.snd (Term.app (Term.listRec
    (Term.lam P (Term.pair (nilT a) (Term.fst (v 0))))
    (Term.lam P (Term.pair (consT a (v 2) tl) (Term.app (Term.app (Term.snd (v 0)) (v 2)) tl)))
    (v 2)) (Term.pair (v 1) (v 0))))))

/-- A binary primitive on labels: the leaf of a function of the two labels. -/
def binT (f : Term → Term → Term) : Term :=
  Term.lam rose (Term.lam rose (leafT (f (call D.lab [] [v 1]) (call D.lab [] [v 0]))))

/-- The translation of the kernel's primitive of an index, each a function of the labels and
the children of trees. -/
def primT (k : ℕ) : Option Term :=
  match k with
  | Kernel.Prim.label => some (Term.lam rose (leafT (call D.lab [] [v 0])))
  | Kernel.Prim.arity =>
    some (Term.lam rose (leafT (call D.length [rose] [call D.children [] [v 0]])))
  | Kernel.Prim.child => some (Term.lam rose (Term.lam rose (call D.headD [rose]
      [leafT zeroT, call D.drop [rose] [call D.children [] [v 1], call D.lab [] [v 0]]])))
  | Kernel.Prim.node =>
    some (Term.lam rose (Term.lam (list rose) (nodeT (Term.pair (call D.lab [] [v 1]) (v 0)))))
  | Kernel.Prim.children => some (Term.lam rose (call D.children [] [v 0]))
  | Kernel.Prim.add => some (binT fun m n ↦ call D.add [] [m, n])
  | Kernel.Prim.sub => some (binT fun m n ↦ call D.sub [] [m, n])
  | Kernel.Prim.mul => some (binT fun m n ↦ call D.mul [] [m, n])
  | Kernel.Prim.div => some (binT fun m n ↦ Term.fst (call D.divMod [] [m, n]))
  | Kernel.Prim.mod => some (binT fun m n ↦ Term.snd (call D.divMod [] [m, n]))
  | Kernel.Prim.eq => some (binT fun m n ↦ call D.eqN [] [m, n])
  | Kernel.Prim.lt => some (binT fun m n ↦ call D.ltN [] [m, n])
  | Kernel.Prim.equal =>
    some (Term.lam rose (Term.lam rose (leafT (call D.equal [] [v 1, v 0]))))
  | Kernel.Prim.log2 => some (Term.lam rose (leafT (call D.log2 [] [call D.lab [] [v 0]])))
  | _ => none

/-! The translation of terms. -/

/-- The domain and codomain of a kernel function type. -/
def arrowParts (t : Tree) : Option (Tree × Tree) :=
  if t.label = Kernel.Label.tyArrow then
    match t.children with
    | [a, b] => some (a, b)
    | _ => none
  else none

/-- The factors of a kernel product type. -/
def prodParts (t : Tree) : Option (Tree × Tree) :=
  if t.label = Kernel.Label.tyProd then
    match t.children with
    | [a, b] => some (a, b)
    | _ => none
  else none

/-- The element type of a kernel list type. -/
def listPart (t : Tree) : Option Tree :=
  if t.label = Kernel.Label.tyList then
    match t.children with
    | [a] => some a
    | _ => none
  else none

/-- The translation of a term, as a function of the types of the globals and of the context:
the term's kernel type, as the kernel's checker infers it, and its translation. -/
abbrev Tr : Type := List Tree → List Tree → Option (Tree × Term)

/-- One node of the translation: the node's label, and each child as a tree with its
translation. -/
def termStep (l : ℕ) (cs : List (Tree × Tr)) : Tr := fun gt Γ ↦
  match l, cs with
  | Kernel.Label.var, [(n, _)] => do pure (← Γ[n.label]?, v n.label)
  | Kernel.Label.lam, [(A, _), (_, b)] =>
    if Kernel.Ty.IsTy A then do
      let (B, t) ← b gt (A :: Γ)
      pure (Kernel.tArrow A B, Term.lam (← ty A) t)
    else none
  | Kernel.Label.app, [(_, f), (_, x)] => do
    let (F, tf) ← f gt Γ
    let (X, tx) ← x gt Γ
    let (A, B) ← arrowParts F
    if X = A then pure (B, Term.app tf tx) else none
  | Kernel.Label.unit, [] => some (Kernel.tUnit, Term.star)
  | Kernel.Label.pair, [(_, a), (_, b)] => do
    let (A, ta) ← a gt Γ
    let (B, tb) ← b gt Γ
    pure (Kernel.tProd A B, Term.pair ta tb)
  | Kernel.Label.fst, [(_, p)] => do
    let (P, tp) ← p gt Γ
    pure ((← prodParts P).1, Term.fst tp)
  | Kernel.Label.snd, [(_, p)] => do
    let (P, tp) ← p gt Γ
    pure ((← prodParts P).2, Term.snd tp)
  | Kernel.Label.quote, [(t, _)] => some (Kernel.tT, quoteT t)
  | Kernel.Label.cond, [(_, c), (_, a), (_, b)] => do
    let (C, tc) ← c gt Γ
    let (A, ta) ← a gt Γ
    let (B, tb) ← b gt Γ
    if C = Kernel.tT ∧ B = A then pure (A, condT (← ty A) (call D.lab [] [tc]) ta tb) else none
  | Kernel.Label.fold, [(A, _)] => do pure (Kernel.foldTy A, foldT (← ty A))
  | Kernel.Label.iter, [(A, _)] => do pure (Kernel.iterTy A, iterT (← ty A))
  | Kernel.Label.nil, [(A, _)] => do pure (Kernel.tList A, nilT (← ty A))
  | Kernel.Label.cons, [(_, x), (_, xs)] => do
    let (X, tx) ← x gt Γ
    let (L, txs) ← xs gt Γ
    let A ← listPart L
    if X = A then pure (L, consT (← ty A) tx txs) else none
  | Kernel.Label.foldr, [(A, _), (B, _)] => do
    pure (Kernel.foldrTy A B, foldrT (← ty A) (← ty B))
  | Kernel.Label.prim, [(k, _)] => do pure ((← Kernel.prims[k.label]?).1, ← primT k.label)
  | Kernel.Label.ref, [(n, _)] => do pure (← gt[n.label]?, call (lib.length + n.label) [] [])
  | Kernel.Label.lcase, [(A, _), (B, _)] => do
    pure (Kernel.lcaseTy A B, lcaseT (← ty A) (← ty B))
  | _, _ => none

/-- The translation of a kernel term in a context, with the types of the globals: its kernel
type and its translation. -/
def term (gt Γ : List Tree) (t : Tree) : Option (Tree × Term) := RoseTree.para termStep t gt Γ

/-- The translation of a program's definitions, each closed, over those before it: the
kernel types of the globals and the definitions of the language, which follow the library's. -/
def program (ds : List Tree) : Option (List Tree × List Defn) :=
  ds.foldl (fun acc t ↦ do
    let (gt, defs) ← acc
    let (A, u) ← term gt [] t
    pure (gt ++ [A], defs ++ [mkDefn 0 [] (← ty A) u])) (some ([], []))

/-- The constants of a translated program: the primitive arrows, and the library's definitions
followed by the program's, whose operations follow the signature's. -/
def globals (defs : List Defn) : Globals :=
  ⟨prims, (lib ++ defs).map Definition.language, sig.length⟩

/-- The translation of a theorem of the computational core, with the types of the globals: the
equality of its sides' translations, in the translation of its context. -/
def thm (gt : List Tree) (a : Metalogic.Thm) : Option Internal.Thm := do
  let Γ ← a.ctx.mapM ty
  let (_, l) ← term gt a.ctx a.eqn.lhs
  let (_, r) ← term gt a.ctx a.eqn.rhs
  pure ⟨0, Γ, [], Term.eq l r⟩

end Geb.FreeTopos.Translation

end
