/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.ProveChecked
public import Geb.Prototypes.FreeTopos.Translation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The library's arithmetic at numerals

The definitions of the translation's library ({name}`Geb.FreeTopos.Translation.lib`) that compute
on bitstrings, evaluated at numerals by the arithmetic of the natural numbers the numerals denote,
as Gödel's T evaluates its primitives at literals in one step: the empty bitstring and a bit
before a bitstring, whether a bitstring is empty, the successor, doubling, the predecessor, the
conditional at bitstrings and at comparisons, addition, multiplication, equality, comparison,
less, and the difference of a number at most the first and the truncated difference. A literal
is a numeral, the bitstring of a number's index in the enumeration of {cite}`Oitavem2010`, or a
comparison's result.

The evaluation is a step of the checker with a step of conversion, sound in every model through
its translation into the language's derivations, which rewrite by the definitions' equations at
the numerals' bits ({lit}`lemmas`), one theorem of a development for each case of the arguments'
least significant bits, such as that the successor of a bitstring whose least significant bit is
zero is the bitstring with that bit one. The step reads the equations among the development's
theorems and computes the result by the arithmetic of the natural numbers; the proof by recursion
on the bits that rewriting by the equations reaches that result ({lit}`eval_reaches`) makes the
step sound without the rewriting being performed.

## Main definitions

* {lit}`Val`, {lit}`Val.term` — a literal, and its term.
* {lit}`Sym`, {lit}`Sym.host` — the definitions evaluated, and their values at literals by the
  arithmetic of the natural numbers.
* {lit}`lemmas` — the definitions' equations at the numerals' bits.
* {lit}`eval` — the value of a term built of the definitions over literals.
* {lit}`ready` — the conditions under which the evaluation is a rewriting: the equations among
  the theorems from an index on, and the definitions' and the literals' types.

## Main statements

* {lit}`eval_reaches` — a term that evaluates rewrites to its value's literal by a derivation of
  the language.
* {lit}`checked_of_eval` — the same, where the evaluation is ready.

## References

* {cite}`Oitavem2010`, Remark 2.2, for the enumeration of the bitstrings.

## Tags

internal language, conversion, arithmetic, numeral, bitstring, bijective numeration
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Literals

open PartialHorn (Tree)
open Sorts
open Internal (Term Thm Entry Globals Deriv Checked Definition IsTy typeIn instTerm rootStep
  dRefl dTrans checked_refl checked_trans check_leaf checked_cong_same)
open Translation
open scoped FinEnum

/-! Literals and their numbers. -/

/-- A literal: a bitstring, least significant bit first, or a comparison's result. -/
inductive Val where
  /-- A bitstring. -/
  | bits (w : List Bool)
  /-- A comparison's result. -/
  | ord (o : Ordering)

/-- The numeral of a bitstring: the empty bitstring's definition, and a bit's before the rest. -/
def bitsT (w : List Bool) : Term := w.foldr (fun b t ↦ if b then b1T t else b0T t) bnilT

/-- The term of a comparison's result. -/
def ordT : Ordering → Term
  | .lt => ltO
  | .eq => eqO
  | .gt => gtO

/-- The term of a literal. -/
def Val.term : Val → Term
  | .bits w => bitsT w
  | .ord o => ordT o

/-- The number a bitstring denotes, its index in the enumeration. -/
abbrev val (w : List Bool) : ℕ := Oitavem.rank w

/-- The bitstring of a number. -/
abbrev num (k : ℕ) : List Bool := Oitavem.unrank k

/-- The truth value of a test, as a bitstring: the numeral of one for truth, of zero
otherwise. -/
def truth (b : Bool) : List Bool := if b then [false] else []

/-! The definitions evaluated. -/

/-- A definition of the library evaluated at literals, at the objects it is applied at. -/
inductive Sym where
  /-- The empty bitstring. -/
  | bnil
  /-- The bit zero before a bitstring. -/
  | b0
  /-- The bit one before a bitstring. -/
  | b1
  /-- Whether a bitstring is empty. -/
  | isNil
  /-- The successor. -/
  | succ
  /-- Doubling. -/
  | dbl
  /-- The predecessor. -/
  | pred
  /-- The conditional on a bitstring, at bitstrings. -/
  | condB
  /-- The conditional on a bitstring, at comparisons. -/
  | condO
  /-- Addition. -/
  | add
  /-- Multiplication. -/
  | mul
  /-- Equality. -/
  | eqB
  /-- Comparison. -/
  | cmp
  /-- Less. -/
  | ltB
  /-- The difference of a number at most the first. -/
  | subE
  /-- The truncated difference. -/
  | sub

/-- The definitions evaluated. -/
def Sym.all : List Sym :=
  [.bnil, .b0, .b1, .isNil, .succ, .dbl, .pred, .condB, .condO, .add, .mul, .eqB, .cmp, .ltB,
    .subE, .sub]

/-- The index of a definition in the library. -/
def Sym.index : Sym → ℕ
  | .bnil => D.bnil
  | .b0 => D.b0
  | .b1 => D.b1
  | .isNil => D.isNil
  | .succ => D.succ
  | .dbl => D.dbl
  | .pred => D.pred
  | .condB | .condO => D.cond
  | .add => D.add
  | .mul => D.mul
  | .eqB => D.eqB
  | .cmp => D.cmp
  | .ltB => D.ltB
  | .subE => D.subE
  | .sub => D.sub

/-- The objects a definition is applied at. -/
def Sym.objs : Sym → List Tree
  | .isNil => [bitTy]
  | .condB => [bitsTy]
  | .condO => [ordTy]
  | _ => []

/-- The types of a definition's arguments, the first first. -/
def Sym.args : Sym → List Tree
  | .bnil => []
  | .b0 | .b1 | .isNil | .succ | .dbl | .pred => [bitsTy]
  | .condB => [bitsTy, bitsTy, bitsTy]
  | .condO => [bitsTy, ordTy, ordTy]
  | .add | .mul | .eqB | .cmp | .ltB | .subE | .sub => [bitsTy, bitsTy]

/-- The type of a definition's value. -/
def Sym.res : Sym → Tree
  | .condO | .cmp => ordTy
  | _ => bitsTy

/-- The application of a definition at its objects to arguments, the first first. -/
def Sym.call (s : Sym) (args : List Term) : Term := Translation.call s.index s.objs args

/-- A function of a bitstring, as a partial function of lists of literals. -/
def ofBits₁ (f : List Bool → List Bool) : List Val → Option Val
  | [.bits w] => some (.bits (f w))
  | _ => none

/-- A function of two bitstrings, as a partial function of lists of literals. -/
def ofBits₂ (f : List Bool → List Bool → Option Val) : List Val → Option Val
  | [.bits a, .bits b] => f a b
  | _ => none

/-- The value of a definition at literals, by the arithmetic of the numbers they denote; nothing
at literals of other types, and for the difference of a number greater than the first. -/
def Sym.host : Sym → List Val → Option Val
  | .bnil => fun
    | [] => some (.bits [])
    | _ => none
  | .b0 => ofBits₁ (false :: ·)
  | .b1 => ofBits₁ (true :: ·)
  | .isNil => ofBits₁ fun w ↦ truth w.isEmpty
  | .succ => ofBits₁ fun w ↦ num (val w + 1)
  | .dbl => ofBits₁ fun w ↦ num (2 * val w)
  | .pred => ofBits₁ fun w ↦ num (val w - 1)
  | .condB => fun
    | [.bits c, .bits t, .bits u] => some (.bits (if c.isEmpty then u else t))
    | _ => none
  | .condO => fun
    | [.bits c, .ord t, .ord u] => some (.ord (if c.isEmpty then u else t))
    | _ => none
  | .add => ofBits₂ fun a b ↦ some (.bits (num (val a + val b)))
  | .mul => ofBits₂ fun a b ↦ some (.bits (num (val a * val b)))
  | .eqB => ofBits₂ fun a b ↦ some (.bits (truth (decide (val a = val b))))
  | .cmp => ofBits₂ fun a b ↦ some (.ord (compare (val a) (val b)))
  | .ltB => ofBits₂ fun a b ↦ some (.bits (truth (decide (val a < val b))))
  | .subE => ofBits₂ fun a b ↦
    if val b ≤ val a then some (.bits (num (val a - val b))) else none
  | .sub => ofBits₂ fun a b ↦ some (.bits (num (val a - val b)))

/-! The definitions' equations at the numerals' bits. -/

/-- An equation in a context, as a theorem in no object variables. -/
def eqn (Γ : List Tree) (l r : Term) : Thm := ⟨0, Γ, [], Term.eq l r⟩

/-- The case analysis of a comparison at the type {lit}`c`, abbreviated. -/
abbrev sel (c : Tree) (o l e g : Term) : Term := ifOrd c o l e g

/-- The definitions' equations at the numerals' bits, each a theorem in variables of
bitstrings, the least significant bits of the arguments decided: whether a bitstring is empty;
the successor, doubling and the predecessor; the conditional at bitstrings and at comparisons;
addition and multiplication, by recursion on the second argument; equality and comparison, the
case analysis of a comparison at its three results, and less, by the comparison; and the
difference of a number at most the first, and the truncated difference by less and that
difference. Each is the definition's own recursion at the bits, so that its sides have one normal
form with the rebuildings of the folds. -/
def lemmas : List Thm :=
  let N := bnilT
  let T := trueT
  let x := Term.var 1
  let y := Term.var 0
  let bb := [bitsTy, bitsTy]
  let isNil (a : Term) := Sym.isNil.call [a]
  let un (s : Sym) (a : Term) := s.call [a]
  let bin (s : Sym) (a b : Term) := s.call [a, b]
  [eqn [] (isNil N) T,
    eqn [bitsTy] (isNil (b0T y)) N,
    eqn [bitsTy] (isNil (b1T y)) N,
    eqn [] (un .succ N) (b0T N),
    eqn [bitsTy] (un .succ (b0T y)) (b1T y),
    eqn [bitsTy] (un .succ (b1T y)) (b0T (un .succ y)),
    eqn [] (un .dbl N) N,
    eqn [bitsTy] (un .dbl (b0T y)) (b1T (un .dbl y)),
    eqn [bitsTy] (un .dbl (b1T y)) (b1T (b0T y)),
    eqn [] (un .pred N) N,
    eqn [bitsTy] (un .pred (b0T y)) (Sym.condB.call [y, b1T (un .pred y), N]),
    eqn [bitsTy] (un .pred (b1T y)) (b0T y),
    -- the conditional at bitstrings and at comparisons
    eqn bb (Sym.condB.call [N, x, y]) y,
    eqn [bitsTy, bitsTy, bitsTy] (Sym.condB.call [b0T (Term.var 2), x, y]) x,
    eqn [bitsTy, bitsTy, bitsTy] (Sym.condB.call [b1T (Term.var 2), x, y]) x,
    eqn [ordTy, ordTy] (Sym.condO.call [N, x, y]) y,
    eqn [ordTy, ordTy, bitsTy] (Sym.condO.call [b0T (Term.var 2), x, y]) x,
    eqn [ordTy, ordTy, bitsTy] (Sym.condO.call [b1T (Term.var 2), x, y]) x,
    -- addition and multiplication
    eqn [bitsTy] (bin .add y N) y,
    eqn [bitsTy] (bin .add N (b0T y)) (b0T y),
    eqn [bitsTy] (bin .add N (b1T y)) (b1T y),
    eqn bb (bin .add (b0T x) (b0T y)) (b1T (bin .add x y)),
    eqn bb (bin .add (b0T x) (b1T y)) (b0T (un .succ (bin .add x y))),
    eqn bb (bin .add (b1T x) (b0T y)) (b0T (un .succ (bin .add x y))),
    eqn bb (bin .add (b1T x) (b1T y)) (b1T (un .succ (bin .add x y))),
    eqn [bitsTy] (bin .mul y N) N,
    eqn bb (bin .mul x (b0T y)) (bin .add (un .dbl (bin .mul x y)) x),
    eqn bb (bin .mul x (b1T y)) (bin .add (un .dbl (bin .mul x y)) (un .dbl x)),
    -- equality
    eqn [bitsTy] (bin .eqB y N) (isNil y),
    eqn [bitsTy] (bin .eqB N (b0T y)) N,
    eqn [bitsTy] (bin .eqB N (b1T y)) N,
    eqn bb (bin .eqB (b0T x) (b0T y)) (bin .eqB x y),
    eqn bb (bin .eqB (b0T x) (b1T y)) N,
    eqn bb (bin .eqB (b1T x) (b0T y)) N,
    eqn bb (bin .eqB (b1T x) (b1T y)) (bin .eqB x y),
    -- comparison, and the case analysis of a comparison
    eqn [bitsTy] (bin .cmp y N) (Sym.condO.call [y, gtO, eqO]),
    eqn [bitsTy] (bin .cmp N (b0T y)) ltO,
    eqn [bitsTy] (bin .cmp N (b1T y)) ltO,
    eqn bb (bin .cmp (b0T x) (b0T y)) (sel ordTy (bin .cmp x y) ltO eqO gtO),
    eqn bb (bin .cmp (b0T x) (b1T y)) (sel ordTy (bin .cmp x y) ltO ltO gtO),
    eqn bb (bin .cmp (b1T x) (b0T y)) (sel ordTy (bin .cmp x y) ltO gtO gtO),
    eqn bb (bin .cmp (b1T x) (b1T y)) (sel ordTy (bin .cmp x y) ltO eqO gtO),
    eqn [ordTy, ordTy, ordTy] (sel ordTy ltO (Term.var 2) x y) (Term.var 2),
    eqn [ordTy, ordTy, ordTy] (sel ordTy eqO (Term.var 2) x y) x,
    eqn [ordTy, ordTy, ordTy] (sel ordTy gtO (Term.var 2) x y) y,
    eqn [bitsTy, bitsTy, bitsTy] (sel bitsTy ltO (Term.var 2) x y) (Term.var 2),
    eqn [bitsTy, bitsTy, bitsTy] (sel bitsTy eqO (Term.var 2) x y) x,
    eqn [bitsTy, bitsTy, bitsTy] (sel bitsTy gtO (Term.var 2) x y) y,
    eqn bb (bin .ltB x y) (sel bitsTy (bin .cmp x y) T N N),
    -- the differences
    eqn [bitsTy] (bin .subE y N) y,
    eqn [bitsTy] (bin .subE N (b0T y)) N,
    eqn [bitsTy] (bin .subE N (b1T y)) N,
    eqn bb (bin .subE (b0T x) (b0T y)) (un .dbl (bin .subE x y)),
    eqn bb (bin .subE (b0T x) (b1T y)) (b0T (un .pred (bin .subE x y))),
    eqn bb (bin .subE (b1T x) (b0T y)) (b0T (bin .subE x y)),
    eqn bb (bin .subE (b1T x) (b1T y)) (un .dbl (bin .subE x y)),
    eqn bb (bin .sub x y) (Sym.condB.call [bin .ltB x y, N, bin .subE x y])]

/-! The evaluation. -/

/-- The definition a label applies, where it is one of those evaluated. -/
def Sym.ofLabel : Internal.Label → Option Sym
  | .defn k θ => Sym.all.find? fun s ↦ decide (s.index = k ∧ s.objs = θ)
  | _ => none

/-- The comparison's result a term is, where it is one. -/
def ordOf (t : Term) : Option Ordering :=
  [Ordering.lt, .eq, .gt].find? fun o ↦ decide (ordT o = t)

/-- One step of the evaluation, at a node of a label, from its children with their values: a
comparison's result, or a definition evaluated at its arguments' values, the children being
the arguments last first. -/
def evalStep (l : Internal.Label) (cs : List (Term × Option Val)) : Option Val :=
  match ordOf (RoseTree.node l (cs.map Prod.fst)) with
  | some o => some (.ord o)
  | none => do
    let s ← Sym.ofLabel l
    s.host (← (cs.map Prod.snd).reverse.mapM id)

/-- The value of a term built of the definitions evaluated over literals. -/
def eval : Term → Option Val := RoseTree.para evalStep

/-- Whether a definition of the constants is the one evaluated, in its objects, its arguments'
types and its value's type. -/
def sigOk (G : Globals) (n : ℕ) (s : Sym) : Bool :=
  match (G.defs[s.index]?).bind Definition.language? with
  | some d => decide (d.arity = s.objs.length) && s.objs.all (IsTy G n) &&
      decide (d.params.map (PartialHorn.subst s.objs) = s.args.reverse) &&
      decide (PartialHorn.subst s.objs d.type = s.res)
  | none => false

/-- Whether the theorems of the environment from an index on are the equations, in their
order. -/
def lemmasIn (E : Array Entry) (j : ℕ) : Bool :=
  lemmas.zipIdx.all fun (a, i) ↦ match (E[j + i]?).bind Entry.language? with
    | some b => decide (b.arity = a.arity ∧ b.ctx = a.ctx ∧ b.hyps = a.hyps ∧ b.concl = a.concl)
    | none => false

/-- The conditions under which the evaluation is a rewriting in a context: the equations among
the theorems from the index {lit}`j` on, the definitions evaluated those of the constants, and
the comparisons' results of their type. -/
def ready (G : Globals) (E : Array Entry) (n : ℕ) (Γ : List Tree) (j : ℕ) : Bool :=
  lemmasIn E j && Sym.all.all (sigOk G n) &&
    [Ordering.lt, .eq, .gt].all fun o ↦ decide (typeIn G n Γ (ordT o) = some ordTy)

/-! Rewriting by derivations. -/

/-- A term rewrites to another in a context under hypotheses, by a derivation the checker
accepts. -/
def Reaches (G : Globals) (E : Array Entry) (n : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Prop :=
  ∃ d : Deriv × Bool, Checked G E n Γ Φ t (u, d)

section Reaching

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}

/-- A term rewrites to itself. -/
theorem reaches_refl (t : Term) : Reaches G E n Γ Φ t t := ⟨dRefl, checked_refl Γ Φ t⟩

/-- Rewritings compose. -/
theorem Reaches.trans {t u v : Term} (h₁ : Reaches G E n Γ Φ t u)
    (h₂ : Reaches G E n Γ Φ u v) : Reaches G E n Γ Φ t v :=
  let ⟨_, h₁⟩ := h₁
  let ⟨_, h₂⟩ := h₂
  ⟨_, checked_trans h₁ h₂⟩

/-- A rule rewriting a term at its root rewrites it. -/
theorem reaches_root {l : Internal.Rule} {t u : Term} (h : rootStep G E n Γ Φ l t = some u) :
    Reaches G E n Γ Φ t u :=
  let ⟨hc, hr⟩ := check_leaf h
  ⟨(RoseTree.node l [], true), hc, fun h ↦ (nomatch h), fun _ ↦ hr⟩

/-- A node whose children are all in its context rewrites by rewriting its children. -/
theorem reaches_node {l : Internal.Label} (hl : ∀ i, Internal.sameCtx l i = true)
    {ts us : List Term} (h : List.Forall₂ (Reaches G E n Γ Φ) ts us) :
    Reaches G E n Γ Φ (RoseTree.node l ts) (RoseTree.node l us) := by
  obtain ⟨rs, hu, hl', hc⟩ : ∃ rs : List (Term × Deriv × Bool), rs.map Prod.fst = us ∧
      rs.length = ts.length ∧
      ∀ (i : ℕ) (h₁ : i < rs.length) (h₂ : i < ts.length), Checked G E n Γ Φ ts[i] rs[i] :=
    List.Forall₂.rec (motive := fun ts us _ ↦ ∃ rs : List (Term × Deriv × Bool),
        rs.map Prod.fst = us ∧ rs.length = ts.length ∧
        ∀ (i : ℕ) (h₁ : i < rs.length) (h₂ : i < ts.length), Checked G E n Γ Φ ts[i] rs[i])
      ⟨[], rfl, rfl, fun _ h ↦ (Nat.not_lt_zero _ h).elim⟩
      (fun {t u ts us} htu _ ih ↦
        let ⟨d, hd⟩ := htu
        let ⟨rs, hu, hl, hc⟩ := ih
        ⟨(u, d) :: rs, by rw [List.map_cons, hu], by rw [List.length_cons, hl,
          List.length_cons], fun i ↦ match i with
          | 0 => fun _ _ ↦ hd
          | i + 1 => fun h₁ h₂ ↦ hc i (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)⟩)
      h
  refine ⟨_, hu ▸ checked_cong_same hl' (fun i _ hi ↦ ?_) hc⟩
  rw [hl i] at hi
  exact (Bool.noConfusion hi)

/-! Types. -/

/-- A list whose elements have values under a partial function with second components given
is mapped to a list with those second components. -/
theorem exists_mapM_snd {α β γ : Type} {f : α → Option (β × γ)} :
    ∀ (l : List α) (ps : List γ), l.map (fun a ↦ (f a).map Prod.snd) = ps.map some →
      ∃ rs, l.mapM f = some rs ∧ rs.map Prod.snd = ps :=
  fun l ↦ l.rec (fun ps h ↦ match ps, h with
      | [], _ => ⟨[], rfl, rfl⟩)
    fun a l ih ps h ↦ match ps, h with
      | p :: ps, h => by
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨⟨b, c⟩, hb, rfl⟩ := Option.map_eq_some_iff.mp h.1
        obtain ⟨rs, hrs, hps⟩ := ih ps h.2
        exact ⟨(b, c) :: rs, by simp [List.mapM_cons, hb, hrs], by simp [hps]⟩

/-- The type of a definition's application at objects to arguments of its parameters' types. -/
theorem typeIn_defn {k : ℕ} {θ : List Tree} {cs : List Term} {d : Internal.Defn}
    (hd : (G.defs[k]?).bind Definition.language? = some d) (ha : θ.length = d.arity)
    (hθ : θ.all (IsTy G n) = true)
    (hcs : cs.map (typeIn G n Γ) = (d.params.map (PartialHorn.subst θ)).map some) :
    typeIn G n Γ (Term.defn k θ cs) = some (PartialHorn.subst θ d.type) := by
  obtain ⟨rs, hrs, hps⟩ := exists_mapM_snd (f := fun c ↦ Internal.compile G n c
    (Internal.ctxObj Γ) (Internal.stdEnv Γ)) cs _ hcs
  simp only [typeIn, Term.defn, Internal.compile_node, Internal.compileStep, hd,
    Option.bind_eq_bind, Option.bind_some, List.mapM_map, Function.comp_def]
  rw [hrs]
  simp [ha, hθ, hps]

/-- The type of a definition's application to arguments of its arguments' types. -/
theorem typeIn_call {s : Sym} (hs : sigOk G n s = true) {args : List Term}
    (ha : args.map (typeIn G n Γ) = s.args.map some) :
    typeIn G n Γ (s.call args) = some s.res := by
  unfold sigOk at hs
  split at hs
  · rename_i d hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hs
    rw [Sym.call, call, typeIn_defn hd h₁.symm h₂ (by rw [h₃, List.map_reverse, ha,
      List.map_reverse]), h₄]
  · cases hs

variable (hS : ∀ s ∈ Sym.all, sigOk G n s = true)
include hS

/-- A numeral is of the bitstrings' type. -/
theorem typeIn_bitsT (w : List Bool) : typeIn G n Γ (bitsT w) = some bitsTy :=
  w.rec (typeIn_call (hS .bnil (by simp [Sym.all])) rfl) fun b w ih ↦ by
    cases b
    · exact typeIn_call (s := .b0) (hS .b0 (by simp [Sym.all])) (congrArg (· :: []) ih)
    · exact typeIn_call (s := .b1) (hS .b1 (by simp [Sym.all])) (congrArg (· :: []) ih)

end Reaching

/-! The equations as rewritings. -/

/-- The equations are the theorems of the environment from an index on. -/
def InEnv (E : Array Entry) (j : ℕ) : Prop :=
  ∀ (i : ℕ) (a : Thm), lemmas[i]? = some a → (E[j + i]?).bind Entry.language? = some a

/-- The test that the equations are the theorems from an index on decides it. -/
theorem inEnv_of_lemmasIn {E : Array Entry} {j : ℕ} (h : lemmasIn E j = true) : InEnv E j := by
  intro i a ha
  have hm := List.all_eq_true.mp h (a, i) (List.mk_mem_zipIdx_iff_getElem?.mpr ha)
  simp only at hm
  split at hm
  · rename_i b hb
    obtain ⟨h₁, h₂, h₃, h₄⟩ := of_decide_eq_true hm
    rw [hb]
    obtain ⟨⟩ := a
    obtain ⟨⟩ := b
    simp only at h₁ h₂ h₃ h₄
    subst h₁ h₂ h₃ h₄
    rfl
  · cases hm

section Equations

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}

/-- Terms of a context's types make each test of the instantiation hold. -/
theorem all_typeIn_of_forall₂ {σ : List Term} {Δ : List Tree}
    (h : List.Forall₂ (fun u A ↦ typeIn G n Γ u = some A) σ Δ) :
    (σ.zip Δ).all (fun (u, A) ↦ decide (typeIn G n Γ u = some A)) = true :=
  List.Forall₂.rec (motive := fun σ Δ _ ↦
      (σ.zip Δ).all (fun (u, A) ↦ decide (typeIn G n Γ u = some A)) = true)
    rfl (fun {u A _ _} hu _ ih ↦ by simp [List.zip_cons_cons, hu, ih]) h

/-- An equation among the theorems, instantiated at terms of its context's types, rewrites its
left side's instance to its right side's. -/
theorem reaches_lemma {j : ℕ} (hE : InEnv E j) {i : ℕ} {Δ : List Tree} {l r : Term}
    (ha : lemmas[i]? = some (eqn Δ l r)) {σ : List Term}
    (hty : List.Forall₂ (fun u A ↦ typeIn G n Γ u = some A) σ Δ) {t u : Term}
    (ht : Term.subst l (Term.substList σ) = t) (hu : Term.subst r (Term.substList σ) = u) :
    Reaches G E n Γ Φ t u := by
  refine reaches_root (l := .thm (j + i) [] σ false) ?_
  have hall := all_typeIn_of_forall₂ hty
  have hinst (s : Term) : instTerm [] σ s = Term.subst s (Term.substList σ) := by
    rw [instTerm, Term.osubst_nil]
  have hΔ : Δ.map (PartialHorn.subst []) = Δ := by
    rw [show PartialHorn.subst [] = id from funext PartialHorn.subst_nil, List.map_id]
  have hok : Internal.instOk G n Γ (eqn Δ l r) [] σ = true := by
    simp only [Internal.instOk, eqn, List.length_nil, List.all_nil, Bool.and_true, hΔ,
      hty.length_eq, decide_true, Bool.true_and]
    exact hall
  simp only [rootStep, hE i _ ha, Option.bind_eq_bind, Option.bind_some, Internal.eqParts, eqn,
    Term.eq, RoseTree.label_node, RoseTree.children_node, Bool.false_eq_true, ite_false, hinst,
    ht, hu, ite_true]
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hok, trivial⟩)

/-- A definition's application rewrites by rewriting its arguments. -/
theorem reaches_call (s : Sym) {as bs : List Term} (h : List.Forall₂ (Reaches G E n Γ Φ) as bs) :
    Reaches G E n Γ Φ (s.call as) (s.call bs) :=
  reaches_node (fun _ ↦ rfl) (List.forall₂_reverse_iff.mpr h)

/-- A definition's application to one argument rewrites by rewriting it. -/
theorem reaches_call₁ (s : Sym) {a b : Term} (h : Reaches G E n Γ Φ a b) :
    Reaches G E n Γ Φ (s.call [a]) (s.call [b]) :=
  reaches_call s (.cons h .nil)

/-- A case analysis of a comparison rewrites by rewriting the comparison. -/
theorem reaches_sel (c : Tree) {o o' : Term} (l e g : Term) (h : Reaches G E n Γ Φ o o') :
    Reaches G E n Γ Φ (sel c o l e g) (sel c o' l e g) :=
  reaches_node (fun _ ↦ rfl) (.cons (reaches_refl _) (.cons h .nil))

end Equations

/-! The numbers of numerals. -/

/-- A bit before a bitstring doubles its number and adds one more than the bit. -/
theorem val_cons (b : Bool) (w : List Bool) : val (b :: w) = 2 * val w + b.toNat + 1 :=
  Oitavem.rank_cons b w

/-- The bitstring of a number is the one whose number it is. -/
theorem num_eq {w : List Bool} {k : ℕ} (h : val w = k) : num k = w :=
  h ▸ Oitavem.unrank_rank w

/-- The number of a number's bitstring is the number. -/
theorem val_num (k : ℕ) : val (num k) = k := Oitavem.rank_unrank k

/-- The empty bitstring denotes zero. -/
theorem val_nil : val [] = 0 := rfl

/-- Closes an equation or inequation of the numbers of numerals by their bits. -/
local macro "bits_arith" : tactic =>
  `(tactic| ((try simp only [val_cons, val_num, val_nil, Bool.toNat_false, Bool.toNat_true,
    Nat.add_zero, Nat.zero_add] at *) <;> omega))

/-- The value at a comparison's result of the case analysis of comparisons. -/
def pick {α : Type} : Ordering → α → α → α → α
  | .lt, l, _, _ => l
  | .eq, _, e, _ => e
  | .gt, _, _, g => g

/-- Each definition evaluated is among them. -/
theorem Sym.mem_all (s : Sym) : s ∈ Sym.all := by
  cases s <;> simp only [Sym.all, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false,
    or_true]

/-- A rewriting to a term rewrites to any term equal to it. -/
theorem Reaches.of_eq {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}
    {t u u' : Term} (h : Reaches G E n Γ Φ t u) (e : u = u') : Reaches G E n Γ Φ t u' :=
  e ▸ h

/-- A definition's application to arguments of its arguments' types is of its value's type. -/
theorem typeIn_call' {G : Globals} {n : ℕ} {Γ : List Tree}
    (hS : ∀ s ∈ Sym.all, sigOk G n s = true) (s : Sym) {args : List Term}
    (ha : List.Forall₂ (fun u A ↦ typeIn G n Γ u = some A) args s.args) :
    typeIn G n Γ (s.call args) = some s.res :=
  typeIn_call (hS s (Sym.mem_all s)) (List.Forall₂.rec (motive := fun as As _ ↦
      as.map (typeIn G n Γ) = As.map some) rfl
    (fun hu _ ih ↦ by rw [List.map_cons, List.map_cons, hu, ih]) ha)

/-! The numerals rewrite as the definitions compute. -/

section Arithmetic

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term} {j : ℕ}
  (hE : InEnv E j) (hS : ∀ s ∈ Sym.all, sigOk G n s = true)
  (hO : ∀ o, typeIn G n Γ (ordT o) = some ordTy)
include hE

/-- The case analysis of a comparison's result at comparisons. -/
theorem reaches_selO (o : Ordering) {l e g : Term} (hl : typeIn G n Γ l = some ordTy)
    (he : typeIn G n Γ e = some ordTy) (hg : typeIn G n Γ g = some ordTy) :
    Reaches G E n Γ Φ (sel ordTy (ordT o) l e g) (pick o l e g) := by
  cases o
  · exact reaches_lemma hE (i := 42) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl
  · exact reaches_lemma hE (i := 43) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl
  · exact reaches_lemma hE (i := 44) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl

/-- The case analysis of a comparison's result at bitstrings. -/
theorem reaches_selB (o : Ordering) {l e g : Term} (hl : typeIn G n Γ l = some bitsTy)
    (he : typeIn G n Γ e = some bitsTy) (hg : typeIn G n Γ g = some bitsTy) :
    Reaches G E n Γ Φ (sel bitsTy (ordT o) l e g) (pick o l e g) := by
  cases o
  · exact reaches_lemma hE (i := 45) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl
  · exact reaches_lemma hE (i := 46) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl
  · exact reaches_lemma hE (i := 47) rfl (.cons hg (.cons he (.cons hl .nil))) rfl rfl

include hS

/-- An equation in one variable of bitstrings, at a numeral. -/
theorem reaches_lemma₁ {i : ℕ} {l r : Term} (ha : lemmas[i]? = some (eqn [bitsTy] l r))
    (y : List Bool) {t u : Term} (ht : Term.subst l (Term.substList [bitsT y]) = t)
    (hu : Term.subst r (Term.substList [bitsT y]) = u) : Reaches G E n Γ Φ t u :=
  reaches_lemma hE ha (.cons (typeIn_bitsT hS y) .nil) ht hu

/-- An equation in two variables of bitstrings, at numerals. -/
theorem reaches_lemma₂ {i : ℕ} {l r : Term} (ha : lemmas[i]? = some (eqn [bitsTy, bitsTy] l r))
    (x y : List Bool) {t u : Term} (ht : Term.subst l (Term.substList [bitsT y, bitsT x]) = t)
    (hu : Term.subst r (Term.substList [bitsT y, bitsT x]) = u) : Reaches G E n Γ Φ t u :=
  reaches_lemma hE ha (.cons (typeIn_bitsT hS y) (.cons (typeIn_bitsT hS x) .nil)) ht hu

/-- Whether a bitstring is empty. -/
theorem reaches_isNil (w : List Bool) :
    Reaches G E n Γ Φ (Sym.isNil.call [bitsT w]) (bitsT (truth w.isEmpty)) := by
  rcases w with _ | ⟨_ | _, w⟩
  · exact reaches_lemma hE (i := 0) rfl .nil rfl rfl
  · exact reaches_lemma₁ hE hS (i := 1) rfl w rfl rfl
  · exact reaches_lemma₁ hE hS (i := 2) rfl w rfl rfl

/-- The successor. -/
theorem reaches_succ (w : List Bool) :
    Reaches G E n Γ Φ (Sym.succ.call [bitsT w]) (bitsT (num (val w + 1))) :=
  w.rec ((reaches_lemma hE (i := 3) rfl .nil rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := [false]) (by bits_arith))).symm)
    fun b w ih ↦ by
      cases b
      · exact (reaches_lemma₁ hE hS (i := 4) rfl w rfl rfl).of_eq
          (congrArg bitsT (num_eq (w := true :: w) (by bits_arith))).symm
      · exact ((reaches_lemma₁ hE hS (i := 5) rfl w rfl rfl).trans
          (reaches_call₁ .b0 ih)).of_eq (congrArg bitsT (num_eq (w := false :: num (val w + 1))
            (by bits_arith))).symm

/-- Doubling. -/
theorem reaches_dbl (w : List Bool) :
    Reaches G E n Γ Φ (Sym.dbl.call [bitsT w]) (bitsT (num (2 * val w))) :=
  w.rec ((reaches_lemma hE (i := 6) rfl .nil rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := []) (by bits_arith))).symm)
    fun b w ih ↦ by
      cases b
      · exact ((reaches_lemma₁ hE hS (i := 7) rfl w rfl rfl).trans
          (reaches_call₁ .b1 ih)).of_eq (congrArg bitsT (num_eq (w := true :: num (2 * val w))
            (by bits_arith))).symm
      · exact (reaches_lemma₁ hE hS (i := 8) rfl w rfl rfl).of_eq
          (congrArg bitsT (num_eq (w := true :: false :: w) (by bits_arith))).symm

/-- The conditional at bitstrings, its branches of the bitstrings' type. -/
theorem reaches_condB (c : List Bool) {t u : Term} (ht : typeIn G n Γ t = some bitsTy)
    (hu : typeIn G n Γ u = some bitsTy) :
    Reaches G E n Γ Φ (Sym.condB.call [bitsT c, t, u]) (if c.isEmpty then u else t) := by
  rcases c with _ | ⟨_ | _, c⟩
  · exact reaches_lemma hE (i := 12) rfl (.cons hu (.cons ht .nil)) rfl rfl
  · exact reaches_lemma hE (i := 13) rfl
      (.cons hu (.cons ht (.cons (typeIn_bitsT hS c) .nil))) rfl rfl
  · exact reaches_lemma hE (i := 14) rfl
      (.cons hu (.cons ht (.cons (typeIn_bitsT hS c) .nil))) rfl rfl

/-- The predecessor. -/
theorem reaches_pred (w : List Bool) :
    Reaches G E n Γ Φ (Sym.pred.call [bitsT w]) (bitsT (num (val w - 1))) :=
  w.rec ((reaches_lemma hE (i := 9) rfl .nil rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := []) (by bits_arith))).symm)
    fun b w ih ↦ by
      cases b
      · have hp := typeIn_call' (Γ := Γ) hS .b1 (.cons (typeIn_call' hS .pred
          (.cons (typeIn_bitsT hS w) .nil)) .nil)
        refine (reaches_lemma₁ hE hS (i := 10) rfl w rfl rfl).trans ?_
        rcases w with _ | ⟨b, w'⟩
        · exact (reaches_condB hE hS [] hp (typeIn_bitsT hS [])).of_eq
            (congrArg bitsT (num_eq (w := []) (by bits_arith))).symm
        · exact ((reaches_condB hE hS (b :: w') hp (typeIn_bitsT hS [])).trans
            (reaches_call₁ .b1 ih)).of_eq (congrArg bitsT (num_eq
              (w := true :: num (val (b :: w') - 1)) (by bits_arith))).symm
      · exact (reaches_lemma₁ hE hS (i := 11) rfl w rfl rfl).of_eq
          (congrArg bitsT (num_eq (w := false :: w) (by bits_arith))).symm

/-- Addition, by recursion on the second summand. -/
theorem reaches_add (b : List Bool) : ∀ a : List Bool,
    Reaches G E n Γ Φ (Sym.add.call [bitsT a, bitsT b]) (bitsT (num (val a + val b))) :=
  b.rec (fun a ↦ (reaches_lemma₁ hE hS (i := 18) rfl a rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := a) (by bits_arith))).symm)
    fun d y ih a ↦ by
      rcases a with _ | ⟨e, x⟩
      · cases d
        · exact (reaches_lemma₁ hE hS (i := 19) rfl y rfl rfl).of_eq
            (congrArg bitsT (num_eq (w := false :: y) (by bits_arith))).symm
        · exact (reaches_lemma₁ hE hS (i := 20) rfl y rfl rfl).of_eq
            (congrArg bitsT (num_eq (w := true :: y) (by bits_arith))).symm
      · have hc (s : Sym) := reaches_call₁ (Φ := Φ) s ((reaches_call₁ .succ (ih x)).trans
          (reaches_succ hE hS _))
        cases e <;> cases d
        · exact ((reaches_lemma₂ hE hS (i := 21) rfl x y rfl rfl).trans
            (reaches_call₁ .b1 (ih x))).of_eq
            (congrArg bitsT (num_eq (w := true :: num (val x + val y)) (by bits_arith))).symm
        · exact ((reaches_lemma₂ hE hS (i := 22) rfl x y rfl rfl).trans (hc .b0)).of_eq
            (congrArg bitsT (num_eq (w := false :: num (val (num (val x + val y)) + 1))
              (by bits_arith))).symm
        · exact ((reaches_lemma₂ hE hS (i := 23) rfl x y rfl rfl).trans (hc .b0)).of_eq
            (congrArg bitsT (num_eq (w := false :: num (val (num (val x + val y)) + 1))
              (by bits_arith))).symm
        · exact ((reaches_lemma₂ hE hS (i := 24) rfl x y rfl rfl).trans (hc .b1)).of_eq
            (congrArg bitsT (num_eq (w := true :: num (val (num (val x + val y)) + 1))
              (by bits_arith))).symm

/-- Multiplication, by recursion on the second factor. -/
theorem reaches_mul (a b : List Bool) :
    Reaches G E n Γ Φ (Sym.mul.call [bitsT a, bitsT b]) (bitsT (num (val a * val b))) :=
  b.rec ((reaches_lemma₁ hE hS (i := 25) rfl a rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := []) (by simp only [val_nil, Nat.mul_zero]))).symm)
    fun d y ih ↦ by
      have hm := (reaches_call₁ (Φ := Φ) .dbl ih).trans (reaches_dbl hE hS _)
      have hy : val a * (2 * val y) = 2 * (val a * val y) := Nat.mul_left_comm _ _ _
      cases d
      · exact (((reaches_lemma₂ hE hS (i := 26) rfl a y rfl rfl).trans
          (reaches_call .add (.cons hm (.cons (reaches_refl _) .nil)))).trans
          (reaches_add hE hS _ _)).of_eq (congrArg (fun k ↦ bitsT (num k)) (by
            simp only [val_cons, val_num, Bool.toNat_false, Nat.add_zero, Nat.mul_add,
              Nat.mul_one, hy]))
      · exact (((reaches_lemma₂ hE hS (i := 27) rfl a y rfl rfl).trans
          (reaches_call .add (.cons hm (.cons (reaches_dbl hE hS a) .nil)))).trans
          (reaches_add hE hS _ _)).of_eq (congrArg (fun k ↦ bitsT (num k)) (by
            simp only [val_cons, val_num, Bool.toNat_true, Nat.mul_add, Nat.mul_one, hy]
            omega))

/-- Equality, by recursion on the second number. -/
theorem reaches_eqB (b : List Bool) : ∀ a : List Bool,
    Reaches G E n Γ Φ (Sym.eqB.call [bitsT a, bitsT b])
      (bitsT (truth (decide (val a = val b)))) :=
  b.rec (fun a ↦ ((reaches_lemma₁ hE hS (i := 28) rfl a rfl rfl).trans
      (reaches_isNil hE hS a)).of_eq (by
        rcases a with _ | ⟨e, x⟩
        · rfl
        · rw [decide_eq_false (by bits_arith)]
          rfl))
    fun d y ih a ↦ by
      rcases a with _ | ⟨e, x⟩
      · rw [decide_eq_false (by bits_arith)]
        cases d
        · exact reaches_lemma₁ hE hS (i := 29) rfl y rfl rfl
        · exact reaches_lemma₁ hE hS (i := 30) rfl y rfl rfl
      · cases e <;> cases d
        · rw [decide_eq_decide.mpr (show val (false :: x) = val (false :: y) ↔ val x = val y by
            constructor <;> intro h <;> bits_arith)]
          exact (reaches_lemma₂ hE hS (i := 31) rfl x y rfl rfl).trans (ih x)
        · rw [decide_eq_false (by bits_arith)]
          exact reaches_lemma₂ hE hS (i := 32) rfl x y rfl rfl
        · rw [decide_eq_false (by bits_arith)]
          exact reaches_lemma₂ hE hS (i := 33) rfl x y rfl rfl
        · rw [decide_eq_decide.mpr (show val (true :: x) = val (true :: y) ↔ val x = val y by
            constructor <;> intro h <;> bits_arith)]
          exact (reaches_lemma₂ hE hS (i := 34) rfl x y rfl rfl).trans (ih x)

/-- The difference of a number at most the first, by recursion on it. -/
theorem reaches_subE (b : List Bool) : ∀ a : List Bool, val b ≤ val a →
    Reaches G E n Γ Φ (Sym.subE.call [bitsT a, bitsT b]) (bitsT (num (val a - val b))) :=
  b.rec (fun a _ ↦ (reaches_lemma₁ hE hS (i := 49) rfl a rfl rfl).of_eq
      (congrArg bitsT (num_eq (w := a) (by bits_arith))).symm)
    fun d y ih a h ↦ by
      rcases a with _ | ⟨e, x⟩
      · exact False.elim (by bits_arith)
      · have hxy : val y ≤ val x := by cases e <;> cases d <;> bits_arith
        have hs := ih x hxy
        cases e <;> cases d
        · exact (((reaches_lemma₂ hE hS (i := 52) rfl x y rfl rfl).trans
            (reaches_call₁ .dbl hs)).trans (reaches_dbl hE hS _)).of_eq
            (congrArg (fun k ↦ bitsT (num k)) (by bits_arith))
        · exact (((reaches_lemma₂ hE hS (i := 53) rfl x y rfl rfl).trans
            (reaches_call₁ .b0 ((reaches_call₁ .pred hs).trans (reaches_pred hE hS _)))).of_eq
            (congrArg bitsT (num_eq (w := false :: num (val (num (val x - val y)) - 1))
              (by bits_arith))).symm)
        · exact ((reaches_lemma₂ hE hS (i := 54) rfl x y rfl rfl).trans
            (reaches_call₁ .b0 hs)).of_eq
            (congrArg bitsT (num_eq (w := false :: num (val x - val y)) (by bits_arith))).symm
        · exact (((reaches_lemma₂ hE hS (i := 55) rfl x y rfl rfl).trans
            (reaches_call₁ .dbl hs)).trans (reaches_dbl hE hS _)).of_eq
            (congrArg (fun k ↦ bitsT (num k)) (by bits_arith))

omit hE hS in
/-- The comparison of numerals whose least significant bits are given: that of the rests, and
where the rests are equal, of the bits. -/
theorem compare_cons (e d : Bool) (x y : List Bool) :
    compare (val (e :: x)) (val (d :: y)) =
      pick (compare (val x) (val y)) .lt (compare e.toNat d.toNat) .gt := by
  rcases h : compare (val x) (val y) with _ | _ | _
  · have := Nat.compare_eq_lt.mp h
    exact Nat.compare_eq_lt.mpr (by cases e <;> cases d <;> bits_arith)
  · have := Nat.compare_eq_eq.mp h
    cases e <;> cases d
    · exact Nat.compare_eq_eq.mpr (by bits_arith)
    · exact Nat.compare_eq_lt.mpr (by bits_arith)
    · exact Nat.compare_eq_gt.mpr (by bits_arith)
    · exact Nat.compare_eq_eq.mpr (by bits_arith)
  · have := Nat.compare_eq_gt.mp h
    exact Nat.compare_eq_gt.mpr (by cases e <;> cases d <;> bits_arith)

variable (hO : ∀ o, typeIn G n Γ (ordT o) = some ordTy)
include hO

/-- The conditional at comparisons. -/
theorem reaches_condO (c : List Bool) (t u : Ordering) :
    Reaches G E n Γ Φ (Sym.condO.call [bitsT c, ordT t, ordT u])
      (ordT (if c.isEmpty then u else t)) := by
  rcases c with _ | ⟨_ | _, c⟩
  · exact reaches_lemma hE (i := 15) rfl (.cons (hO u) (.cons (hO t) .nil)) rfl rfl
  · exact reaches_lemma hE (i := 16) rfl
      (.cons (hO u) (.cons (hO t) (.cons (typeIn_bitsT hS c) .nil))) rfl rfl
  · exact reaches_lemma hE (i := 17) rfl
      (.cons (hO u) (.cons (hO t) (.cons (typeIn_bitsT hS c) .nil))) rfl rfl

/-- Comparison, by recursion on the second number. -/
theorem reaches_cmp (b : List Bool) : ∀ a : List Bool,
    Reaches G E n Γ Φ (Sym.cmp.call [bitsT a, bitsT b]) (ordT (compare (val a) (val b))) :=
  b.rec (fun a ↦ ((reaches_lemma₁ hE hS (i := 35) rfl a rfl rfl).trans
      (reaches_condO hE hS hO a .gt .eq)).of_eq (by
        rcases a with _ | ⟨e, x⟩
        · rw [Nat.compare_eq_eq.mpr rfl]
          rfl
        · rw [Nat.compare_eq_gt.mpr (by bits_arith)]
          rfl))
    fun d y ih a ↦ by
      rcases a with _ | ⟨e, x⟩
      · rw [Nat.compare_eq_lt.mpr (by bits_arith)]
        cases d
        · exact reaches_lemma₁ hE hS (i := 36) rfl y rfl rfl
        · exact reaches_lemma₁ hE hS (i := 37) rfl y rfl rfl
      · have hsel (m : Term) (hm : typeIn G n Γ m = some ordTy) :=
          (reaches_sel (Φ := Φ) ordTy ltO m gtO (ih x)).trans
            (reaches_selO hE (compare (val x) (val y)) (hO .lt) hm (hO .gt))
        rw [compare_cons]
        cases e <;> cases d
        · exact ((reaches_lemma₂ hE hS (i := 38) rfl x y rfl rfl).trans (hsel eqO (hO .eq))).of_eq
            (by cases compare (val x) (val y) <;> rfl)
        · exact ((reaches_lemma₂ hE hS (i := 39) rfl x y rfl rfl).trans (hsel ltO (hO .lt))).of_eq
            (by cases compare (val x) (val y) <;> rfl)
        · exact ((reaches_lemma₂ hE hS (i := 40) rfl x y rfl rfl).trans (hsel gtO (hO .gt))).of_eq
            (by cases compare (val x) (val y) <;> rfl)
        · exact ((reaches_lemma₂ hE hS (i := 41) rfl x y rfl rfl).trans (hsel eqO (hO .eq))).of_eq
            (by cases compare (val x) (val y) <;> rfl)

/-- Less, by the comparison. -/
theorem reaches_ltB (a b : List Bool) :
    Reaches G E n Γ Φ (Sym.ltB.call [bitsT a, bitsT b])
      (bitsT (truth (decide (val a < val b)))) := by
  have ty := typeIn_bitsT (Γ := Γ) hS
  refine (((reaches_lemma₂ hE hS (i := 48) rfl a b rfl rfl).trans
    (reaches_sel bitsTy trueT bnilT bnilT (reaches_cmp hE hS hO b a))).trans
    (reaches_selB hE _ (ty [false]) (ty []) (ty []))).of_eq ?_
  rcases h : compare (val a) (val b) with _ | _ | _
  · rw [decide_eq_true (Nat.compare_eq_lt.mp h)]
    rfl
  · rw [decide_eq_false (by have := Nat.compare_eq_eq.mp h; omega)]
    rfl
  · rw [decide_eq_false (by have := Nat.compare_eq_gt.mp h; omega)]
    rfl

/-- The truncated difference, by less and the difference of a number at most the first. -/
theorem reaches_sub (a b : List Bool) :
    Reaches G E n Γ Φ (Sym.sub.call [bitsT a, bitsT b]) (bitsT (num (val a - val b))) := by
  have ty := typeIn_bitsT (Γ := Γ) hS
  have hc := ((reaches_lemma₂ hE hS (Φ := Φ) (i := 56) rfl a b rfl rfl).trans
    (reaches_call .condB (.cons (reaches_ltB hE hS hO a b)
      (.cons (reaches_refl _) (.cons (reaches_refl _) .nil))))).trans
    (reaches_condB hE hS (truth (decide (val a < val b))) (ty [])
      (typeIn_call' hS .subE (.cons (ty a) (.cons (ty b) .nil))))
  by_cases h : val a < val b
  · rw [decide_eq_true h] at hc
    exact hc.of_eq (congrArg bitsT (num_eq (w := []) (by bits_arith))).symm
  · rw [decide_eq_false h] at hc
    exact hc.trans (reaches_subE hE hS b a (by omega))

omit hE hS hO in
/-- A function of a bitstring has a value only at a bitstring. -/
theorem ofBits₁_eq_some {f : List Bool → List Bool} {vs : List Val} {v : Val}
    (h : ofBits₁ f vs = some v) : ∃ w, vs = [.bits w] ∧ v = .bits (f w) := by
  rcases vs with _ | ⟨_ | _, _ | _⟩ <;> simp only [ofBits₁, reduceCtorEq] at h
  exact ⟨_, rfl, (Option.some_inj.mp h).symm⟩

omit hE hS hO in
/-- A function of two bitstrings has a value only at two bitstrings. -/
theorem ofBits₂_eq_some {f : List Bool → List Bool → Option Val} {vs : List Val} {v : Val}
    (h : ofBits₂ f vs = some v) : ∃ a b, vs = [.bits a, .bits b] ∧ f a b = some v := by
  rcases vs with _ | ⟨_ | _, _ | ⟨_ | _, _ | _⟩⟩ <;> simp only [ofBits₂, reduceCtorEq] at h
  exact ⟨_, _, rfl, h⟩

/-- A definition rewrites at literals to its value's literal. -/
theorem reaches_host (s : Sym) {vs : List Val} {v : Val} (h : s.host vs = some v) :
    Reaches G E n Γ Φ (s.call (vs.map Val.term)) v.term := by
  have ty := typeIn_bitsT (Γ := Γ) hS
  cases s
  case bnil =>
    rcases vs with _ | _ <;> simp only [Sym.host, reduceCtorEq] at h
    cases h
    exact reaches_refl _
  case condB =>
    rcases vs with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | _⟩⟩⟩ <;>
      simp only [Sym.host, reduceCtorEq] at h
    cases h
    exact (reaches_condB hE hS _ (ty _) (ty _)).of_eq (by split <;> rfl)
  case condO =>
    rcases vs with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | _⟩⟩⟩ <;>
      simp only [Sym.host, reduceCtorEq] at h
    cases h
    exact reaches_condO hE hS hO _ _ _
  all_goals first
    | obtain ⟨w, rfl, rfl⟩ := ofBits₁_eq_some h
    | obtain ⟨a, b, rfl, hf⟩ := ofBits₂_eq_some h
  case b0 => exact reaches_refl _
  case b1 => exact reaches_refl _
  case isNil => exact reaches_isNil hE hS w
  case succ => exact reaches_succ hE hS w
  case dbl => exact reaches_dbl hE hS w
  case pred => exact reaches_pred hE hS w
  case add => cases hf; exact reaches_add hE hS b a
  case mul => cases hf; exact reaches_mul hE hS a b
  case eqB => cases hf; exact reaches_eqB hE hS b a
  case cmp => cases hf; exact reaches_cmp hE hS hO b a
  case ltB => cases hf; exact reaches_ltB hE hS hO a b
  case sub => cases hf; exact reaches_sub hE hS hO a b
  case subE =>
    split at hf
    · cases hf
      exact reaches_subE hE hS b a (by assumption)
    · cases hf

omit hE hS hO in
/-- The comparison's result a term is, where it is one, has that term. -/
theorem ordOf_eq_some {t : Term} {o : Ordering} (h : ordOf t = some o) : ordT o = t :=
  of_decide_eq_true (List.find?_some (p := fun o ↦ decide (ordT o = t)) h)

omit hE hS hO in
/-- A label applying a definition evaluated is that definition's at its objects. -/
theorem ofLabel_eq_some {l : Internal.Label} {s : Sym} (h : Sym.ofLabel l = some s) :
    l = .defn s.index s.objs := by
  cases l <;> simp only [Sym.ofLabel, reduceCtorEq] at h
  rename_i k θ
  obtain ⟨rfl, rfl⟩ := of_decide_eq_true
    (List.find?_some (p := fun s : Sym ↦ decide (s.index = k ∧ s.objs = θ)) h)
  rfl

omit hE hS hO in
/-- Terms whose values are a list of literals rewrite to those literals where each term that
evaluates rewrites to its value's literal. -/
theorem forall₂_of_map_eval : ∀ cs : List Term,
    (∀ c ∈ cs, ∀ v, eval c = some v → Reaches G E n Γ Φ c v.term) →
    ∀ ws : List Val, cs.map eval = ws.map some →
      List.Forall₂ (Reaches G E n Γ Φ) cs (ws.map Val.term) :=
  fun cs ↦ cs.rec (fun _ ws h ↦ match ws, h with
      | [], _ => .nil)
    fun c cs ih hc ws h ↦ match ws, h with
      | w :: ws, h => by
        simp only [List.map_cons, List.cons.injEq] at h
        exact .cons (hc c List.mem_cons_self w h.1)
          (ih (fun c' hc' ↦ hc c' (List.mem_cons_of_mem c hc')) ws h.2)

/-- A term that evaluates rewrites to its value's literal. -/
theorem eval_reaches : ∀ (t : Term) (v : Val), eval t = some v → Reaches G E n Γ Φ t v.term :=
  RoseTree.ind fun l cs ih v h ↦ by
    have hcs : (cs.map fun c ↦ (c, eval c)).map Prod.fst = cs := by
      rw [List.map_map]
      exact List.map_id' cs
    simp only [eval, RoseTree.para_node, evalStep] at h
    change (match ordOf (RoseTree.node l ((cs.map fun c ↦ (c, eval c)).map Prod.fst)) with
      | some o => some (Val.ord o)
      | none => (Sym.ofLabel l).bind fun s ↦
        (((cs.map fun c ↦ (c, eval c)).map Prod.snd).reverse.mapM id).bind s.host) = some v at h
    rw [hcs] at h
    split at h
    · rename_i o ho
      cases h
      exact (reaches_refl _).of_eq (ordOf_eq_some ho).symm
    · obtain ⟨s, hs, h₁⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, hvs, h₂⟩ := Option.bind_eq_some_iff.mp h₁
      obtain rfl := ofLabel_eq_some hs
      have hm := (PartialHorn.mapM_eq_some_iff _ vs).mp hvs
      rw [List.map_id, List.map_map] at hm
      have hm' : cs.map eval = vs.reverse.map some := by
        rw [List.map_reverse, ← hm, List.reverse_reverse]
        rfl
      have hr := reaches_node (G := G) (E := E) (n := n) (Γ := Γ) (Φ := Φ)
        (l := .defn s.index s.objs) (fun _ ↦ rfl)
        (forall₂_of_map_eval cs ih vs.reverse hm')
      refine hr.trans ?_
      have hc : RoseTree.node (Internal.Label.defn s.index s.objs) (vs.reverse.map Val.term) =
          s.call (vs.map Val.term) := by
        rw [Sym.call, call, Term.defn, List.map_reverse]
      rw [hc]
      exact reaches_host hE hS hO s h₂

end Arithmetic

/-- A term that evaluates rewrites to its value's literal by a derivation of the language, where
the evaluation is ready. -/
theorem checked_of_eval {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}
    {j : ℕ} {t : Term} {v : Val} (hr : ready G E n Γ j = true) (h : eval t = some v) :
    ∃ d, Checked G E n Γ Φ t (v.term, d) := by
  simp only [ready, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨hE, hS⟩, hO⟩ := hr
  exact eval_reaches (inEnv_of_lemmasIn hE) hS (fun o ↦ by
    cases o <;> exact of_decide_eq_true (hO _ (by simp only [List.mem_cons, reduceCtorEq,
      List.not_mem_nil, or_false, or_true]))) t v h

end Geb.FreeTopos.Literals

end
