/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.W.Basic
public import Geb.Prototypes.RoseTree.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Partial Horn logic

The logic of partial Horn theories {cite}`PalmgrenVickers2007`, over rose trees. A signature
names, for each partial operation by its index, the sorts of its arguments and the sort of its
result. A term is a rose tree: a variable is the node of label zero over the leaf of its index,
and the operation of index {lit}`k` applied to terms is the node of label {lit}`k + 1` over
them. An
equation between two terms holds in a model at an assignment of the variables when both sides
are defined there and denote one value, so that the equation of a term with itself states that
the term is defined. A sequent is a context of sorts, a list of equations as hypotheses and an
equation as its conclusion; a theory is a signature with sequents as its axioms.

A model interprets each sort as a type and each operation as a partial function on sorted
values. It is a model of a theory when each axiom holds in it at every assignment of the
axiom's context that satisfies the axiom's hypotheses.

A certificate is a rose tree whose node's label names a rule and whose children are its
premises' certificates and the terms the rule names. The checker is a fold over the certificate
that computes each conclusion from its premises' conclusions, trusting no stated conclusion. Its
rules are those of Definition 1 of the source, stated for a single equation as conclusion: a
hypothesis; the reflexivity of a variable; symmetry and transitivity; congruence of an
operation at a defined application; the strictness of operations, by which the arguments of a
defined application are defined; the instance of an axiom at defined terms of its context's
sorts whose hypotheses are proved, which is partial term substitution followed by cut; cut; and
the instance of a theorem of an environment, as of an axiom. Every conclusion the checker
computes holds in every model of the theory in which the environment's theorems hold.

## Main definitions

* {lit}`Sig`, {lit}`Theory` — signatures and theories.
* {lit}`sortOf`, {lit}`subst`, {lit}`Scoped` — the sort of a term, substitution, and the scope
  of a term's variables.
* {lit}`Model`, {lit}`eval` — models and the value of a term.
* {lit}`Eqn`, {lit}`Seq`, {lit}`Valid`, {lit}`IsModel` — equations, sequents, validity, and
  models of a theory.
* {lit}`checkStep`, {lit}`check` — the rules, and the checker.

## Main statements

* {lit}`eval_subst` — the value of a substitution instance is the value at the substituted
  terms' values.
* {lit}`sort_eval` — a defined term's value has the term's sort.
* {lit}`check_sound` — every conclusion the checker computes is valid in every model.

## References

* {cite}`PalmgrenVickers2007`, Definition 1 for the rules, Section 3 for models.

## Tags

partial Horn logic, essentially algebraic theory, partial algebra, proof certificate, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

universe v

/-- The terms of a partial Horn theory, and its certificates: rose trees with natural-number
labels. -/
abbrev Tree : Type := RoseTree ℕ

/-- The variable of an index. -/
def var (i : ℕ) : Tree := RoseTree.node 0 [RoseTree.node i []]

/-- The operation of index {lit}`k` applied to terms. -/
def op (k : ℕ) (ts : List Tree) : Tree := RoseTree.node (k + 1) ts

/-- A many-sorted signature of partial operations: for each operation, by its index, the sorts
of its arguments and the sort of its result. -/
abbrev Sig : Type := List (List ℕ × ℕ)

/-- The sort of a term in a context of sorts, or nothing when the term is not well sorted. -/
def sortOf (S : Sig) (Γ : List ℕ) : Tree → Option ℕ :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => Γ[i.label]?
    | k + 1, cs => S[k]?.bind fun o ↦ if cs.map Prod.snd = o.1.map some then some o.2 else none
    | _, _ => none

/-- Whether every variable of a term has an index below {lit}`n`. -/
def Scoped (n : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => decide (i.label < n)
    | 0, _ => false
    | _ + 1, cs => cs.all Prod.snd

/-- The substitution of terms for the variables of a term, the variable of index {lit}`i`
replaced by the term at position {lit}`i`; a variable beyond the terms is left in place. -/
def subst (ts : List Tree) : Tree → Tree :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => ts[i.label]?.getD (var i.label)
    | l, cs => RoseTree.node l (cs.map Prod.snd)

/-- An equation between two terms. -/
@[ext] structure Eqn where
  /-- The left side. -/
  lhs : Tree
  /-- The right side. -/
  rhs : Tree
deriving DecidableEq

/-- The substitution of terms for the variables of both sides of an equation. -/
def Eqn.subst (ts : List Tree) (q : Eqn) : Eqn := ⟨PartialHorn.subst ts q.lhs,
  PartialHorn.subst ts q.rhs⟩

/-- Whether every variable of both sides of an equation has an index below {lit}`n`. -/
def Eqn.Scoped (n : ℕ) (q : Eqn) : Bool := PartialHorn.Scoped n q.lhs && PartialHorn.Scoped n q.rhs

/-- A Horn sequent: a context of sorts, hypotheses and a conclusion, each an equation. -/
@[ext] structure Seq where
  /-- The sorts of the variables. -/
  ctx : List ℕ
  /-- The hypotheses. -/
  hyps : List Eqn
  /-- The conclusion. -/
  concl : Eqn

/-- Whether every variable of a sequent's equations is in its context. -/
def Seq.Scoped (a : Seq) : Bool :=
  a.hyps.all (·.Scoped a.ctx.length) && a.concl.Scoped a.ctx.length

/-- A partial Horn theory: a signature and axioms. -/
structure Theory where
  /-- The signature. -/
  sig : Sig
  /-- The axioms. -/
  axioms : List Seq

/-- A model of a signature: a type for each sort, and for each operation, by its index, a
partial function from lists of sorted values to sorted values, whose values have the operation's
result sort. -/
structure Model (S : Sig) where
  /-- The values of each sort. -/
  Car : ℕ → Type v
  /-- The partial operations. -/
  op : ℕ → List (Σ s, Car s) → Option (Σ s, Car s)
  /-- A value of an operation has the operation's result sort. -/
  op_sort : ∀ {k : ℕ} {args : List (Σ s, Car s)} {w : Σ s, Car s}, op k args = some w →
    (S[k]?).map Prod.snd = some w.1

variable {S : Sig}

/-- The sorted values of a model. -/
abbrev Model.Val (M : Model.{v} S) : Type v := Σ s, M.Car s

/-- The value of a term in a model at an assignment of values to the variables by index, or
nothing when the term is undefined there. -/
def eval (M : Model.{v} S) (ρ : List M.Val) : Tree → Option M.Val :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => ρ[i.label]?
    | k + 1, cs => (cs.mapM Prod.snd).bind (M.op k)
    | _, _ => none

/-- An equation holds at an assignment when both sides are defined there with one value. -/
def Eqn.Holds (M : Model.{v} S) (ρ : List M.Val) (q : Eqn) : Prop :=
  ∃ w, eval M ρ q.lhs = some w ∧ eval M ρ q.rhs = some w

/-- A conclusion is valid under hypotheses in a context when it holds at every assignment of
the context's sorts at which the hypotheses hold. -/
def Valid (M : Model.{v} S) (Γ : List ℕ) (H : List Eqn) (q : Eqn) : Prop :=
  ∀ ρ : List M.Val, ρ.map Sigma.fst = Γ → (∀ h ∈ H, h.Holds M ρ) → q.Holds M ρ

/-- A sequent is valid in a model when its conclusion is valid under its hypotheses. -/
def Seq.Valid (M : Model.{v} S) (a : Seq) : Prop := PartialHorn.Valid M a.ctx a.hyps a.concl

/-- A model of a theory: every axiom is valid in it. -/
def IsModel (T : Theory) (M : Model.{v} T.sig) : Prop := ∀ a ∈ T.axioms, a.Valid M

namespace Rule

/-- A hypothesis, by index. -/
@[match_pattern] abbrev hyp : ℕ := 0

/-- The reflexivity of a variable, by index: the variable is defined. -/
@[match_pattern] abbrev refl : ℕ := 1

/-- Symmetry. -/
@[match_pattern] abbrev symm : ℕ := 2

/-- Transitivity. -/
@[match_pattern] abbrev trans : ℕ := 3

/-- Congruence of an operation at a defined application. -/
@[match_pattern] abbrev cong : ℕ := 4

/-- Strictness: an argument of a defined application is defined. -/
@[match_pattern] abbrev strict : ℕ := 5

/-- An instance of an axiom. -/
@[match_pattern] abbrev ax : ℕ := 6

/-- Cut. -/
@[match_pattern] abbrev cut : ℕ := 7

/-- An instance of a theorem of the environment. -/
@[match_pattern] abbrev thm : ℕ := 8

end Rule

/-- The checker's result at a certificate: the conclusion, as a function of the context and
the hypotheses, or nothing when the certificate does not check. -/
abbrev Chk : Type := List ℕ → List Eqn → Option Eqn

/-- The instance of a sequent at the terms of a certificate's node: the terms for the context's
variables, then a premise for each term whose conclusion's left side is that term, then a
premise for each hypothesis whose conclusion is its instance. The terms must have the context's
sorts and the sequent's variables must lie in its context. -/
def inst (S : Sig) (a : Seq) (cs : List (Tree × Chk)) : Chk := fun Γ H ↦
  let n := a.ctx.length
  let ts := (cs.take n).map Prod.fst
  let ds := ((cs.drop n).take n).map fun c ↦ (c.2 Γ H).map Eqn.lhs
  let hs := (cs.drop (n + n)).map fun c ↦ c.2 Γ H
  if a.Scoped ∧ ts.map (sortOf S Γ) = a.ctx.map some ∧ ds = ts.map some ∧
      hs = a.hyps.map fun h ↦ some (h.subst ts) then
    some (a.concl.subst ts)
  else none

/-- One rule of the checker, by the label of a certificate's node: its children are the
premises' certificates, with their results, and the terms the rule names. -/
def checkStep (T : Theory) (E : List Seq) (l : ℕ) (cs : List (Tree × Chk)) : Chk := fun Γ H ↦
  match l, cs with
  | Rule.hyp, [(i, _)] => H[i.label]?
  | Rule.refl, [(i, _)] => if i.label < Γ.length then some ⟨var i.label, var i.label⟩ else none
  | Rule.symm, [(_, p)] => (p Γ H).map fun q ↦ ⟨q.rhs, q.lhs⟩
  | Rule.trans, [(_, p), (_, p')] => (p Γ H).bind fun q ↦ (p' Γ H).bind fun q' ↦
    if q.rhs = q'.lhs then some ⟨q.lhs, q'.rhs⟩ else none
  | Rule.cong, (_, d) :: ps => (d Γ H).bind fun q ↦
    if q.lhs.label ≠ 0 ∧ (ps.map fun p ↦ (p.2 Γ H).map Eqn.lhs) = q.lhs.children.map some then
      (ps.mapM fun (p : Tree × Chk) ↦ (p.2 Γ H).map Eqn.rhs).map fun ts ↦
        ⟨q.lhs, RoseTree.node q.lhs.label ts⟩
    else none
  | Rule.strict, [(j, _), (_, p)] => (p Γ H).bind fun q ↦
    if q.lhs.label ≠ 0 then (q.lhs.children[j.label]?).map fun t ↦ ⟨t, t⟩ else none
  | Rule.ax, (j, _) :: cs => T.axioms[j.label]?.bind fun a ↦ inst T.sig a cs Γ H
  | Rule.cut, [(_, p), (_, p')] => (p Γ H).bind fun h ↦ p' Γ (h :: H)
  | Rule.thm, (j, _) :: cs => E[j.label]?.bind fun a ↦ inst T.sig a cs Γ H
  | _, _ => none

/-- The checker: the conclusion of a certificate in a theory and an environment of theorems, as
a function of the context and the hypotheses, or nothing when the certificate does not check. -/
def check (T : Theory) (E : List Seq) (c : Tree) : Chk := RoseTree.para (checkStep T E) c

section Soundness

/-- A list's elements all have values under a partial function exactly when the function
mapped over the list is the list of those values. -/
theorem mapM_eq_some_iff {α β : Type*} {f : α → Option β} (l : List α) :
    ∀ vs : List β, l.mapM f = some vs ↔ l.map f = vs.map some :=
  l.rec (motive := fun l ↦ ∀ vs, l.mapM f = some vs ↔ l.map f = vs.map some)
    (fun vs ↦ by cases vs <;> simp)
    (fun a l ih vs ↦ by
      cases vs with
      | nil => simp [List.mapM_cons, Option.bind_eq_some_iff]
      | cons v vs =>
        simp only [List.mapM_cons, List.map_cons, List.cons.injEq, ← ih vs]
        cases f a <;> cases l.mapM f <;> simp)

variable {M : Model.{v} S} {ρ : List M.Val}

/-- The value of a variable is the assignment's value at its index. -/
@[simp] theorem eval_var (i : ℕ) : eval M ρ (var i) = ρ[i]? := by
  simp [eval, var]

/-- The value of a node of label zero over one child is the assignment's value at the child's
label. -/
theorem eval_node_zero (i : Tree) : eval M ρ (RoseTree.node 0 [i]) = ρ[i.label]? := by
  simp [eval]

/-- The value of an operation's application: the operation at its arguments' values, when
they are all defined. -/
theorem eval_node_succ (k : ℕ) (ts : List Tree) :
    eval M ρ (RoseTree.node (k + 1) ts) = (ts.mapM (eval M ρ)).bind (M.op k) := by
  simp only [eval, RoseTree.para_node, List.mapM_map]
  rfl

/-- Substitution at a variable's node. -/
theorem subst_node_zero (ts : List Tree) (i : Tree) :
    subst ts (RoseTree.node 0 [i]) = ts[i.label]?.getD (var i.label) := by
  simp [subst]

/-- Substitution at an operation's node substitutes in the arguments. -/
theorem subst_node_succ (ts : List Tree) (k : ℕ) (cs : List Tree) :
    subst ts (RoseTree.node (k + 1) cs) = RoseTree.node (k + 1) (cs.map (subst ts)) := by
  simp [subst]
  rfl

/-- A variable's node is in scope when its index is. -/
theorem scoped_node_zero (n : ℕ) (i : Tree) :
    Scoped n (RoseTree.node 0 [i]) = decide (i.label < n) := by
  simp [Scoped]

/-- An operation's node is in scope when its arguments are. -/
theorem scoped_node_succ (n k : ℕ) (cs : List Tree) :
    Scoped n (RoseTree.node (k + 1) cs) = cs.all (Scoped n) := by
  simp [Scoped, List.all_map]
  rfl

/-- Mapping partial functions that agree on a list's elements gives one result. -/
theorem mapM_congr {α β : Type*} {f g : α → Option β} {l : List α} (h : ∀ a ∈ l, f a = g a) :
    l.mapM f = l.mapM g := by
  rw [← Function.id_comp f, ← Function.id_comp g, ← List.mapM_map, ← List.mapM_map,
    List.map_congr_left h]

/-- The value of a substitution instance of a term in scope is the term's value at the
substituted terms' values. -/
theorem eval_subst {ts : List Tree} {ws : List M.Val} (hts : ts.map (eval M ρ) = ws.map some) :
    ∀ t, Scoped ts.length t = true → eval M ρ (subst ts t) = eval M ws t :=
  RoseTree.ind fun l cs ih hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [Scoped] at hs
      · have hi : i.label < ts.length := by simpa [scoped_node_zero] using hs
        have hlen : ts.length = ws.length := by simpa using congrArg List.length hts
        have hi' : i.label < ws.length := hlen ▸ hi
        have hw := congrArg (fun l ↦ l[i.label]?) hts
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at hw
        rw [subst_node_zero, eval_node_zero, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi']
        exact hw
      · simp [Scoped] at hs
    · rw [scoped_node_succ, List.all_eq_true] at hs
      rw [subst_node_succ, eval_node_succ, eval_node_succ, List.mapM_map]
      exact congrArg (fun o ↦ Option.bind o (M.op k)) (mapM_congr fun c hc ↦ ih c hc (hs c hc))

/-- The sort of a variable's node is the context's sort at its index. -/
theorem sortOf_node_zero (Γ : List ℕ) (i : Tree) :
    sortOf S Γ (RoseTree.node 0 [i]) = Γ[i.label]? := by
  simp [sortOf]

/-- The sort of an operation's node is the operation's result sort, when its arguments have
the operation's argument sorts. -/
theorem sortOf_node_succ (Γ : List ℕ) (k : ℕ) (cs : List Tree) :
    sortOf S Γ (RoseTree.node (k + 1) cs) = S[k]?.bind fun o ↦
      if cs.map (sortOf S Γ) = o.1.map some then some o.2 else none := by
  simp only [sortOf, RoseTree.para_node, List.map_map]
  rfl

/-- A defined term's value has the term's sort, at an assignment of the context's sorts. -/
theorem sort_eval {Γ : List ℕ} (hρ : ρ.map Sigma.fst = Γ) :
    ∀ t : Tree, ∀ {s : ℕ} {w : M.Val}, sortOf S Γ t = some s → eval M ρ t = some w → w.1 = s :=
  RoseTree.ind fun l cs _ s w hs he ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [sortOf] at hs
      · rw [sortOf_node_zero] at hs
        rw [eval_node_zero] at he
        have h := congrArg (fun l ↦ l[i.label]?) hρ
        simp only [List.getElem?_map, he, hs, Option.map_some, Option.some.injEq] at h
        exact h
      · simp [sortOf] at hs
    · rw [eval_node_succ, Option.bind_eq_some_iff] at he
      obtain ⟨_, -, hop⟩ := he
      have hw := M.op_sort hop
      rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, hk, ho⟩ := hs
      rw [hk, Option.map_some, Option.some.injEq] at hw
      split at ho
      · exact hw.symm.trans (Option.some.inj ho)
      · exact absurd ho (by simp)

/-- When a partial function has a value at every element of a list, it maps the list to the
list of those values. -/
theorem exists_map_eq_map_some {α β : Type*} {f : α → Option β} (l : List α) :
    (∀ a ∈ l, ∃ b, f a = some b) → ∃ bs : List β, l.map f = bs.map some :=
  l.rec (motive := fun l ↦ (∀ a ∈ l, ∃ b, f a = some b) → ∃ bs : List β, l.map f = bs.map some)
    (fun _ ↦ ⟨[], rfl⟩)
    (fun a l ih h ↦ by
      obtain ⟨b, hb⟩ := h a List.mem_cons_self
      obtain ⟨bs, hbs⟩ := ih fun a' ha' ↦ h a' (List.mem_cons_of_mem a ha')
      exact ⟨b :: bs, by simp [hb, hbs]⟩)

/-- An instance of a valid sequent is valid, when the checker's premises are. -/
theorem inst_sound {a : Seq} {cs : List (Tree × Chk)} {Γ : List ℕ} {H : List Eqn} {q : Eqn}
    (ha : a.Valid M) (hcs : ∀ c ∈ cs, ∀ Γ' H' q', c.2 Γ' H' = some q' → Valid M Γ' H' q')
    (h : inst S a cs Γ H = some q) : Valid M Γ H q := by
  simp only [inst] at h
  split at h
  · rename_i hc
    obtain ⟨hsc, hsort, hds, hhs⟩ := hc
    cases h
    intro ρ hρ hH
    set ts := (cs.take a.ctx.length).map Prod.fst with hts
    have hlen : ts.length = a.ctx.length := by simpa using congrArg List.length hsort
    have hdef : ∀ t ∈ ts, ∃ w, eval M ρ t = some w := by
      intro t ht
      have hm : some t ∈ ts.map some := List.mem_map_of_mem ht
      rw [← hds] at hm
      obtain ⟨c, hc, hct⟩ := List.mem_map.mp hm
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hct
      obtain ⟨w, hw, -⟩ :=
        hcs c (List.mem_of_mem_drop (List.mem_of_mem_take hc)) Γ H e he ρ hρ hH
      exact ⟨w, hw⟩
    obtain ⟨ws, hws⟩ := exists_map_eq_map_some _ hdef
    have hlw : ws.length = a.ctx.length :=
      (by simpa using congrArg List.length hws : ts.length = ws.length).symm.trans hlen
    have hwsort : ws.map Sigma.fst = a.ctx := by
      refine List.ext_getElem (by simpa using hlw) fun i h1 h2 ↦ ?_
      have hi : i < ts.length := hlen ▸ h2
      have e1 := congrArg (fun l ↦ l[i]?) hws
      have e2 := congrArg (fun l ↦ l[i]?) hsort
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (hlw ▸ h2), List.getElem?_eq_getElem h2, Option.map_some,
        Option.some.injEq] at e1 e2
      simpa using sort_eval hρ _ e2 e1
    have hsc' := hsc
    simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at hsc'
    obtain ⟨hsh, hscl, hscr⟩ := hsc'
    rw [← hlen] at hsh hscl hscr
    have hhyp : ∀ h ∈ a.hyps, h.Holds M ws := by
      intro h hh
      have hm : some (h.subst ts) ∈ a.hyps.map fun h ↦ some (h.subst ts) :=
        List.mem_map.mpr ⟨h, hh, rfl⟩
      rw [← hhs] at hm
      obtain ⟨c, hc, hct⟩ := List.mem_map.mp hm
      obtain ⟨w, h1, h2⟩ := hcs c (List.mem_of_mem_drop hc) Γ H _ hct ρ hρ hH
      obtain ⟨hl, hr⟩ := hsh h hh
      exact ⟨w, (eval_subst hws _ hl).symm.trans h1, (eval_subst hws _ hr).symm.trans h2⟩
    obtain ⟨w, h1, h2⟩ := ha ws hwsort hhyp
    exact ⟨w, (eval_subst hws _ hscl).trans h1, (eval_subst hws _ hscr).trans h2⟩
  · exact absurd h (by simp)

/-- Every conclusion the checker computes is valid in every model of the theory in which the
environment's theorems are valid. -/
theorem check_sound {T : Theory} {E : List Seq} {M : Model.{v} T.sig} (hM : IsModel T M)
    (hE : ∀ a ∈ E, a.Valid M) :
    ∀ c : Tree, ∀ Γ H q, check T E c Γ H = some q → Valid M Γ H q :=
  RoseTree.ind fun l cs ih Γ H q h ↦ by
    have hcs : ∀ c ∈ cs.map (fun c ↦ (c, check T E c)), ∀ Γ' H' q',
        c.2 Γ' H' = some q' → Valid M Γ' H' q' := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
    rw [check, RoseTree.para_node] at h
    change checkStep T E l (cs.map fun c ↦ (c, check T E c)) Γ H = some q at h
    generalize cs.map (fun c ↦ (c, check T E c)) = rs at h hcs
    unfold checkStep at h
    split at h
    · -- a hypothesis
      exact fun ρ _ hH ↦ hH q (List.mem_of_getElem? h)
    · -- the reflexivity of a variable
      rename_i i _
      split at h
      · rename_i hi
        cases h
        intro ρ hρ _
        have hi' : i.label < ρ.length := by simpa [← hρ] using hi
        exact ⟨ρ[i.label], by simp [hi'], by simp [hi']⟩
      · exact absurd h (by simp)
    · -- symmetry
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      intro ρ hρ hH
      obtain ⟨w, h1, h2⟩ := hcs _ List.mem_cons_self Γ H q' hq' ρ hρ hH
      exact ⟨w, h2, h1⟩
    · -- transitivity
      rename_i _ p _ p'
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, q₂, hq₂, h⟩ := h
      split at h
      · rename_i hmid
        cases h
        intro ρ hρ hH
        obtain ⟨w, h1, h2⟩ := hcs _ List.mem_cons_self Γ H q₁ hq₁ ρ hρ hH
        obtain ⟨w', h1', h2'⟩ :=
          hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ H q₂ hq₂ ρ hρ hH
        rw [← hmid, h2, Option.some.injEq] at h1'
        exact ⟨w, h1, h1' ▸ h2'⟩
      · exact absurd h (by simp)
    · -- congruence of an operation at a defined application
      rename_i _ d ps
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₀, hq₀, h⟩ := h
      split at h
      · rename_i hc
        obtain ⟨hl, hls⟩ := hc
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [mapM_eq_some_iff] at hts
        intro ρ hρ hH
        obtain ⟨w, h1, -⟩ := hcs _ List.mem_cons_self Γ H q₀ hq₀ ρ hρ hH
        obtain ⟨k, hk⟩ : ∃ k, q₀.lhs.label = k + 1 := ⟨q₀.lhs.label - 1, by omega⟩
        have hlhs : q₀.lhs = RoseTree.node (k + 1) q₀.lhs.children := by
          rw [← hk]; exact (RoseTree.node_label_children _).symm
        have hlen₁ : ps.length = q₀.lhs.children.length := by
          simpa using congrArg List.length hls
        have hlen₂ : ps.length = ts.length := by simpa using congrArg List.length hts
        have hmap : q₀.lhs.children.map (eval M ρ) = ts.map (eval M ρ) := by
          refine List.ext_getElem (by simp [← hlen₁, hlen₂]) fun i hi₁ hi₂ ↦ ?_
          have hi : i < ps.length := by simpa [hlen₁] using hi₁
          have e₁ := congrArg (fun l ↦ l[i]?) hls
          have e₂ := congrArg (fun l ↦ l[i]?) hts
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
            List.getElem?_eq_getElem (hlen₁ ▸ hi), List.getElem?_eq_getElem (hlen₂ ▸ hi),
            Option.map_some, Option.some.injEq] at e₁ e₂
          obtain ⟨e, he, hel⟩ := Option.map_eq_some_iff.mp e₁
          rw [he, Option.map_some, Option.some.injEq] at e₂
          obtain ⟨v, hv₁, hv₂⟩ :=
            hcs ps[i] (List.mem_cons_of_mem _ (List.getElem_mem hi)) Γ H e he ρ hρ hH
          simp only [List.getElem_map]
          rw [← hel, hv₁, ← e₂, hv₂]
        refine ⟨w, h1, ?_⟩
        rw [hlhs, eval_node_succ] at h1
        change eval M ρ (RoseTree.node q₀.lhs.label ts) = some w
        rw [hk, eval_node_succ, ← h1, ← Function.id_comp (eval M ρ), ← List.mapM_map,
          ← List.mapM_map, hmap]
      · exact absurd h (by simp)
    · -- strictness: an argument of a defined application is defined
      rename_i j _ _ p
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₀, hq₀, h⟩ := h
      split at h
      · rename_i hl
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        intro ρ hρ hH
        obtain ⟨w, h1, -⟩ := hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ H q₀ hq₀ ρ hρ hH
        obtain ⟨k, hk⟩ : ∃ k, q₀.lhs.label = k + 1 := ⟨q₀.lhs.label - 1, by omega⟩
        rw [← RoseTree.node_label_children q₀.lhs, hk, eval_node_succ,
          Option.bind_eq_some_iff] at h1
        obtain ⟨args, hargs, -⟩ := h1
        rw [mapM_eq_some_iff] at hargs
        have hj : j.label < q₀.lhs.children.length := (List.getElem?_eq_some_iff.mp ht).1
        have e := congrArg (fun l ↦ l[j.label]?) hargs
        simp only [List.getElem?_map, ht, Option.map_some] at e
        obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp e.symm
        exact ⟨a, ha.symm, ha.symm⟩
      · exact absurd h (by simp)
    · -- an instance of an axiom
      rename_i _ _ cs'
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      exact inst_sound (hM a (List.mem_of_getElem? ha))
        (fun c hc ↦ hcs c (List.mem_cons_of_mem _ hc)) h
    · -- cut
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, hq⟩ := h
      intro ρ hρ hH
      have h₁ := hcs _ List.mem_cons_self Γ H q₁ hq₁ ρ hρ hH
      exact hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ (q₁ :: H) q hq ρ hρ
        (List.forall_mem_cons.mpr ⟨h₁, hH⟩)
    · -- an instance of a theorem
      rename_i _ _ cs'
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      exact inst_sound (hE a (List.mem_of_getElem? ha))
        (fun c hc ↦ hcs c (List.mem_cons_of_mem _ hc)) h
    · exact absurd h (by simp)

end Soundness

end Geb.PartialHorn

end
