/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import Geb.Prototypes.FreeTopos.Internal.MachineSound

set_option doc.verso true in
/-!
# The environment machine written in Geb

The functions of {lit}`bootstrap/free-topos/machine.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the environment machine reducing the internal language's
terms ({name}`Geb.FreeTopos.Internal.machineReduce`) at every encoded input: the reading back of
a value, the evaluation of a term in an environment, the weak head normal form of a value and
the normal form of a value's term in a context, each within a depth of recursion, and the
reduction of a term.

The machine written in Geb applies a level of its recursion to a list of jobs at once: a job is
one of the machine's three operations at its arguments, and a job's state holds the jobs it waits
for, which the level below computes, and what it does with their results. A level is the image
of a function of its jobs, and that function's rounds from the state a job starts in are the
step of the machine's operation at the operations of the depth below, so that the depth of
recursion the machine written in Geb is given means what it means in Lean. A delayed value is
the node of its value and its source ({name}`Geb.FreeTopos.Internal.delayed_eq`), the value that
of the level that builds it.

## Main definitions

* {lit}`mk` — the node of a position over the node of its data and its children, the form of the
  mirror's terms, values, jobs and states.
* {lit}`vdata`, {lit}`encVal` — the position of a value's label with its data, and a value as
  the node of its label's position over the node of the label's data and its children.
* {lit}`encNF` — a normal form with its mark.
* {lit}`Params`, {lit}`PRel` — the parameters of the mirror's machine, and their relation to the
  machine's.
* {lit}`encJobE`, {lit}`encJobW`, {lit}`encJobN` — the encoded jobs.
* {lit}`advBy`, {lit}`machJ` — a state advanced by a function of its jobs, and the result of a
  job within a depth of recursion by the rounds of the state it starts in.
* {lit}`JRel`, {lit}`Reach` — the relation of a function of jobs to the machine's operations at
  a depth, and a state's reaching a result within a number of rounds.
* {lit}`post` — the step of the normal form at a node's normal form with its mark.

## Main statements

* {lit}`readBack_eq` — the mirror's reading back of a value.
* {lit}`msRound_eq`, {lit}`machB_eq` — a round advances each state by a function of its jobs,
  and a level is the image of the result of a job.
* {lit}`eStart_reach`, {lit}`wStart_reach`, {lit}`nStart_reach` — the rounds of the state a job
  starts in are the step of the machine's operation.
* {lit}`machJ_rel` — the result of a job within a depth of recursion is the machine's operation
  at that depth.
* {lit}`machineReduce_eq` — the mirror's reduction of a term.

## Tags

internal language, abstract machine, environment, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Machine

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
open Internal (Term Label VLabel Val Machine)
open scoped FinEnum

/-! Nodes of a position over data and children. -/

/-- The node of a position over the node of its data and its children: the form of the mirror's
terms, values, jobs and states. -/
def mk (l : ℕ) (d cs : List Tree) : Tree := RoseTree.node l (RoseTree.node 0 d :: cs)

/-- The mirror's node of a position over data and children. -/
@[simp] theorem mNode_leaf (l : ℕ) (d cs : List Tree) :
    «Language.mNode» (leaf l) d cs = mk l d cs := rfl

/-- The label of a node of a position. -/
@[simp] theorem label_mk (l : ℕ) (d cs : List Tree) : (mk l d cs).label = l := rfl

/-- The node of the data of a node of a position. -/
@[simp] theorem child_mk (l : ℕ) (d cs : List Tree) :
    Const.child (mk l d cs) (leaf 0) = RoseTree.node 0 d := rfl

/-- The children of a node of a position, as a tree's. -/
@[simp] theorem children_mk (l : ℕ) (d cs : List Tree) :
    (mk l d cs).children = RoseTree.node 0 d :: cs := RoseTree.children_node _ _

/-- The mirror's children of a node of a position. -/
@[simp] theorem mArgs_mk (l : ℕ) (d cs : List Tree) : «Language.mArgs» (mk l d cs) = cs := by
  simp [«Language.mArgs», mk]

/-- The mirror's datum of a node of a position, at an index. -/
@[simp] theorem mD_mk (l : ℕ) (d cs : List Tree) (i : ℕ) :
    «Language.mD» (mk l d cs) (leaf i) = d.getD i (leaf 0) := by
  simp [«Language.mD», «Language.mData», mk]

/-- The mirror's child of a node of a position, at an index. -/
@[simp] theorem mArg_mk (l : ℕ) (d cs : List Tree) (i : ℕ) :
    «Language.mArg» (mk l d cs) (leaf i) = cs.getD i (leaf 0) := by
  simp [«Language.mArg»]

/-- The mirror's test of the position and the number of children of a node of a position. -/
@[simp] theorem mIs_mk (a b l : ℕ) (d cs : List Tree) :
    «Language.mIs» (leaf a) (leaf b) (mk l d cs) = ofBool (l == a && cs.length == b) := by
  simp [«Language.mIs»]

/-- The mirror's lists of a few elements. -/
theorem l2_eq (a b : Tree) : «Theory.l2» a b = [a, b] := rfl

@[inherit_doc l2_eq] theorem l3_eq (a b c : Tree) : «Theory.l3» a b c = [a, b, c] := rfl

@[inherit_doc l2_eq] theorem l4_eq (a b c d : Tree) : «Theory.l4» a b c d = [a, b, c, d] := rfl

@[inherit_doc l2_eq] theorem l5_eq (a b c d e : Tree) :
    «Theory.l5» a b c d e = [a, b, c, d, e] := rfl

@[inherit_doc l2_eq] theorem l6_eq (a b c d e f : Tree) :
    «Theory.l6» a b c d e f = [a, b, c, d, e, f] := rfl

/-- A list with elements beyond a number has not that number of elements. -/
theorem succ_beq_zero (m : ℕ) : (m + 1 == 0) = false := by simp

@[inherit_doc succ_beq_zero] theorem succ₂_beq_one (m : ℕ) : (m + 1 + 1 == 1) = false := by simp

@[inherit_doc succ_beq_zero] theorem succ₃_beq_two (m : ℕ) : (m + 1 + 1 + 1 == 2) = false := by
  simp

@[inherit_doc succ_beq_zero] theorem succ₄_beq_three (m : ℕ) :
    (m + 1 + 1 + 1 + 1 == 3) = false := by simp

/-- A list of two elements and more has not fewer than two. -/
theorem succ₂_lt_two (m : ℕ) : decide (m + 1 + 1 < 2) = false := by simp

/-- The position of a free variable of a level: zero where the level is not negative, and one
where it is. -/
def fpos (l : ℤ) : ℕ := if 0 ≤ l then 0 else 1

/-- The datum of a free variable of a level: the level where it is not negative, and otherwise the
index of the variable it denotes in the reduced term's context. -/
def fdat (l : ℤ) : Tree := if 0 ≤ l then leaf l.toNat else leaf (-l - 1).toNat

/-- The position of a free variable is none of the positions after the first two. -/
theorem fpos_beq (l : ℤ) (a : ℕ) : (fpos l == a + 2) = false := by
  unfold fpos
  split <;> simp

/-- The position of a free variable is below the positions after the first two. -/
theorem fpos_lt (l : ℤ) (a : ℕ) : decide (fpos l < a + 2) = true := by
  unfold fpos
  split <;> simp

/-- No position but the first is below the position of a free variable. -/
theorem lt_fpos (l : ℤ) (a : ℕ) : decide (a + 1 < fpos l) = false := by
  unfold fpos
  split <;> simp

/-! Values. -/

/-- The position of a value's label, and its data: a free variable of a level that is not
negative over the level, and of a negative level over the index of the variable it denotes in the
reduced term's context. -/
def vdata : VLabel → ℕ × List Tree
  | .free l => (fpos l, [fdat l])
  | .star => (2, [])
  | .pair => (3, [])
  | .clo a b k => (4, [a, encTerm b, leaf k])
  | .arr j θ => (5, [leaf j, RoseTree.node 0 θ])
  | .app => (6, [])
  | .fst => (7, [])
  | .snd => (8, [])
  | .natRec s k => (9, [encTerm s, leaf k])
  | .listRec s k => (10, [encTerm s, leaf k])
  | .roseRec c s k => (11, [c, encTerm s, leaf k])
  | .defn j θ => (12, [leaf j, RoseTree.node 0 θ])
  | .eq => (13, [])
  | .term t k => (14, [encTerm t, leaf k])
  | .delay => (15, [])
  | .fail => (16, [])

/-- A value as the node of its label's position over the node of the label's data and its
children. -/
def encVal : Val → Tree :=
  encWith (fun l ↦ (vdata l).1) fun l ↦ RoseTree.node 0 (vdata l).2

/-- The encoding of a node of a value. -/
theorem encVal_node (l : VLabel) (cs : List Val) :
    encVal (RoseTree.node l cs) = mk (vdata l).1 (vdata l).2 (cs.map encVal) :=
  encWith_node _ _ l cs

/-- The encoding of a value, by its label and its children. -/
theorem encVal_eq (v : Val) : encVal v = mk (vdata v.label).1 (vdata v.label).2
    (v.children.map encVal) := by
  conv_lhs => rw [← RoseTree.node_label_children v]
  exact encVal_node _ _

/-- The label of an encoded value. -/
@[simp] theorem label_encVal (v : Val) : (encVal v).label = (vdata v.label).1 := by
  rw [encVal_eq]
  rfl

/-- The node of the data of an encoded value's label. -/
@[simp] theorem child_encVal (v : Val) :
    Const.child (encVal v) (leaf 0) = RoseTree.node 0 (vdata v.label).2 := by
  rw [encVal_eq]
  rfl

/-- The mirror's children of an encoded value. -/
@[simp] theorem mArgs_encVal (v : Val) :
    «Language.mArgs» (encVal v) = v.children.map encVal := by
  rw [encVal_eq, mArgs_mk]

/-- The mirror's test of an encoded value's label and number of children. -/
@[simp] theorem mIs_encVal (a b : ℕ) (v : Val) :
    «Language.mIs» (leaf a) (leaf b) (encVal v) =
      ofBool ((vdata v.label).1 == a && v.children.length == b) := by
  rw [encVal_eq, mIs_mk, List.length_map]

/-- The mirror's child of an encoded value at a position. -/
@[simp] theorem mArg_encVal (v : Val) (i : ℕ) :
    «Language.mArg» (encVal v) (leaf i) = (v.children.map encVal).getD i (leaf 0) := by
  rw [encVal_eq, mArg_mk]

/-- The mirror's datum of an encoded value's label at a position. -/
@[simp] theorem mD_encVal (v : Val) (i : ℕ) :
    «Language.mD» (encVal v) (leaf i) = (vdata v.label).2.getD i (leaf 0) := by
  rw [encVal_eq, mD_mk]

/-- The simplification of the mirror's machine: the lemmas of {lit}`mirror_simp`, the accessors
of encoded terms and of nodes of a position, the lists of a few elements, and the given
lemmas. -/
local macro "mach_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  mirror_simp [mIs_eq, mArg_eq, mD_eq, mArgs_eq, label_encTerm, mNode_leaf, label_mk, child_mk,
    children_mk, mArgs_mk, mD_mk, mArg_mk, mIs_mk, l2_eq, l3_eq, l4_eq, l5_eq, l6_eq, none_eq,
    some_eq, List.getD_nil, List.isEmpty_cons, List.isEmpty_nil, List.head?_cons, List.head?_nil,
    List.tail_nil, List.drop_succ_cons, List.drop_zero, Nat.reduceLT, Nat.reduceEqDiff,
    decide_true, decide_false, succ_beq_zero, succ₂_beq_one, succ₃_beq_two, succ₄_beq_three,
    succ₂_lt_two, Option.bind_eq_bind, Option.pure_def, fpos_beq, fpos_lt, lt_fpos,
    label_encVal, child_encVal, mArgs_encVal, mIs_encVal, mArg_encVal, mD_encVal,
    $ls,*] $(loc)?)

/-- A normal form with its mark as the node of the term and the mark. -/
def encNF (p : Term × Bool) : Tree := RoseTree.node 0 [encTerm p.1, ofBool p.2]

/-- The mirror's value of a computation that does not reach one. -/
@[simp] theorem failV_eq : «Machine.failV» = encVal Internal.failV := rfl

/-- The mirror's delayed value of an optional value with its source. -/
theorem delayed_eq (o : Option Val) (src : Val) :
    «Machine.delayed» (encOpt (o.map encVal)) (encVal src) =
      encVal (Internal.vnode .delay [o.getD Internal.failV, src]) := by
  cases o <;> rfl

/-- The mirror's free variable of the level of the variable of an index past an environment
under a number of binders. -/
theorem freeVar_eq (k j : ℕ) :
    «Machine.freeVar» (leaf k) (leaf j) =
      encVal (Internal.vnode (.free ((k : ℤ) - 1 - (j : ℤ))) []) := by
  simp only [«Machine.freeVar», lt_leaf, sub_leaf, single_eq, mNode_leaf, ofBool_bne,
    label_ne_zero, decide_eq_true_eq, encVal_node, vdata, fpos, fdat, List.map_nil]
  by_cases h : j < k
  · have h0 : (0 : ℤ) ≤ (k : ℤ) - 1 - (j : ℤ) := by omega
    have h1 : ((k : ℤ) - 1 - (j : ℤ)).toNat = k - 1 - j := by omega
    simp only [h, h0, ↓reduceIte, h1]
  · have h0 : ¬ (0 : ℤ) ≤ (k : ℤ) - 1 - (j : ℤ) := by omega
    have h1 : (-((k : ℤ) - 1 - (j : ℤ)) - 1).toNat = j - k := by omega
    simp only [h, h0, ↓reduceIte, h1]

/-- The mirror's free variable of the level of a binder. -/
theorem level_eq (k : ℕ) :
    «Machine.level» (leaf k) = encVal (Internal.vnode (.free (k : ℤ)) []) := by
  have h0 : (0 : ℤ) ≤ (k : ℤ) := by omega
  simp only [«Machine.level», single_eq, mNode_leaf, encVal_node, vdata, fpos, fdat, h0,
    ↓reduceIte, Int.toNat_natCast, List.map_nil]

/-! Reading back. -/

/-- The mirror's substitution an environment of encoded terms stands for. -/
theorem envSubst_eq (ts : List Term) (k i : ℕ) :
    «Machine.envSubst» (ts.map encTerm) (leaf k) (leaf i) =
      encTerm (Internal.envSubst ts k i) := by
  simp only [«Machine.envSubst», length_eq, List.length_map, lt_leaf, sub_leaf, add_leaf, at_eq,
    mVar_eq, ofBool_bne, label_ne_zero, decide_eq_true_eq, Internal.envSubst]
  by_cases h : i < ts.length
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h]

/-- The mirror's lifting of a substitution under a binder, at a substitution of encoded terms for
leaves. -/
theorem liftS_eq (σ : Tree → Tree) (σ' : ℕ → Term) (hσ : ∀ i, σ (leaf i) = encTerm (σ' i))
    (i : ℕ) : «Language.liftS» σ (leaf i) = encTerm (Term.liftS σ' i) := by
  cases i with
  | zero => rfl
  | succ j =>
    mirror_simp [«Language.liftS», Internal.Term.liftS, hσ]
    exact rename_eq _ _ _ fun i ↦ by mirror_simp []

/-- The node of a term's label over its data and encoded children is the encoded node. -/
theorem mk_encTerm (l : Label) (ts : List Term) :
    mk (labelData l).1 (labelData l).2 (ts.map encTerm) = encTerm (RoseTree.node l ts) :=
  (encTerm_node l ts).symm

/-- The mirror's substitution by an environment of encoded terms lifted under a binder. -/
theorem subst_liftS_envSubst (s : Term) (ts : List Term) (k : ℕ) :
    «Language.subst» (encTerm s)
        (fun x ↦ «Language.liftS» («Machine.envSubst» (ts.map encTerm) (leaf k)) x) =
      encTerm (Term.subst s (Term.liftS (Internal.envSubst ts k))) :=
  subst_eq _ _ _ fun i ↦ liftS_eq _ _ (envSubst_eq ts k) i

/-- The mirror's substitution by an environment of encoded terms lifted under two binders. -/
theorem subst_liftS₂_envSubst (s : Term) (ts : List Term) (k : ℕ) :
    «Language.subst» (encTerm s) (fun x ↦ «Language.liftS»
        (fun y ↦ «Language.liftS» («Machine.envSubst» (ts.map encTerm) (leaf k)) y) x) =
      encTerm (Term.subst s (Term.liftS (Term.liftS (Internal.envSubst ts k)))) :=
  subst_eq _ _ _ fun i ↦ liftS_eq _ _ (fun j ↦ liftS_eq _ _ (envSubst_eq ts k) j) i

/-- The mirror's step of the reading back of a value to a term under a number of binders, at a
node of a label's position and data from its children's encoded terms. -/
theorem readStep_eq (D : ℕ) (l : VLabel) (X : List Tree) (ts : List Term) :
    «Machine.readStep» (leaf D) (mk (vdata l).1 (vdata l).2 X) (ts.map encTerm) =
      encTerm (Internal.readStep D l ts) := by
  have hpl : ∀ (l' : Label), mk (labelData l').1 (labelData l').2 (ts.map encTerm) =
      encTerm (RoseTree.node l' ts) := fun l' ↦ mk_encTerm l' ts
  cases l with
  | free l =>
    by_cases h : 0 ≤ l
    · have h1 : ((D : ℤ) - 1 - l).toNat = D - 1 - l.toNat := by omega
      mirror_simp [«Machine.readStep», label_mk, vdata, fpos, fdat, h, mD_mk, mVar_eq,
        Internal.readStep, h1]
    · have h1 : ((D : ℤ) - 1 - l).toNat = D + (-l - 1).toNat := by omega
      mirror_simp [«Machine.readStep», label_mk, vdata, fpos, fdat, h, mD_mk, mVar_eq,
        Internal.readStep, h1]
  | star => mirror_simp [«Machine.readStep», label_mk, vdata, mStar_eq, Internal.readStep]
  | pair => mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
            exact hpl .pair
  | clo a b k =>
    mirror_simp [«Machine.readStep», label_mk, vdata, mD_mk, mLam_eq, subst_liftS_envSubst,
      Internal.readStep]
  | arr j θ =>
    mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, child_mk, Internal.readStep]
    exact hpl (.arr j θ)
  | app => mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
           exact hpl .app
  | fst => mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
           exact hpl .fst
  | snd => mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
           exact hpl .snd
  | natRec s k =>
    rcases ts with _ | ⟨z, _ | ⟨m, cs⟩⟩
    · mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
      exact hpl .natRec
    · mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
      exact hpl .natRec
    · have hlen : ¬ cs.length + 1 + 1 < 2 := by omega
      mirror_simp [«Machine.readStep», label_mk, vdata, mD_mk, Internal.readStep,
        List.drop_succ_cons, List.drop_zero, mNatRec_eq, subst_liftS_envSubst, hlen,
        decide_false]
  | listRec s k =>
    rcases ts with _ | ⟨z, _ | ⟨m, cs⟩⟩
    · mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
      exact hpl .listRec
    · mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
      exact hpl .listRec
    · have hlen : ¬ cs.length + 1 + 1 < 2 := by omega
      mirror_simp [«Machine.readStep», label_mk, vdata, mD_mk, Internal.readStep,
        List.drop_succ_cons, List.drop_zero, mListRec_eq, subst_liftS₂_envSubst, hlen,
        decide_false]
  | roseRec c s k =>
    rcases ts with _ | ⟨m, cs⟩
    · mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, mD_mk, Internal.readStep]
      exact hpl (.roseRec c)
    · mirror_simp [«Machine.readStep», label_mk, vdata, mD_mk, Internal.readStep, mRoseRec_eq,
        subst_liftS_envSubst, List.isEmpty_cons]
  | defn j θ =>
    mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, child_mk, Internal.readStep]
    exact hpl (.defn j θ)
  | eq => mirror_simp [«Machine.readStep», label_mk, vdata, mNode_leaf, Internal.readStep]
          exact hpl .eq
  | term t k =>
    mirror_simp [«Machine.readStep», label_mk, vdata, mD_mk, Internal.readStep]
    exact subst_eq _ _ _ (envSubst_eq ts (D - k))
  | delay =>
    have hlen : ∀ m : ℕ, ¬ m + 1 + 1 + 1 = 2 := fun m ↦ by omega
    rcases ts with _ | ⟨a, _ | ⟨c, _ | ⟨e, cs⟩⟩⟩ <;>
      mirror_simp [«Machine.readStep», label_mk, vdata, mStar_eq, Internal.readStep, beq_iff_eq,
        hlen]
  | fail => mirror_simp [«Machine.readStep», label_mk, vdata, mStar_eq, Internal.readStep]

/-- The mirror's reading back of an encoded value to a term under a number of binders. -/
theorem readBack_eq (D : ℕ) : ∀ v : Val,
    «Machine.readBack» (leaf D) (encVal v) = encTerm (Internal.readBack D v) :=
  RoseTree.ind fun l cs ih ↦ by
    simp only [«Machine.readBack»] at ih ⊢
    rw [encVal_node, mk, Const.para_node, List.map_cons, tail_eq, List.tail_cons, List.map_map,
      Internal.readBack_node]
    have h : cs.map (Const.para (fun x2 x3 ↦ «Machine.readStep» (leaf D) x2 («Prelude.tail» x3)) ∘
        encVal) = (cs.map (Internal.readBack D)).map encTerm := by
      rw [List.map_map]
      exact List.map_congr_left fun c hc ↦ ih c hc
    rw [h]
    exact readStep_eq D l _ _

/-- The mirror's test whether each variable of an encoded term is a leaf. -/
theorem varLeaves_eq : ∀ t : Term,
    «Machine.varLeaves» (encTerm t) = ofBool (Term.VarLeaves t) :=
  RoseTree.ind fun l cs ih ↦ by
    simp only [«Machine.varLeaves»] at ih ⊢
    rw [encTerm_node, Const.para_node, List.map_cons, tail_eq, List.tail_cons, List.map_map]
    have h : cs.map (Const.para (fun x1 x2 ↦ «Prelude.and»
        (if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
          «Base.isEmpty» («Prelude.tail» x2) else leaf 1)
        («Base.allT» (fun x3 ↦ x3) («Prelude.tail» x2))) ∘ encTerm) =
        cs.map fun c ↦ ofBool (Term.VarLeaves c) :=
      List.map_congr_left fun c hc ↦ ih c hc
    rw [h]
    have ha : «Base.allT» (fun x3 ↦ x3) (cs.map fun c ↦ ofBool (Term.VarLeaves c)) =
        ofBool (cs.all Term.VarLeaves) :=
      allT_map (fun x ↦ x) (fun c ↦ ofBool (Term.VarLeaves c)) Term.VarLeaves cs fun _ _ ↦ rfl
    rw [ha]
    have hv : Term.VarLeaves (RoseTree.node l cs) =
        ((match l with | .var _ => (cs.map Term.VarLeaves).isEmpty | _ => true) &&
          (cs.map Term.VarLeaves).all id) := RoseTree.elim_node _ l cs
    rw [hv]
    have hand : ∀ b : Bool, «Prelude.and» (leaf 1) (ofBool b) = ofBool b := fun b ↦
      (and_eq true b).trans (by rw [Bool.true_and])
    cases l with
    | var i =>
      simp only [labelData, label_eq, RoseTree.label_node, eq_leaf, ofBool_bne, label_ne_zero,
        beq_self_eq_true, ↓reduceIte, isEmpty_eq, and_eq, List.all_map, List.isEmpty_map,
        Function.comp_def, id]
    | _ =>
      simp only [labelData, label_eq, RoseTree.label_node, eq_leaf, ofBool_bne, label_ne_zero,
        Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, hand, List.all_map, Function.comp_def, id,
        Bool.true_and]

/-! The machine applied to lists of jobs. -/

/-- The parameters of the mirror's machine: the constants, the number of object variables, the
predicate selecting the definitions unfolded, the indices of the primitives of lists, and the
rewriting at a root of a normal form. -/
structure Params where
  /-- The constants. -/
  G : Tree
  /-- The number of object variables. -/
  n : Tree
  /-- The predicate selecting the definitions unfolded. -/
  unf : Tree → Tree
  /-- The index of the primitive of the empty list. -/
  kl : Tree
  /-- The index of the primitive of a list's construction. -/
  kc : Tree
  /-- The rewriting at a root of a normal form. -/
  rw : List Tree → Tree → Tree → Tree

/-- The mirror's first results, as many as the jobs, and the results after them. -/
theorem splitRs_eq (F : Tree → Tree) :
    ∀ (qs rest : List Tree), «Machine.splitRs» qs (qs.map F ++ rest) = (qs.map F, rest) := by
  simp only [«Machine.splitRs», foldr_eq]
  exact List.rec (fun _ ↦ rfl) fun q qs ih rest ↦ by
    simp only [List.foldr_cons, List.map_cons, List.cons_append, lcase_cons, ih]

/-- The jobs every state of a list waits for. -/
def needs (ss : List Tree) : List Tree :=
  ss.foldr (fun s acc ↦ «Language.mArgs» s ++ acc) []

/-- A state advanced by the results a function of its jobs gives. -/
def advBy (P : Params) (F : Tree → Tree) (s : Tree) : Tree :=
  «Machine.msAdv» P.G P.n P.unf P.kl P.kc P.rw s ((«Language.mArgs» s).map F)

/-- A round of the mirror, at a level below that is the image of a function of its jobs, advances
each state by that function's results. -/
theorem msRound_eq (P : Params) (F : Tree → Tree) (rec : List Tree → List Tree)
    (hrec : ∀ js, rec js = js.map F) (ss : List Tree) :
    «Machine.msRound» P.G P.n P.unf P.kl P.kc P.rw rec ss = ss.map (advBy P F) := by
  have h : ∀ (xs : List Tree) (rest : List Tree),
      List.foldr (fun (s : Tree) (k : List Tree → List Tree) (x : List Tree) ↦
          «Machine.msAdv» P.G P.n P.unf P.kl P.kc P.rw s
              («Machine.splitRs» («Language.mArgs» s) x).1 ::
            k («Machine.splitRs» («Language.mArgs» s) x).2)
        (fun _ ↦ []) xs ((needs xs).map F ++ rest) = xs.map (advBy P F) :=
    List.rec (fun _ ↦ rfl) fun s xs ih rest ↦ by
      simp only [needs, List.foldr_cons, List.map_append, List.append_assoc, List.map_cons,
        splitRs_eq, advBy]
      exact congrArg _ (ih rest)
  have h2 := h ss []
  rw [List.append_nil] at h2
  simp only [«Machine.msRound», foldr_eq, hrec, append_eq]
  exact h2

/-- The mirror's result of a job within a depth of recursion, as the rounds of the state the job
starts in, each level's jobs computed by the level below; no job has a result at the depth
zero. -/
def machJ (P : Params) (fuel : ℕ) : Tree → Tree :=
  Nat.rec (fun _ ↦ «Prelude.none»)
    (fun _ F j ↦ «Machine.msResult» ((advBy P F)^[6] («Machine.msStart» j))) fuel

/-- A function iterated six times. -/
theorem iterate_six {α : Type} (f : α → α) (s : α) : f^[6] s = f (f (f (f (f (f s))))) := rfl

/-- A level of the mirror, at a level below that is the image of a function of its jobs, is the
image of the rounds of the state each job starts in. -/
theorem machStepB_eq (P : Params) (F : Tree → Tree) (rec : List Tree → List Tree)
    (hrec : ∀ js, rec js = js.map F) (js : List Tree) :
    «Machine.machStepB» P.G P.n P.unf P.kl P.kc P.rw rec js =
      js.map fun j ↦ «Machine.msResult» ((advBy P F)^[6] («Machine.msStart» j)) := by
  rcases js with _ | ⟨j, js⟩
  · rfl
  · simp only [«Machine.machStepB», lcase_cons, msRound_eq P F rec hrec, mapT_eq, List.map_map,
      Function.comp_def, iterate_six]

/-- The mirror's machine within a depth of recursion, at a list of jobs, is the image of the
result of a job. -/
theorem machB_eq (P : Params) (fuel : ℕ) :
    ∀ js, «Machine.machB» P.G P.n P.unf P.kl P.kc P.rw (leaf fuel) js =
      js.map (machJ P fuel) := by
  simp only [«Machine.machB», iter_leaf]
  exact Nat.rec (fun js ↦ by
      simp only [Nat.repeat, mapT_eq]
      rfl)
    (fun m ih js ↦ by
      simp only [Nat.repeat]
      exact machStepB_eq P _ _ ih js) fuel

/-! States and their rounds. -/

/-- The mirror's finished state of a result. -/
theorem msDone_eq (R : Tree) : «Machine.msDone» R = mk 0 [R] [] := rfl

/-- The mirror's state waiting for a job whose result is its own. -/
theorem msTail_eq (j : Tree) : «Machine.msTail» j = mk 1 [] [j] := rfl

/-- The mirror's state waiting for a job whose result's weak head normal form is its own. -/
theorem msWhnf_eq (j : Tree) : «Machine.msWhnf» j = mk 2 [] [j] := rfl

/-- The mirror's result of a finished state. -/
theorem msResult_done (R : Tree) : «Machine.msResult» («Machine.msDone» R) = R := by
  mirror_simp [«Machine.msResult», msDone_eq, label_mk, mD_mk]

/-- The mirror's state a present optional tree continues in. -/
theorem bindS_some (x : Tree) (f : Tree → Tree) :
    «Machine.bindS» (encOpt (some x)) f = f x := by
  mirror_simp [«Machine.bindS»]

/-- The mirror's state an absent optional tree continues in: finished without a result. -/
theorem bindS_none (f : Tree → Tree) :
    «Machine.bindS» (encOpt none) f = «Machine.msDone» (encOpt none) := by
  mirror_simp [«Machine.bindS»]
  rfl

/-- A state's reaching a result within a number of rounds. -/
def Reach (P : Params) (F : Tree → Tree) (m : ℕ) (s R : Tree) : Prop :=
  (advBy P F)^[m] s = «Machine.msDone» R

section Reach

variable {P : Params} {F : Tree → Tree}

/-- A finished state stays so. -/
theorem advBy_done (R : Tree) : advBy P F («Machine.msDone» R) = «Machine.msDone» R := by
  mirror_simp [advBy, «Machine.msAdv», msDone_eq, label_mk]

/-- A finished state has reached its result. -/
theorem reach_done (m : ℕ) (R : Tree) : Reach P F m («Machine.msDone» R) R :=
  Function.iterate_fixed (advBy_done R) m

/-- A state reaches a result within a round more than what it advances to. -/
theorem reach_step {m : ℕ} {s s' R : Tree} (h : advBy P F s = s') (hs : Reach P F m s' R) :
    Reach P F (m + 1) s R := by
  subst h
  exact hs

/-- A state that reaches a result reaches it within more rounds. -/
theorem reach_mono {m : ℕ} {s R : Tree} (h : Reach P F m s R) : Reach P F (m + 1) s R := by
  simp only [Reach, Function.iterate_succ_apply'] at h ⊢
  rw [h, advBy_done]

/-- A state that reaches a result reaches it within any greater number of rounds. -/
theorem reach_le {m m' : ℕ} {s R : Tree} (h : Reach P F m s R) (hm : m ≤ m') :
    Reach P F m' s R := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact Nat.rec h (fun _ ih ↦ reach_mono ih) d

/-- The result of a job whose state reaches a result within six rounds. -/
theorem result_of_reach {m : ℕ} {s R : Tree} (h : Reach P F m s R) (hm : m ≤ 6) :
    «Machine.msResult» ((advBy P F)^[6] s) = R := by
  rw [reach_le h hm, msResult_done]

/-- A state waiting for a job whose result is its own reaches that result in a round. -/
theorem reach_tail (j : Tree) : Reach P F 1 («Machine.msTail» j) (F j) := by
  simp only [Reach, Function.iterate_one]
  mirror_simp [advBy, «Machine.msAdv», msTail_eq, label_mk, mArgs_mk]

end Reach

/-! Jobs, and the states' dispatch. -/

/-- The encoded job of the evaluation of a term in an environment past which its variables are
those under a number of binders. -/
def encJobE (t : Term) (vs : List Val) (k : ℕ) : Tree :=
  mk 0 [encTerm t, leaf k] (vs.map encVal)

/-- The encoded job of the weak head normal form of an optional value. -/
def encJobW (ov : Option Val) : Tree := mk 1 [encOpt (ov.map encVal)] []

/-- The encoded job of the normal form of an optional value's term in a context under a number of
binders. -/
def encJobN (Γ : List Tree) (k : ℕ) (ov : Option Val) : Tree :=
  mk 2 [leaf k, encOpt (ov.map encVal)] Γ

/-- The mirror's job of an evaluation at encoded arguments. -/
theorem jobE_eq (t : Term) (vs : List Val) (k : ℕ) :
    «Machine.jobE» (encTerm t) (vs.map encVal) (leaf k) = encJobE t vs k := rfl

/-- The mirror's job of a weak head normal form at an encoded optional value. -/
theorem jobW_eq (ov : Option Val) : «Machine.jobW» (encOpt (ov.map encVal)) = encJobW ov := rfl

/-- The mirror's job of a normal form at encoded arguments. -/
theorem jobN_eq (Γ : List Tree) (k : ℕ) (ov : Option Val) :
    «Machine.jobN» Γ (leaf k) (encOpt (ov.map encVal)) = encJobN Γ k ov := rfl

/-- A function of the mirror's jobs is related to the machine's operations at a depth when it
gives, at each encoded job, the encoding of the operation's result: the value of a term, the weak
head normal form of an optional value, and the normal form of an optional value's term with its
mark. -/
structure JRel (F : Tree → Tree) (o : Machine) : Prop where
  /-- The function at a job of evaluation. -/
  eval : ∀ t vs k, F (encJobE t vs k) = encOpt ((o.eval t vs k).map encVal)
  /-- The function at a job of a weak head normal form. -/
  whnf : ∀ ov, F (encJobW ov) = encOpt ((ov.bind o.whnf).map encVal)
  /-- The function at a job of a normal form. -/
  nf : ∀ Γ k ov, F (encJobN Γ k ov) = encOpt ((ov.bind (o.nf Γ k)).map encNF)

section Dispatch

variable {P : Params} {F : Tree → Tree}

/-- A state waiting for a job whose result's weak head normal form is its own advances to waiting
for that weak head normal form. -/
theorem adv_whnf (j : Tree) :
    advBy P F («Machine.msWhnf» j) = «Machine.msTail» («Machine.jobW» (F j)) := by
  mirror_simp [advBy, «Machine.msAdv», msWhnf_eq, label_mk, mArgs_mk]

/-- The state of each position advances by its own function of its data and its jobs'
results. -/
theorem adv3 (j : Tree) (js : List Tree) :
    advBy P F (mk 3 [j] js) = «Machine.eArgs» j (js.map F) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv4 (j r : Tree) (ws : List Tree) :
    advBy P F (mk 4 [j, r] ws) =
      «Machine.eFinal» P.G P.unf j r («Machine.eDelays» j (ws.map F)) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv5 (v j : Tree) :
    advBy P F (mk 5 [v] [j]) =
      «Machine.bindS» (F j) fun h ↦ «Machine.wHead» P.G P.kl P.kc v h := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv6 (f1 j : Tree) :
    advBy P F (mk 6 [f1] [j]) = «Machine.bindS» (F j) fun u1 ↦ «Machine.wCase» P.G f1 u1 := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv7 (f1 u1 j : Tree) :
    advBy P F (mk 7 [f1, u1] [j]) =
      «Machine.bindS» (F j) fun p1 ↦ «Machine.wCase2» P.G f1 u1 p1 := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv8 (v m1 j : Tree) :
    advBy P F (mk 8 [v, m1] [j]) = «Machine.bindS» (F j) fun c1 ↦ «Machine.wBase» v m1 c1 := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv9 (v m1 j : Tree) :
    advBy P F (mk 9 [v, m1] [j]) = «Machine.bindS» (F j) fun c1 ↦ «Machine.wCons» v m1 c1 := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv10 (v m1 j : Tree) :
    advBy P F (mk 10 [v, m1] [j]) =
      «Machine.bindS» (F j) fun p1 ↦ «Machine.wRose2» P.kl P.kc v m1 p1 := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv11 (d : List Tree) (j : Tree) :
    advBy P F (mk 11 d [j]) = «Machine.wRec» d (F j) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, child_mk]

@[inherit_doc adv3] theorem adv12 (g : List Tree) (k j : Tree) :
    advBy P F (mk 12 [RoseTree.node 0 g, k] [j]) =
      «Machine.bindS» (F j) fun w ↦ «Machine.nNode» P.rw g k w := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv13 (g : List Tree) (k w : Tree) (js : List Tree) :
    advBy P F (mk 13 [RoseTree.node 0 g, k, w] js) =
      «Machine.nFold» P.G P.n g k w (js.map F) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv14 (d : List Tree) (j : Tree) :
    advBy P F (mk 14 d [j]) = «Machine.nBody» d (F j) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, child_mk]

@[inherit_doc adv3] theorem adv15 (d : List Tree) (j : Tree) :
    advBy P F (mk 15 d [j]) = «Machine.bindS» (F j) fun x ↦ «Machine.nDone» P.rw d x := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, child_mk]

@[inherit_doc adv3] theorem adv16 (g : List Tree) (k w : Tree) (js : List Tree) :
    advBy P F (mk 16 [RoseTree.node 0 g, k, w] js) = «Machine.nKids» P.rw g k w (js.map F) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk]

@[inherit_doc adv3] theorem adv17 (g : List Tree) (k j : Tree) :
    advBy P F (mk 17 [RoseTree.node 0 g, k] [j]) = mk 18 [] [«Machine.jobN» g k (F j)] := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk, mD_mk, mNode_leaf]

@[inherit_doc adv3] theorem adv18 (j : Tree) :
    advBy P F (mk 18 [] [j]) = «Machine.msDone»
      («Base.bindO» (F j) fun x ↦ «Machine.marked» («Machine.nfTerm» x) (leaf 1)) := by
  mirror_simp [advBy, «Machine.msAdv», label_mk, mArgs_mk]

end Dispatch

/-! The evaluation of a term. -/

/-- The images of a list's positions under a function of the elements of two images of the list
at each position are the images of its elements. -/
theorem map_range_getD {α : Type} (xs : List α) (a b : α → Tree) (g : Tree → Tree → Tree)
    (d₁ d₂ : Tree) :
    (List.range xs.length).map (fun i ↦ g ((xs.map a).getD i d₁) ((xs.map b).getD i d₂)) =
      xs.map fun x ↦ g (a x) (b x) :=
  List.ext_getElem (by simp) fun i h₁ h₂ ↦ by
    have hi : i < xs.length := by simpa using h₂
    simp [List.getD_eq_getElem?_getD, hi]

section Eval

variable {P : Params} {F : Tree → Tree} {o : Machine}

/-- The encoding of the delayed value of a term in an environment. -/
theorem encVal_delay (o : Machine) (u : Term) (vs : List Val) (k : ℕ) :
    encVal (o.delay u vs k) =
      «Machine.delayed» (encOpt (((o.eval u vs k).bind o.whnf).map encVal))
        (mk 14 [encTerm u, leaf k] (vs.map encVal)) := by
  have h : encVal (Internal.vnode (.term u k) vs) = mk 14 [encTerm u, leaf k] (vs.map encVal) :=
    encVal_node _ _
  rw [Internal.Machine.delay_eq, ← h]
  exact (delayed_eq _ _).symm

/-- A state waiting for the weak head normal form of an optional value reaches it in a round. -/
theorem reach_tailW (hF : JRel F o) (ov : Option Val) :
    Reach P F 1 («Machine.msTail» («Machine.jobW» (encOpt (ov.map encVal))))
      (encOpt ((ov.bind o.whnf).map encVal)) := by
  rw [jobW_eq, ← hF.whnf]
  exact reach_tail _

/-- A state waiting for the value of a term, whose weak head normal form is its result, reaches
that weak head normal form in two rounds. -/
theorem reach_whnfE (hF : JRel F o) (t : Term) (vs : List Val) (k : ℕ) :
    Reach P F 2 («Machine.msWhnf» (encJobE t vs k))
      (encOpt (((o.eval t vs k).bind o.whnf).map encVal)) := by
  refine reach_step (adv_whnf _) ?_
  rw [hF.eval]
  exact reach_tailW hF _

/-- The mirror's state of an evaluation after the values of its subterms: waiting for the weak
head normal forms of those delayed, beside the optional value of the one the node reduces by. -/
theorem eArgs_eq (hF : JRel F o) (t : Term) (vs : List Val) (k : ℕ) (b : Bool) (ks : List Term)
    (hs : «Machine.eHasStrict» (encTerm t) = ofBool b) :
    «Machine.eArgs» (encJobE t vs k) ((ks.map fun u ↦ encJobE u vs k).map F) =
      mk 4 [encJobE t vs k,
          if b then encOpt ((ks.head?.bind fun p ↦ o.eval p vs k).map encVal) else encOpt none]
        ((if b then ks.tail else ks).map fun u ↦
          «Machine.jobW» (encOpt ((o.eval u vs k).map encVal))) := by
  have hm : (ks.map fun u ↦ encJobE u vs k).map F =
      ks.map fun u ↦ encOpt ((o.eval u vs k).map encVal) := by
    rw [List.map_map]
    exact List.map_congr_left fun u _ ↦ hF.eval u vs k
  rw [hm]
  cases b
  · mach_simp [«Machine.eArgs», encJobE, hs]
  · rcases ks with _ | ⟨p, ds⟩
    · mach_simp [«Machine.eArgs», encJobE, hs]
      rfl
    · mach_simp [«Machine.eArgs», encJobE, hs]

/-- The mirror's delayed values of the subterms an evaluation delays, at the weak head normal
forms of their values. -/
theorem eDelays_eq (hF : JRel F o) (t : Term) (vs : List Val) (k : ℕ) (ds : List Term)
    (hd : «Machine.eDelayed» (encTerm t) = ds.map encTerm) :
    «Machine.eDelays» (encJobE t vs k)
        ((ds.map fun u ↦ «Machine.jobW» (encOpt ((o.eval u vs k).map encVal))).map F) =
      (ds.map fun u ↦ o.delay u vs k).map encVal := by
  have hm : (ds.map fun u ↦ «Machine.jobW» (encOpt ((o.eval u vs k).map encVal))).map F =
      ds.map fun u ↦ encOpt (((o.eval u vs k).bind o.whnf).map encVal) := by
    rw [List.map_map]
    exact List.map_congr_left fun u _ ↦ by
      rw [Function.comp_apply, jobW_eq, hF.whnf]
  rw [hm]
  mach_simp [«Machine.eDelays», encJobE, hd]
  rw [map_range_getD ds (fun u ↦ encOpt (((o.eval u vs k).bind o.whnf).map encVal)) encTerm
    (fun a b ↦ «Machine.delayed» a (mk 14 [b, leaf k] (vs.map encVal)))]
  exact List.map_congr_left fun u _ ↦ (encVal_delay o u vs k).symm

/-- Two rounds of the state of an evaluation waiting for its subterms' values bring it to the
state of its term's node, at the optional value of the subterm it reduces by and the delayed
values of the others. -/
theorem eRounds (hF : JRel F o) (t : Term) (vs : List Val) (k : ℕ) (b : Bool) (ks : List Term)
    (hs : «Machine.eHasStrict» (encTerm t) = ofBool b)
    (hk : «Machine.eKids» (encTerm t) = ks.map encTerm) :
    advBy P F (advBy P F (mk 3 [encJobE t vs k] (ks.map fun u ↦ encJobE u vs k))) =
      «Machine.eFinal» P.G P.unf (encJobE t vs k)
        (if b then encOpt ((ks.head?.bind fun p ↦ o.eval p vs k).map encVal) else encOpt none)
        (((if b then ks.tail else ks).map fun u ↦ o.delay u vs k).map encVal) := by
  have hd : «Machine.eDelayed» (encTerm t) = (if b then ks.tail else ks).map encTerm := by
    cases b <;> mach_simp [«Machine.eDelayed», hs, hk, List.map_tail]
  rw [adv3, eArgs_eq hF t vs k b ks hs, adv4, eDelays_eq hF t vs k _ hd]

/-- The mirror's state an evaluation of a term other than a variable, the element of the terminal
type and an abstraction starts in: waiting for the values of the subterms it evaluates. -/
theorem eStart_kids (t : Term) (vs : List Val) (k : ℕ) (ks : List Term)
    (hk : «Machine.eKids» (encTerm t) = ks.map encTerm)
    (h0 : (labelData t.label).1 ≠ 0)
    (h1 : ¬ ((labelData t.label).1 = 1 ∧ t.children.length = 0))
    (h5 : ¬ ((labelData t.label).1 = 5 ∧ t.children.length = 1)) :
    «Machine.eStart» (encJobE t vs k) = mk 3 [encJobE t vs k] (ks.map fun u ↦ encJobE u vs k) := by
  have h1' : ((labelData t.label).1 == 1 && t.children.isEmpty) = false := by
    simpa [Bool.and_eq_true, List.isEmpty_iff_length_eq_zero] using h1
  have h5' : ((labelData t.label).1 == 5 && t.children.length == 1) = false := by
    simpa [Bool.and_eq_true] using h5
  mach_simp [«Machine.eStart», encJobE, h0, h1', h5', beq_iff_eq, hk, «Machine.jobE»]

/-- The mirror's parameters are related to the machine's when they are the encodings of the
constants, of the number of object variables and of the indices of the primitives of lists, its
predicate gives the truth value of the machine's at each index, and its rewriting the encoding of
the machine's result at each context, number of binders and encoded term. -/
structure PRel (P : Params) (G : Internal.Globals) (n : ℕ) (unfold : ℕ → Bool) (kl kc : ℕ)
    (rw : List Tree → ℕ → Term → Option Term) : Prop where
  /-- The constants. -/
  G_eq : P.G = encGlobals G
  /-- The number of object variables. -/
  n_eq : P.n = leaf n
  /-- The predicate selecting the definitions unfolded. -/
  unf_eq : ∀ j, P.unf (leaf j) = ofBool (unfold j)
  /-- The index of the primitive of the empty list. -/
  kl_eq : P.kl = leaf kl
  /-- The index of the primitive of a list's construction. -/
  kc_eq : P.kc = leaf kc
  /-- The rewriting at a root of a normal form. -/
  rw_eq : ∀ Γ k t, P.rw Γ (leaf k) (encTerm t) = encOpt ((rw Γ k t).map encTerm)

variable {G : Internal.Globals} {n : ℕ} {unfold : ℕ → Bool} {kl kc : ℕ}
  {rw : List Tree → ℕ → Term → Option Term}

/-- The state an evaluation starts in reaches a result within three rounds when the state of its
term's node reaches it in one. -/
theorem eStart_final (hF : JRel F o) (t : Term) (vs : List Val) (k : ℕ) (b : Bool)
    (ks : List Term) (hs : «Machine.eHasStrict» (encTerm t) = ofBool b)
    (hk : «Machine.eKids» (encTerm t) = ks.map encTerm)
    (h0 : (labelData t.label).1 ≠ 0)
    (h1 : ¬ ((labelData t.label).1 = 1 ∧ t.children.length = 0))
    (h5 : ¬ ((labelData t.label).1 = 5 ∧ t.children.length = 1)) {R : Tree}
    (h : Reach P F 1 («Machine.eFinal» P.G P.unf (encJobE t vs k)
        (if b then encOpt ((ks.head?.bind fun p ↦ o.eval p vs k).map encVal) else encOpt none)
        (((if b then ks.tail else ks).map fun u ↦ o.delay u vs k).map encVal)) R) :
    Reach P F 3 («Machine.eStart» (encJobE t vs k)) R := by
  rw [eStart_kids t vs k ks hk h0 h1 h5]
  refine reach_step rfl (reach_step rfl ?_)
  rw [eRounds hF t vs k b ks hs hk]
  exact h

/-- The state of the application of a definition, at the delayed values of its arguments,
reaches the evaluation's result in a round. -/
theorem evalDefn_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (j : ℕ) (θ : List Tree)
    (ts : List Term) (vs : List Val) (k : ℕ) :
    Reach P F 1 («Machine.evalDefn» P.G P.unf ((ts.map fun u ↦ o.delay u vs k).map encVal)
        (encTerm (RoseTree.node (.defn j θ) ts)) (leaf k))
      (encOpt ((Machine.evalStep G unfold o (RoseTree.node (.defn j θ) ts) vs k).map encVal)) := by
  have hm : ts.map (fun u ↦ encVal (o.delay u vs k)) =
      (ts.map fun u ↦ o.delay u vs k).map encVal := (List.map_map ..).symm
  have hstuck : mk 12 [leaf j, RoseTree.node 0 θ] (ts.map fun u ↦ encVal (o.delay u vs k)) =
      encVal (Internal.vnode (.defn j θ) (ts.map fun u ↦ o.delay u vs k)) := by
    rw [hm]
    exact (encVal_node (.defn j θ) _).symm
  simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node]
  rw [hP.G_eq]
  rcases hj : unfold j with _ | _
  · mach_simp [«Machine.evalDefn», labelData, child_encTerm, hP.unf_eq, hj, hstuck]
    exact reach_done _ _
  · rcases hk : G.defs[j]? with _ | (d | ⟨m, b⟩)
    · mach_simp [«Machine.evalDefn», labelData, child_encTerm, hP.unf_eq, hj, hstuck, gDefs_eq, hk]
      exact reach_done _ _
    · by_cases hlen : ts.length = d.params.length
      · mach_simp [«Machine.evalDefn», labelData, child_encTerm, hP.unf_eq, hj, hstuck, gDefs_eq,
          hk, defLanguage_eq, Internal.Definition.language?, ldParams_eq, ldBody_eq, hlen,
          osubst_eq]
        have hb : (if θ.isEmpty = true then encTerm d.body
            else encTerm (Term.osubst θ d.body)) =
            encTerm (if θ.isEmpty then d.body else Term.osubst θ d.body) := by
          split <;> rfl
        rw [hb, hm, jobE_eq, ← hF.eval]
        exact reach_tail _
      · mach_simp [«Machine.evalDefn», labelData, child_encTerm, hP.unf_eq, hj, hstuck, gDefs_eq,
          hk, defLanguage_eq, Internal.Definition.language?, ldParams_eq, hlen, beq_iff_eq]
        exact reach_done _ _
    · mach_simp [«Machine.evalDefn», labelData, child_encTerm, hP.unf_eq, hj, hstuck, gDefs_eq,
        hk, defLanguage_eq, Internal.Definition.language?]
      exact reach_done _ _

/-- A state waiting for the weak head normal form of the image of an optional value, each image
the encoding of a value, reaches it in a round. -/
theorem reach_tailW_map (hF : JRel F o) (ov : Option Val) (f : Val → Val) (g : Val → Tree)
    (hfg : ∀ x, g x = encVal (f x)) :
    Reach P F 1 («Machine.msTail» («Machine.jobW» (encOpt (ov.map g))))
      (encOpt ((ov.bind fun x ↦ o.whnf (f x)).map encVal)) := by
  have h := reach_tailW (P := P) hF (ov.map f)
  have hg : g = fun x ↦ encVal (f x) := funext hfg
  subst hg
  cases ov <;> exact h

/-- The node of a value's label over its data and the encodings of values is the encoded
node. -/
theorem mk_encVal (l : VLabel) (cs : List Val) :
    mk (vdata l).1 (vdata l).2 (cs.map encVal) = encVal (Internal.vnode l cs) :=
  (encVal_node l cs).symm

set_option maxRecDepth 8000 in
/-- The rounds of the state an evaluation starts in are the step of the machine's evaluation, at
a function of jobs related to the operations of the depth below. -/
theorem eStart_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (t : Term)
    (vs : List Val) (k : ℕ) :
    Reach P F 3 («Machine.eStart» (encJobE t vs k))
      (encOpt ((Machine.evalStep G unfold o t vs k).map encVal)) := by
  obtain ⟨l, ts, rfl⟩ := exists_node t
  -- a node all of whose subterms are delayed
  have plain : ∀ (l : Label) (ts : List Term) (R : Tree),
      «Machine.eHasStrict» (encTerm (RoseTree.node l ts)) = ofBool false →
      «Machine.eKids» (encTerm (RoseTree.node l ts)) = ts.map encTerm →
      (labelData l).1 ≠ 0 → ¬ ((labelData l).1 = 1 ∧ ts.length = 0) →
      ¬ ((labelData l).1 = 5 ∧ ts.length = 1) →
      Reach P F 1 («Machine.eFinal» P.G P.unf (encJobE (RoseTree.node l ts) vs k) (encOpt none)
        ((ts.map fun u ↦ o.delay u vs k).map encVal)) R →
      Reach P F 3 («Machine.eStart» (encJobE (RoseTree.node l ts) vs k)) R :=
    fun l ts R hs hk h0 h1 h5 h ↦ eStart_final hF _ vs k false ts hs hk
      (by simpa using h0) (by simpa using h1) (by simpa using h5) h
  cases l with
  | var i =>
    simp only [Machine.evalStep, RoseTree.label_node]
    by_cases h : i < vs.length
    · have hget : (vs.map encVal).getD i (leaf 0) = encVal vs[i] := by
        simp [List.getD_eq_getElem?_getD, h]
      mach_simp [«Machine.eStart», encJobE, labelData, h, hget, ↓reduceDIte]
      exact reach_done _ _
    · mach_simp [«Machine.eStart», encJobE, labelData, h, freeVar_eq, ↓reduceDIte]
      exact reach_done _ _
  | star =>
    rcases ts with _ | ⟨c, ts⟩
    · mach_simp [«Machine.eStart», encJobE, labelData, Machine.evalStep, Internal.vnode,
        encVal_node, vdata]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ Nat.succ_ne_zero _ h.2)
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | pair =>
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | fst =>
    rcases ts with _ | ⟨p, _ | ⟨q, ts⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [p] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _ (fun x ↦ RoseTree.node .fst [x]) _
        fun x ↦ (encVal_node .fst [x]).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | snd =>
    rcases ts with _ | ⟨p, _ | ⟨q, ts⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [p] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _ (fun x ↦ RoseTree.node .snd [x]) _
        fun x ↦ (encVal_node .snd [x]).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | lam a =>
    rcases ts with _ | ⟨b, _ | ⟨q, ts⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.2 (by simp)) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · mach_simp [«Machine.eStart», encJobE, labelData, Machine.evalStep, Internal.vnode,
        encVal_node, vdata]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ by
          have h2 := h.2
          simp only [List.length_cons] at h2
          omega) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | app =>
    rcases ts with _ | ⟨f, _ | ⟨u, _ | ⟨w, ts⟩⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [f, u] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _ (fun x ↦ RoseTree.node .app [x, o.delay u vs k]) _
        fun x ↦ (encVal_node .app [x, o.delay u vs k]).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | arr j θ =>
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | natRec =>
    rcases ts with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, ts⟩⟩⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [m, z] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _ (fun x ↦ RoseTree.node (.natRec s k) (o.delay z vs k :: x :: vs))
        _ fun x ↦ (encVal_node (.natRec s k) (o.delay z vs k :: x :: vs)).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | listRec =>
    rcases ts with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, ts⟩⟩⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [m, z] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _
        (fun x ↦ RoseTree.node (.listRec s k) (o.delay z vs k :: x :: vs)) _
        fun x ↦ (encVal_node (.listRec s k) (o.delay z vs k :: x :: vs)).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | roseRec c =>
    rcases ts with _ | ⟨s, _ | ⟨m, _ | ⟨w, ts⟩⟩⟩
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
    · refine eStart_final hF _ vs k true [m] (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Internal.vnode]
      exact reach_tailW_map hF _ (fun x ↦ RoseTree.node (.roseRec c s k) (x :: vs)) _
        fun x ↦ (encVal_node (.roseRec c s k) (x :: vs)).symm
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _
  | defn j θ =>
    refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
      (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
      (fun h ↦ absurd h.1 (by simp [labelData]))
      (fun h ↦ absurd h.1 (by simp [labelData])) ?_
    have hf : «Machine.eFinal» P.G P.unf (encJobE (RoseTree.node (.defn j θ) ts) vs k) (encOpt none)
        ((ts.map fun u ↦ o.delay u vs k).map encVal) =
        «Machine.evalDefn» P.G P.unf ((ts.map fun u ↦ o.delay u vs k).map encVal)
          (encTerm (RoseTree.node (.defn j θ) ts)) (leaf k) := by
      mach_simp [«Machine.eFinal», encJobE, labelData]
    rw [hf]
    exact evalDefn_reach hP hF j θ ts vs k
  | eq =>
    · refine plain _ _ _ (by mach_simp [«Machine.eHasStrict», labelData])
        (by mach_simp [«Machine.eKids», labelData]) (by simp [labelData])
        (fun h ↦ absurd h.1 (by simp [labelData]))
        (fun h ↦ absurd h.1 (by simp [labelData])) ?_
      mach_simp [«Machine.eFinal», encJobE, labelData, Machine.evalStep, Label.plain?,
        Internal.vnode, encVal_node, vdata, child_encTerm]
      exact reach_done _ _

end Eval

/-! The weak head normal form of a value. -/

section Whnf

variable {P : Params} {F : Tree → Tree} {o : Machine} {G : Internal.Globals} {n : ℕ}
  {unfold : ℕ → Bool} {kl kc : ℕ} {rw : List Tree → ℕ → Term → Option Term}

/-- The encoding of the delayed value of a value's weak head normal form. -/
theorem encVal_delayed (o : Machine) (src : Val) :
    «Machine.delayed» (encOpt ((o.whnf src).map encVal)) (encVal src) =
      encVal (Internal.delayed (Thunk.mk fun _ ↦ o.whnf src) src) := by
  rw [Internal.delayed_eq]
  exact delayed_eq _ _

/-- The state waiting for the weak head normal form of the source of a recursion's value reaches,
in three rounds, the weak head normal form of the value of the fold's step in the environment
extended by that value delayed. -/
theorem wRec_reach_none (hF : JRel F o) (s : Term) (k : ℕ) (src : Val) (env : List Val) :
    Reach P F 3
      («Machine.wRecOf» (encTerm s) (leaf k) (encVal src) (encOpt none) (env.map encVal))
      (encOpt (((o.eval s (Internal.delayed (Thunk.mk fun _ ↦ o.whnf src) src :: env) k).bind
        o.whnf).map encVal)) := by
  have hw := hF.whnf (some src)
  simp only [encJobW, Option.map_some, Option.bind_some] at hw
  refine reach_step (s' := «Machine.msWhnf» (encJobE s
    (Internal.delayed (Thunk.mk fun _ ↦ o.whnf src) src :: env) k)) ?_ (reach_whnfE hF _ _ _)
  mach_simp [«Machine.wRecOf», adv11, «Machine.wRec», «Machine.jobW», hw, encVal_delayed,
    «Machine.jobE», encJobE]

/-- The state waiting for the weak head normal form of the source of a recursion's value reaches,
in three rounds, the weak head normal form of the value of the fold's step in the environment
extended by the pair of a label and that value delayed. -/
theorem wRec_reach_some (hF : JRel F o) (s : Term) (k : ℕ) (src l : Val) (env : List Val) :
    Reach P F 3
      («Machine.wRecOf» (encTerm s) (leaf k) (encVal src) (encOpt (some (encVal l)))
        (env.map encVal))
      (encOpt (((o.eval s (Internal.vnode .pair
        [l, Internal.delayed (Thunk.mk fun _ ↦ o.whnf src) src] :: env) k).bind
          o.whnf).map encVal)) := by
  have hw := hF.whnf (some src)
  simp only [encJobW, Option.map_some, Option.bind_some] at hw
  refine reach_step (s' := «Machine.msWhnf» (encJobE s (Internal.vnode .pair
    [l, Internal.delayed (Thunk.mk fun _ ↦ o.whnf src) src] :: env) k)) ?_
    (reach_whnfE hF _ _ _)
  mach_simp [«Machine.wRecOf», adv11, «Machine.wRec», «Machine.jobW», hw, encVal_delayed,
    «Machine.jobE», encJobE, Internal.vnode, encVal_node, vdata]

/-- The state of a component at the weak head normal form of its pair reaches the weak head
normal form of the component in a round. -/
theorem wProj_reach (hF : JRel F o) (b : Bool) (p p' : Val) (hp : o.whnf p = some p') :
    Reach P F 1
      («Machine.wProj» (encVal (Internal.vnode (if b then .fst else .snd) [p])) (encVal p'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (if b then .fst else .snd) [p])).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node p'
  cases b <;>
    simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hp,
      Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte] <;>
    cases l' <;> rcases cs' with _ | ⟨a, _ | ⟨c, _ | ⟨e, cs'⟩⟩⟩ <;>
    mach_simp [«Machine.wProj», encVal_node, vdata] <;>
    first
      | exact reach_done _ _
      | exact reach_tailW hF (some _)

/-- A state waiting for the weak head normal form of a value's node reaches it in a round. -/
theorem reach_tailW_node (hF : JRel F o) (l : VLabel) (cs : List Val) :
    Reach P F 1
      («Machine.msTail» («Machine.jobW» (encOpt (some (mk (vdata l).1 (vdata l).2
        (cs.map encVal))))))
      (encOpt ((o.whnf (RoseTree.node l cs)).map encVal)) := by
  rw [← encVal_node]
  exact reach_tailW hF (some _)

/-- The function of jobs at the job of a value's weak head normal form. -/
theorem JRel.whnf_some (hF : JRel F o) (v : Val) :
    F («Machine.jobW» (encOpt (some (encVal v)))) = encOpt ((o.whnf v).map encVal) :=
  hF.whnf (some v)

/-- The state of a case analysis at an injection, at the weak head normal form of its pair of
functions, reaches the weak head normal form of the application in a round. -/
theorem wCase2_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (f u p w p' : Val)
    (j j' : ℕ) (θ θ' : List Tree)
    (hf : o.whnf f = some (Internal.vnode (.arr j θ) [p]))
    (hcase : G.prims[j]? = some Internal.casePrim)
    (hu : o.whnf u = some (Internal.vnode (.arr j' θ') [w]))
    (hinj : G.prims[j']? = some Internal.inlPrim ∨ G.prims[j']? = some Internal.inrPrim)
    (hp : o.whnf p = some p') :
    Reach P F 1
      («Machine.wCase2» P.G (encVal (Internal.vnode (.arr j θ) [p]))
        (encVal (Internal.vnode (.arr j' θ') [w])) (encVal p'))
      (encOpt ((Machine.whnfStep G kl kc o (Internal.vnode .app [f, u])).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node p'
  rw [hP.G_eq]
  simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hf,
    hu, hp, hcase, hinj, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
  by_cases hinl : G.prims[j']? = some Internal.inlPrim <;>
    cases l' <;> rcases cs' with _ | ⟨a, _ | ⟨c, _ | ⟨e, cs'⟩⟩⟩ <;>
    mach_simp [«Machine.wCase2», encVal_node, vdata, primIs_eq, inlPrim_eq, hinl] <;>
    first
      | exact reach_done _ _
      | exact reach_tailW_node hF .app [_, _]

/-- The state of a case analysis at the weak head normal form of its argument reaches the weak
head normal form of the application within two rounds. -/
theorem wCase_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (f u p u' : Val) (j : ℕ)
    (θ : List Tree) (hf : o.whnf f = some (Internal.vnode (.arr j θ) [p]))
    (hcase : G.prims[j]? = some Internal.casePrim) (hu : o.whnf u = some u') :
    Reach P F 2
      («Machine.wCase» P.G (encVal (Internal.vnode (.arr j θ) [p])) (encVal u'))
      (encOpt ((Machine.whnfStep G kl kc o (Internal.vnode .app [f, u])).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node u'
  have stuck : ∀ {m : ℕ} {s : Tree}, s = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode .app [f, u])).map encVal)) → Reach P F m s _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | arr j' θ' =>
    rcases cs' with _ | ⟨w, _ | ⟨e, cs'⟩⟩
    · refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wCase», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf, hu,
        hcase]
    · by_cases hinj : G.prims[j']? = some Internal.inlPrim ∨
          G.prims[j']? = some Internal.inrPrim
      · have hs : «Machine.wCase» P.G (encVal (Internal.vnode (.arr j θ) [p]))
            (encVal (RoseTree.node (.arr j' θ') [w])) =
            mk 7 [encVal (Internal.vnode (.arr j θ) [p]),
                encVal (Internal.vnode (.arr j' θ') [w])]
              [«Machine.jobW» (encOpt (some (encVal p)))] := by
          rw [hP.G_eq]
          have hd : (decide (G.prims[j']? = some Internal.inlPrim) ||
              decide (G.prims[j']? = some Internal.inrPrim)) = true := by simpa using hinj
          mach_simp [«Machine.wCase», Internal.vnode, encVal_node, vdata, primIs_eq, inlPrim_eq,
            inrPrim_eq, hd]
        rw [hs]
        refine reach_step (adv7 _ _ _) ?_
        rw [hF.whnf_some]
        rcases hp : o.whnf p with _ | p'
        · rw [Option.map_none, bindS_none]
          refine stuck ?_
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hf, hu, hp, hcase, hinj, Option.bind_eq_bind,
            Option.bind_some, Option.bind_none, ↓reduceIte, Option.map_none]
        · rw [Option.map_some, bindS_some]
          exact wCase2_reach hP hF f u p w p' j j' θ θ' hf hcase hu hinj hp
      · refine stuck ?_
        rw [hP.G_eq]
        have hd : (decide (G.prims[j']? = some Internal.inlPrim) ||
            decide (G.prims[j']? = some Internal.inrPrim)) = false := by simpa using hinj
        mach_simp [«Machine.wCase», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf, hu,
          hcase, hinj, primIs_eq, inlPrim_eq, inrPrim_eq, hd]
    · refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wCase», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf, hu,
        hcase]
  | _ =>
    refine stuck ?_
    rw [hP.G_eq]
    rcases cs' with _ | ⟨w, _ | ⟨e, cs'⟩⟩ <;>
      mach_simp [«Machine.wCase», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf, hu,
        hcase]

/-- The state of an application at the weak head normal form of its function reaches the weak
head normal form of the application within four rounds. -/
theorem wApp_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (f u f' : Val)
    (hf : o.whnf f = some f') :
    Reach P F 4 («Machine.wApp» P.G (encVal (Internal.vnode .app [f, u])) (encVal f'))
      (encOpt ((Machine.whnfStep G kl kc o (Internal.vnode .app [f, u])).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node f'
  have stuck : ∀ {m : ℕ} {s : Tree}, s = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode .app [f, u])).map encVal)) → Reach P F m s _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | clo a b k =>
    have hs : «Machine.wApp» P.G (encVal (Internal.vnode .app [f, u]))
        (encVal (RoseTree.node (.clo a b k) cs')) = «Machine.msWhnf» (encJobE b (u :: cs') k) := by
      mach_simp [«Machine.wApp», Internal.vnode, encVal_node, vdata, «Machine.jobE», encJobE]
    rw [hs]
    simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hf,
      Option.bind_eq_bind, Option.bind_some]
    exact reach_le (reach_whnfE hF b (u :: cs') k) (by omega)
  | arr j θ =>
    rcases cs' with _ | ⟨p, _ | ⟨e, cs'⟩⟩
    · refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wApp», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf]
    · by_cases hcase : G.prims[j]? = some Internal.casePrim
      · have hs : «Machine.wApp» P.G (encVal (Internal.vnode .app [f, u]))
            (encVal (RoseTree.node (.arr j θ) [p])) =
            mk 6 [encVal (Internal.vnode (.arr j θ) [p])]
              [«Machine.jobW» (encOpt (some (encVal u)))] := by
          rw [hP.G_eq]
          mach_simp [«Machine.wApp», Internal.vnode, encVal_node, vdata, primIs_eq, casePrim_eq,
            hcase]
        rw [hs]
        refine reach_step (adv6 _ _) ?_
        rw [hF.whnf_some]
        rcases hu : o.whnf u with _ | u'
        · rw [Option.map_none, bindS_none]
          refine stuck ?_
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hf, hu, hcase, Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, ↓reduceIte, Option.map_none]
        · rw [Option.map_some, bindS_some]
          exact reach_le (wCase_reach hP hF f u p u' j θ hf hcase hu) (by omega)
      · refine stuck ?_
        rw [hP.G_eq]
        mach_simp [«Machine.wApp», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf,
          primIs_eq, casePrim_eq, hcase]
    · refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wApp», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf]
  | _ =>
    refine stuck ?_
    rw [hP.G_eq]
    rcases cs' with _ | ⟨p, _ | ⟨e, cs'⟩⟩ <;>
      mach_simp [«Machine.wApp», Machine.whnfStep, Internal.vnode, encVal_node, vdata, hf]

/-- The state of a fold of a natural number at zero, at the weak head normal form of the
constructor's datum, reaches the weak head normal form of the fold in a round. -/
theorem wBaseNat_reach (hF : JRel F o) (s : Term) (k : ℕ) (z m c c' : Val) (env : List Val)
    (j : ℕ) (hm : o.whnf m = some (Internal.vnode (.arr j []) [c]))
    (hz : G.prims[j]? = some Internal.zeroPrim) (hc : o.whnf c = some c') :
    Reach P F 1
      («Machine.wBase» (encVal (Internal.vnode (.natRec s k) (z :: m :: env)))
        (encVal (Internal.vnode (.arr j []) [c])) (encVal c'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.natRec s k) (z :: m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node c'
  simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hm,
    hc, hz, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
  cases l' <;> rcases cs' with _ | ⟨a, cs'⟩ <;>
    mach_simp [«Machine.wBase», «Machine.foldStuck», encVal_node, vdata] <;>
    first
      | exact reach_done _ _
      | exact reach_tailW hF (some _)

/-- The state of a fold of a list at the empty list, at the weak head normal form of the
constructor's datum, reaches the weak head normal form of the fold in a round. -/
theorem wBaseList_reach (hF : JRel F o) (s : Term) (k : ℕ) (z m c c' : Val) (env : List Val)
    (j : ℕ) (a : Tree) (hm : o.whnf m = some (Internal.vnode (.arr j [a]) [c]))
    (hz : G.prims[j]? = some Internal.nilPrim) (hc : o.whnf c = some c') :
    Reach P F 1
      («Machine.wBase» (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
        (encVal (Internal.vnode (.arr j [a]) [c])) (encVal c'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.listRec s k) (z :: m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node c'
  simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hm,
    hc, hz, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
  cases l' <;> rcases cs' with _ | ⟨a', cs'⟩ <;>
    mach_simp [«Machine.wBase», «Machine.foldStuck», encVal_node, vdata] <;>
    first
      | exact reach_done _ _
      | exact reach_tailW hF (some _)

/-- The state of a fold of a natural number at the weak head normal form of its number reaches
the weak head normal form of the fold within four rounds. -/
theorem wNat_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (s : Term) (k : ℕ)
    (z m m' : Val) (env : List Val) (hm : o.whnf m = some m') :
    Reach P F 4
      («Machine.wNat» P.G (encVal (Internal.vnode (.natRec s k) (z :: m :: env))) (encVal m'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.natRec s k) (z :: m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node m'
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode (.natRec s k) (z :: m :: env))).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | arr j θ =>
    rcases θ with _ | ⟨a, θ⟩ <;> rcases cs' with _ | ⟨c, _ | ⟨e, cs'⟩⟩
    case nil.cons.nil =>
      by_cases hz : G.prims[j]? = some Internal.zeroPrim
      · have hs : «Machine.wNat» P.G (encVal (Internal.vnode (.natRec s k) (z :: m :: env)))
            (encVal (RoseTree.node (.arr j []) [c])) =
            mk 8 [encVal (Internal.vnode (.natRec s k) (z :: m :: env)),
                encVal (Internal.vnode (.arr j []) [c])]
              [«Machine.jobW» (encOpt (some (encVal c)))] := by
          rw [hP.G_eq]
          mach_simp [«Machine.wNat», Internal.vnode, encVal_node, vdata, primIs_eq, zeroPrim_eq,
            hz]
        rw [hs]
        refine reach_step (adv8 _ _ _) ?_
        rw [hF.whnf_some]
        rcases hc : o.whnf c with _ | c'
        · rw [Option.map_none, bindS_none]
          refine stuck ?_
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hm, hc, hz, Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, ↓reduceIte, Option.map_none]
        · rw [Option.map_some, bindS_some]
          exact reach_le (wBaseNat_reach hF s k z m c c' env j hm hz hc) (by omega)
      · by_cases hsucc : G.prims[j]? = some Internal.succPrim
        · have hne : ¬ (some Internal.succPrim = some Internal.zeroPrim) :=
            fun h ↦ hz (hsucc.trans h)
          have hsrc : mk 9 [encTerm s, leaf k] (encVal z :: encVal c :: env.map encVal) =
              encVal (Internal.vnode (.natRec s k) (z :: c :: env)) :=
            (encVal_node (.natRec s k) (z :: c :: env)).symm
          have hs : «Machine.wNat» P.G (encVal (Internal.vnode (.natRec s k) (z :: m :: env)))
              (encVal (RoseTree.node (.arr j []) [c])) =
              «Machine.wRecOf» (encTerm s) (leaf k)
                (encVal (Internal.vnode (.natRec s k) (z :: c :: env))) (encOpt none)
                (env.map encVal) := by
            rw [hP.G_eq]
            mach_simp [«Machine.wNat», Internal.vnode, vdata, primIs_eq, zeroPrim_eq,
              succPrim_eq, hsucc, hne, hsrc]
          rw [hs]
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hm, hsucc, Option.bind_eq_bind, Option.bind_some,
            ↓reduceIte]
          exact reach_le (wRec_reach_none hF s k _ env) (by omega)
        · refine stuck ?_
          rw [hP.G_eq]
          mach_simp [«Machine.wNat», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
            encVal_node, vdata, hm, primIs_eq, zeroPrim_eq, succPrim_eq, hz, hsucc]
    all_goals
      refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wNat», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]
  | _ =>
    refine stuck ?_
    rw [hP.G_eq]
    rcases cs' with _ | ⟨c, _ | ⟨e, cs'⟩⟩ <;>
      mach_simp [«Machine.wNat», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]

/-- The state of a fold of a list at a construction, at the weak head normal form of the
constructor's datum, reaches the weak head normal form of the fold within three rounds. -/
theorem wCons_reach (hF : JRel F o) (s : Term) (k : ℕ) (z m c c' : Val) (env : List Val)
    (j : ℕ) (a : Tree) (hm : o.whnf m = some (Internal.vnode (.arr j [a]) [c]))
    (hnil : ¬ G.prims[j]? = some Internal.nilPrim)
    (hcons : G.prims[j]? = some Internal.consPrim) (hc : o.whnf c = some c') :
    Reach P F 3
      («Machine.wCons» (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
        (encVal (Internal.vnode (.arr j [a]) [c])) (encVal c'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.listRec s k) (z :: m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node c'
  have hne : ¬ (some Internal.consPrim = some Internal.nilPrim) := fun h ↦ hnil (hcons.trans h)
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode (.listRec s k) (z :: m :: env))).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | pair =>
    rcases cs' with _ | ⟨h, _ | ⟨tl, _ | ⟨e, cs'⟩⟩⟩
    case cons.cons.nil =>
      have hsrc : mk 10 [encTerm s, leaf k] (encVal z :: encVal tl :: env.map encVal) =
          encVal (Internal.vnode (.listRec s k) (z :: tl :: env)) :=
        (encVal_node (.listRec s k) (z :: tl :: env)).symm
      have hs : «Machine.wCons» (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
          (encVal (Internal.vnode (.arr j [a]) [c])) (encVal (RoseTree.node .pair [h, tl])) =
          «Machine.wRecOf» (encTerm s) (leaf k)
            (encVal (Internal.vnode (.listRec s k) (z :: tl :: env))) (encOpt none)
            ((h :: env).map encVal) := by
        mach_simp [«Machine.wCons», Internal.vnode, vdata, hsrc]
      rw [hs]
      simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node,
        hm, hc, hcons, hne, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
      exact wRec_reach_none hF s k _ (h :: env)
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wCons», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm, hc, hcons, hne]
  | _ =>
    refine stuck ?_
    rcases cs' with _ | ⟨h, _ | ⟨tl, _ | ⟨e, cs'⟩⟩⟩ <;>
      mach_simp [«Machine.wCons», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm, hc, hcons, hne]

/-- The state of a fold of a list at the weak head normal form of its list reaches the weak head
normal form of the fold within four rounds. -/
theorem wList_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (s : Term) (k : ℕ)
    (z m m' : Val) (env : List Val) (hm : o.whnf m = some m') :
    Reach P F 4
      («Machine.wList» P.G (encVal (Internal.vnode (.listRec s k) (z :: m :: env))) (encVal m'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.listRec s k) (z :: m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node m'
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode (.listRec s k) (z :: m :: env))).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | arr j θ =>
    rcases θ with _ | ⟨a, _ | ⟨a', θ⟩⟩ <;> rcases cs' with _ | ⟨c, _ | ⟨e, cs'⟩⟩
    case cons.nil.cons.nil =>
      by_cases hz : G.prims[j]? = some Internal.nilPrim
      · have hs : «Machine.wList» P.G (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
            (encVal (RoseTree.node (.arr j [a]) [c])) =
            mk 8 [encVal (Internal.vnode (.listRec s k) (z :: m :: env)),
                encVal (Internal.vnode (.arr j [a]) [c])]
              [«Machine.jobW» (encOpt (some (encVal c)))] := by
          rw [hP.G_eq]
          mach_simp [«Machine.wList», Internal.vnode, encVal_node, vdata, primIs_eq, nilPrim_eq,
            hz]
        rw [hs]
        refine reach_step (adv8 _ _ _) ?_
        rw [hF.whnf_some]
        rcases hc : o.whnf c with _ | c'
        · rw [Option.map_none, bindS_none]
          refine stuck ?_
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hm, hc, hz, Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, ↓reduceIte, Option.map_none]
        · rw [Option.map_some, bindS_some]
          exact reach_le (wBaseList_reach hF s k z m c c' env j a hm hz hc) (by omega)
      · by_cases hcons : G.prims[j]? = some Internal.consPrim
        · have hne : ¬ (some Internal.consPrim = some Internal.nilPrim) :=
            fun h ↦ hz (hcons.trans h)
          have hs : «Machine.wList» P.G (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
              (encVal (RoseTree.node (.arr j [a]) [c])) =
              mk 9 [encVal (Internal.vnode (.listRec s k) (z :: m :: env)),
                  encVal (Internal.vnode (.arr j [a]) [c])]
                [«Machine.jobW» (encOpt (some (encVal c)))] := by
            rw [hP.G_eq]
            mach_simp [«Machine.wList», Internal.vnode, encVal_node, vdata, primIs_eq,
              nilPrim_eq, consPrim_eq, hcons, hne]
          rw [hs]
          refine reach_step (adv9 _ _ _) ?_
          rw [hF.whnf_some]
          rcases hc : o.whnf c with _ | c'
          · rw [Option.map_none, bindS_none]
            refine stuck ?_
            simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
              RoseTree.children_node, hm, hc, hcons, hne, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, ↓reduceIte, Option.map_none]
          · rw [Option.map_some, bindS_some]
            exact wCons_reach hF s k z m c c' env j a hm hz hcons hc
        · refine stuck ?_
          rw [hP.G_eq]
          mach_simp [«Machine.wList», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
            encVal_node, vdata, hm, primIs_eq, nilPrim_eq, consPrim_eq, hz, hcons]
    all_goals
      refine stuck ?_
      rw [hP.G_eq]
      mach_simp [«Machine.wList», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]
  | _ =>
    refine stuck ?_
    rw [hP.G_eq]
    rcases cs' with _ | ⟨c, _ | ⟨e, cs'⟩⟩ <;>
      mach_simp [«Machine.wList», «Machine.foldStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]

/-- The state of a fold of a rose tree at a node, at the weak head normal form of the node's
pair, reaches the weak head normal form of the fold within three rounds. -/
theorem wRose2_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (c : Tree) (s : Term)
    (k : ℕ) (m p p' : Val) (env : List Val) (j : ℕ) (θ : List Tree)
    (hm : o.whnf m = some (Internal.vnode (.arr j θ) [p]))
    (hprims : (G.prims[j]? = some Internal.nodePrim ∨ G.prims[j]? = some Internal.lnodePrim) ∧
      G.prims[kl]? = some Internal.nilPrim ∧ G.prims[kc]? = some Internal.consPrim)
    (hp : o.whnf p = some p') :
    Reach P F 3
      («Machine.wRose2» P.kl P.kc (encVal (Internal.vnode (.roseRec c s k) (m :: env)))
        (encVal (Internal.vnode (.arr j θ) [p])) (encVal p'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.roseRec c s k) (m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node p'
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode (.roseRec c s k) (m :: env))).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  rw [hP.kl_eq, hP.kc_eq]
  cases l' with
  | pair =>
    rcases cs' with _ | ⟨l, _ | ⟨cs, _ | ⟨e, cs'⟩⟩⟩
    case cons.cons.nil =>
      have hsrc : mk 10 [encTerm (Term.arr kc [c] (Term.pair
          (Term.roseRec c (Internal.weakenStep2 s) (Term.var 1)) (Term.var 0))), leaf k]
          (mk 5 [leaf kl, RoseTree.node 0 [c]] [mk 2 [] []] :: encVal cs :: env.map encVal) =
          encVal (Internal.vnode (.listRec (Term.arr kc [c] (Term.pair
            (Term.roseRec c (Internal.weakenStep2 s) (Term.var 1)) (Term.var 0))) k)
            (Internal.vnode (.arr kl [c]) [Internal.vnode .star []] :: cs :: env)) := by
        simp only [Internal.vnode, encVal_node, vdata, List.map_cons, List.map_nil]
      have hs : «Machine.wRose2» (leaf kl) (leaf kc)
          (encVal (Internal.vnode (.roseRec c s k) (m :: env)))
          (encVal (Internal.vnode (.arr j θ) [p])) (encVal (RoseTree.node .pair [l, cs])) =
          «Machine.wRecOf» (encTerm s) (leaf k)
            (encVal (Internal.vnode (.listRec (Term.arr kc [c] (Term.pair
              (Term.roseRec c (Internal.weakenStep2 s) (Term.var 1)) (Term.var 0))) k)
              (Internal.vnode (.arr kl [c]) [Internal.vnode .star []] :: cs :: env)))
            (encOpt (some (encVal l))) (env.map encVal) := by
        mach_simp [«Machine.wRose2», Internal.vnode, vdata, mArr_eq, mPair_eq, mRoseRec_eq,
          weakenStep2_eq, mVar_eq, hsrc]
      rw [hs]
      simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node, RoseTree.children_node,
        hm, hp, hprims, Option.bind_eq_bind, Option.bind_some, ↓reduceIte, and_self]
      exact wRec_reach_some hF s k _ l env
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wRose2», «Machine.roseStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm, hp, hprims, and_self]
  | _ =>
    refine stuck ?_
    rcases cs' with _ | ⟨l, _ | ⟨cs, _ | ⟨e, cs'⟩⟩⟩ <;>
      mach_simp [«Machine.wRose2», «Machine.roseStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm, hp, hprims, and_self]

/-- The state of a fold of a rose tree at the weak head normal form of its tree reaches the weak
head normal form of the fold within four rounds. -/
theorem wRose_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (c : Tree) (s : Term)
    (k : ℕ) (m m' : Val) (env : List Val) (hm : o.whnf m = some m') :
    Reach P F 4
      («Machine.wRose» P.G P.kl P.kc (encVal (Internal.vnode (.roseRec c s k) (m :: env)))
        (encVal m'))
      (encOpt ((Machine.whnfStep G kl kc o
        (Internal.vnode (.roseRec c s k) (m :: env))).map encVal)) := by
  obtain ⟨l', cs', rfl⟩ := exists_node m'
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (Internal.vnode (.roseRec c s k) (m :: env))).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l' with
  | arr j θ =>
    rcases cs' with _ | ⟨p, _ | ⟨e, cs'⟩⟩
    case cons.nil =>
      by_cases hprims : (G.prims[j]? = some Internal.nodePrim ∨
          G.prims[j]? = some Internal.lnodePrim) ∧
          G.prims[kl]? = some Internal.nilPrim ∧ G.prims[kc]? = some Internal.consPrim
      · have hd : ((decide (G.prims[j]? = some Internal.nodePrim) ||
            decide (G.prims[j]? = some Internal.lnodePrim)) &&
            (decide (G.prims[kl]? = some Internal.nilPrim) &&
              decide (G.prims[kc]? = some Internal.consPrim))) = true := by simpa using hprims
        have hs : «Machine.wRose» P.G P.kl P.kc
            (encVal (Internal.vnode (.roseRec c s k) (m :: env)))
            (encVal (RoseTree.node (.arr j θ) [p])) =
            mk 10 [encVal (Internal.vnode (.roseRec c s k) (m :: env)),
                encVal (Internal.vnode (.arr j θ) [p])]
              [«Machine.jobW» (encOpt (some (encVal p)))] := by
          rw [hP.G_eq, hP.kl_eq, hP.kc_eq]
          mach_simp [«Machine.wRose», Internal.vnode, vdata, primIs_eq, nodePrim_eq,
            lnodePrim_eq, nilPrim_eq, consPrim_eq, hd]
        rw [hs]
        refine reach_step (adv10 _ _ _) ?_
        rw [hF.whnf_some]
        rcases hp : o.whnf p with _ | p'
        · rw [Option.map_none, bindS_none]
          refine stuck ?_
          simp only [Machine.whnfStep, Internal.vnode, RoseTree.label_node,
            RoseTree.children_node, hm, hp, hprims, Option.bind_eq_bind, Option.bind_some,
            Option.bind_none, ↓reduceIte, Option.map_none, and_self]
        · rw [Option.map_some, bindS_some]
          exact wRose2_reach hP hF c s k m p p' env j θ hm hprims hp
      · have hd : ((decide (G.prims[j]? = some Internal.nodePrim) ||
            decide (G.prims[j]? = some Internal.lnodePrim)) &&
            (decide (G.prims[kl]? = some Internal.nilPrim) &&
              decide (G.prims[kc]? = some Internal.consPrim))) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact hprims (by simpa using h)
        refine stuck ?_
        rw [hP.G_eq, hP.kl_eq, hP.kc_eq]
        mach_simp [«Machine.wRose», «Machine.roseStuck», Machine.whnfStep, Internal.vnode,
          encVal_node, vdata, hm, primIs_eq, nodePrim_eq, lnodePrim_eq, nilPrim_eq, consPrim_eq,
          hd, hprims]
    all_goals
      refine stuck ?_
      rw [hP.G_eq, hP.kl_eq, hP.kc_eq]
      mach_simp [«Machine.wRose», «Machine.roseStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]
  | _ =>
    refine stuck ?_
    rw [hP.G_eq, hP.kl_eq, hP.kc_eq]
    rcases cs' with _ | ⟨p, _ | ⟨e, cs'⟩⟩ <;>
      mach_simp [«Machine.wRose», «Machine.roseStuck», Machine.whnfStep, Internal.vnode,
        encVal_node, vdata, hm]

set_option maxRecDepth 8000 in
/-- The rounds of the state a weak head normal form starts in are the step of the machine's weak
head normal form, at a function of jobs related to the operations of the depth below. -/
theorem wStart_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (v : Val) :
    Reach P F 5 («Machine.wStart» (encVal v))
      (encOpt ((Machine.whnfStep G kl kc o v).map encVal)) := by
  obtain ⟨l, cs, rfl⟩ := exists_node v
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt ((Machine.whnfStep G kl kc o
      (RoseTree.node l cs)).map encVal)) → Reach P F r t _ :=
    fun h ↦ h ▸ reach_done _ _
  cases l with
  | delay =>
    rcases cs with _ | ⟨r, _ | ⟨x, _ | ⟨e, cs⟩⟩⟩
    case cons.cons.nil =>
      refine stuck ?_
      obtain ⟨lr, csr, rfl⟩ := exists_node r
      cases lr <;>
        mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | fst =>
    rcases cs with _ | ⟨p, _ | ⟨q, cs⟩⟩
    case cons.nil =>
      have hs : «Machine.wStart» (encVal (RoseTree.node .fst [p])) =
          mk 5 [encVal (Internal.vnode .fst [p])]
            [«Machine.jobW» (encOpt (some (encVal p)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hp : o.whnf p with _ | p'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hp,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc (encVal (Internal.vnode .fst [p]))
            (encVal p') = «Machine.wProj» (encVal (Internal.vnode .fst [p])) (encVal p') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact reach_le (wProj_reach hF true p p' hp) (by omega)
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | snd =>
    rcases cs with _ | ⟨p, _ | ⟨q, cs⟩⟩
    case cons.nil =>
      have hs : «Machine.wStart» (encVal (RoseTree.node .snd [p])) =
          mk 5 [encVal (Internal.vnode .snd [p])]
            [«Machine.jobW» (encOpt (some (encVal p)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hp : o.whnf p with _ | p'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hp,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc (encVal (Internal.vnode .snd [p]))
            (encVal p') = «Machine.wProj» (encVal (Internal.vnode .snd [p])) (encVal p') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact reach_le (wProj_reach hF false p p' hp) (by omega)
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | app =>
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨e, cs⟩⟩⟩
    case cons.cons.nil =>
      have hs : «Machine.wStart» (encVal (RoseTree.node .app [f, u])) =
          mk 5 [encVal (Internal.vnode .app [f, u])]
            [«Machine.jobW» (encOpt (some (encVal f)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hf : o.whnf f with _ | f'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hf,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc (encVal (Internal.vnode .app [f, u]))
            (encVal f') = «Machine.wApp» P.G (encVal (Internal.vnode .app [f, u])) (encVal f') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact wApp_reach hP hF f u f' hf
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | natRec s k =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    case cons.cons =>
      have hs : «Machine.wStart» (encVal (RoseTree.node (.natRec s k) (z :: m :: env))) =
          mk 5 [encVal (Internal.vnode (.natRec s k) (z :: m :: env))]
            [«Machine.jobW» (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hm : o.whnf m with _ | m'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hm,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc
            (encVal (Internal.vnode (.natRec s k) (z :: m :: env))) (encVal m') =
            «Machine.wNat» P.G (encVal (Internal.vnode (.natRec s k) (z :: m :: env)))
              (encVal m') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact wNat_reach hP hF s k z m m' env hm
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | listRec s k =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    case cons.cons =>
      have hs : «Machine.wStart» (encVal (RoseTree.node (.listRec s k) (z :: m :: env))) =
          mk 5 [encVal (Internal.vnode (.listRec s k) (z :: m :: env))]
            [«Machine.jobW» (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hm : o.whnf m with _ | m'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hm,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc
            (encVal (Internal.vnode (.listRec s k) (z :: m :: env))) (encVal m') =
            «Machine.wList» P.G (encVal (Internal.vnode (.listRec s k) (z :: m :: env)))
              (encVal m') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact wList_reach hP hF s k z m m' env hm
    all_goals
      refine stuck ?_
      mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | roseRec c s k =>
    rcases cs with _ | ⟨m, env⟩
    case cons =>
      have hs : «Machine.wStart» (encVal (RoseTree.node (.roseRec c s k) (m :: env))) =
          mk 5 [encVal (Internal.vnode (.roseRec c s k) (m :: env))]
            [«Machine.jobW» (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.wStart», Internal.vnode, vdata]
      rw [hs]
      refine reach_step (adv5 _ _) ?_
      rw [hF.whnf_some]
      rcases hm : o.whnf m with _ | m'
      · rw [Option.map_none, bindS_none]
        refine stuck ?_
        simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node, hm,
          Option.bind_eq_bind, Option.bind_none, Option.map_none]
      · rw [Option.map_some, bindS_some]
        have hh : «Machine.wHead» P.G P.kl P.kc
            (encVal (Internal.vnode (.roseRec c s k) (m :: env))) (encVal m') =
            «Machine.wRose» P.G P.kl P.kc (encVal (Internal.vnode (.roseRec c s k) (m :: env)))
              (encVal m') := by
          mach_simp [«Machine.wHead», Internal.vnode, vdata]
        rw [hh]
        exact wRose_reach hP hF c s k m m' env hm
    refine stuck ?_
    mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]
  | _ =>
    refine stuck ?_
    mach_simp [«Machine.wStart», Machine.whnfStep, Internal.vnode, vdata]

end Whnf

/-! The normal form of a value's term. -/

/-- The step of the normal form at a node's normal form with its mark, the node's weak head
normal form {lit}`w`: a node that eliminates a child within which a rewriting changed a term is
reduced again, and any other is rewritten at its root where the rewriting rewrites it to a term
whose variables are leaves, the result reduced again. -/
def post (rw : List Tree → ℕ → Term → Option Term) (o : Machine) (Γ : List Tree) (k : ℕ)
    (w : Val) (p : Term × Bool) : Option (Term × Bool) :=
  if p.2 && w.label.eliminates then o.renorm Γ k p.1
  else match rw Γ k p.1 with
    | some u => if u.VarLeaves then o.renorm Γ k u else some p
    | none => some p

/-- The machine's step of the normal form: the weak head normal form, the normal form of its
node, and the step at that normal form. -/
theorem nfStep_eq (G : Internal.Globals) (n : ℕ) (rw : List Tree → ℕ → Term → Option Term)
    (o : Machine) (Γ : List Tree) (k : ℕ) (v : Val) :
    Machine.nfStep G n rw o Γ k v =
      (o.whnf v).bind fun w ↦ (o.nfNode G n Γ k w).bind (post rw o Γ k w) := by
  unfold Machine.nfStep
  cases o.whnf v with
  | none => rfl
  | some w =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases o.nfNode G n Γ k w with
    | none => rfl
    | some p =>
      obtain ⟨t, b⟩ := p
      simp only [Option.bind_some, post]
      cases rw Γ k t <;> rfl

/-- Whether a value's label eliminates one of its children, by its position. -/
theorem eliminates_eq (l : VLabel) :
    (decide (5 < (vdata l).1) && decide ((vdata l).1 < 12)) = l.eliminates := by
  cases l with
  | free l =>
    have h5 : ¬ 5 < fpos l := by
      unfold fpos
      split <;> omega
    simp [vdata, VLabel.eliminates, h5]
  | _ => simp [vdata, VLabel.eliminates]

/-- A traversal of a list by a function to optional values gives the list of the values where
each is present, and nothing where one is absent. -/
theorem mapM_some_or_none {α β : Type} (f : α → Option β) (xs : List α) :
    (∃ ys, xs.mapM f = some ys ∧ xs.map f = ys.map some) ∨
      (xs.mapM f = none ∧ (xs.all fun x ↦ (f x).isSome) = false) :=
  xs.rec (.inl ⟨[], rfl, rfl⟩) fun x r ih ↦ by
    rw [List.mapM_cons]
    rcases hx : f x with _ | y
    · exact .inr ⟨rfl, by simp [hx]⟩
    · rcases ih with ⟨ys, h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨y :: ys, by simp [h₁], by simp [hx, h₂]⟩
      · exact .inr ⟨by simp [h₁], by simp [hx, h₂]⟩

section Nf

variable {P : Params} {F : Tree → Tree} {o : Machine} {G : Internal.Globals} {n : ℕ}
  {unfold : ℕ → Bool} {kl kc : ℕ} {rw : List Tree → ℕ → Term → Option Term}

/-- The function of jobs at the job of a value's normal form. -/
theorem JRel.nf_some (hF : JRel F o) (Γ : List Tree) (k : ℕ) (v : Val) :
    F («Machine.jobN» Γ (leaf k) (encOpt (some (encVal v)))) =
      encOpt ((o.nf Γ k v).map encNF) :=
  hF.nf Γ k (some v)

/-- The state waiting for the value of a term in the empty environment reaches, in two rounds,
its normal form marked as changed by a rewriting. -/
theorem nRenorm_reach (hF : JRel F o) (Γ : List Tree) (k : ℕ) (t : Term) :
    Reach P F 2 («Machine.nRenorm» Γ (leaf k) (encTerm t))
      (encOpt ((o.renorm Γ k t).map encNF)) := by
  have hs : «Machine.nRenorm» Γ (leaf k) (encTerm t) =
      mk 17 [RoseTree.node 0 Γ, leaf k] [encJobE t [] k] := rfl
  rw [hs]
  refine reach_step (adv17 _ _ _) (reach_step (adv18 _) ?_)
  rw [hF.eval, jobN_eq, hF.nf]
  have hres : «Base.bindO» (encOpt (((o.eval t [] k).bind (o.nf Γ k)).map encNF))
      (fun x ↦ «Machine.marked» («Machine.nfTerm» x) (leaf 1)) =
      encOpt ((o.renorm Γ k t).map encNF) := by
    unfold Machine.renorm
    rcases o.eval t [] k with _ | v
    · rfl
    · simp only [Option.bind_eq_bind, Option.bind_some]
      rcases o.nf Γ k v with _ | ⟨u, b⟩
      · rfl
      · mach_simp [«Machine.marked», «Machine.nfTerm», encNF]
        rfl
  rw [hres]
  exact reach_done _ _

/-- The state of a node's normal form with its mark reaches the step of the normal form at it
within two rounds. -/
theorem nPost_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (w : Val) (p : Term × Bool) :
    Reach P F 2 («Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm p.1) (ofBool p.2))
      (encOpt ((post rw o Γ k w p).map encNF)) := by
  obtain ⟨t, b⟩ := p
  have he := eliminates_eq w.label
  by_cases h : (b && w.label.eliminates) = true
  · have hs : «Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm t) (ofBool b) =
        «Machine.nRenorm» Γ (leaf k) (encTerm t) := by
      mach_simp [«Machine.nPost», he, h]
    rw [hs]
    simp only [post, h, ↓reduceIte]
    exact nRenorm_reach hF Γ k t
  · rw [Bool.not_eq_true] at h
    rcases hrw : rw Γ k t with _ | u
    · have hs : «Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm t) (ofBool b) =
          «Machine.msDone» (encOpt (some (encNF (t, b)))) := by
        mach_simp [«Machine.nPost», he, h, hP.rw_eq, hrw, «Machine.marked»]
        rfl
      rw [hs]
      simp only [post, h, hrw, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      exact reach_done _ _
    · by_cases hv : u.VarLeaves = true
      · have hs : «Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm t) (ofBool b) =
            «Machine.nRenorm» Γ (leaf k) (encTerm u) := by
          mach_simp [«Machine.nPost», he, h, hP.rw_eq, hrw, varLeaves_eq, hv]
        rw [hs]
        simp only [post, h, hrw, hv, Bool.false_eq_true, ↓reduceIte]
        exact nRenorm_reach hF Γ k u
      · rw [Bool.not_eq_true] at hv
        have hs : «Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm t) (ofBool b) =
            «Machine.msDone» (encOpt (some (encNF (t, b)))) := by
          mach_simp [«Machine.nPost», he, h, hP.rw_eq, hrw, varLeaves_eq, hv, «Machine.marked»]
          rfl
        rw [hs]
        simp only [post, h, hrw, hv, Bool.false_eq_true, ↓reduceIte, Option.map_some]
        exact reach_done _ _

/-- The state waiting for the value of a closure's body or of a fold's step reaches, within four
rounds, the step of the normal form at the term built from that value's normal form in the
extended context. -/
theorem nBody_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (w : Val) (Γ' : List Tree) (k' : ℕ) (pre : List Tree) (s : Term) (vs : List Val) (ks : ℕ)
    (build : Term × Bool → Term × Bool)
    (hT : ∀ x, «Machine.nBuildT» (encVal w) pre (encNF x) = encTerm (build x).1)
    (hB : ∀ x, «Machine.nBuildB» (encVal w) pre (encNF x) = ofBool (build x).2) :
    Reach P F 4
      (mk 14 [RoseTree.node 0 Γ, leaf k, encVal w, RoseTree.node 0 Γ', leaf k',
        RoseTree.node 0 pre] [encJobE s vs ks])
      (encOpt ((((o.eval s vs ks).bind (o.nf Γ' k')).bind fun x ↦
        post rw o Γ k w (build x)).map encNF)) := by
  refine reach_step (s' := mk 15 [RoseTree.node 0 Γ, leaf k, encVal w, RoseTree.node 0 pre]
    [encJobN Γ' k' (o.eval s vs ks)]) ?_ ?_
  · rw [adv14, hF.eval]
    mach_simp [«Machine.nBody», «Machine.jobN», encJobN]
  · refine reach_step (adv15 _ _) ?_
    rw [hF.nf]
    rcases (o.eval s vs ks).bind (o.nf Γ' k') with _ | x
    · rw [Option.map_none, bindS_none]
      exact reach_done _ _
    · rw [Option.map_some, bindS_some]
      have hs : «Machine.nDone» P.rw [RoseTree.node 0 Γ, leaf k, encVal w, RoseTree.node 0 pre]
          (encNF x) = «Machine.nPost» P.rw Γ (leaf k) (encVal w) (encTerm (build x).1)
            (ofBool (build x).2) := by
        mach_simp [«Machine.nDone», hT, hB]
      rw [hs]
      exact nPost_reach hP hF Γ k w (build x)

/-- The state of a node whose children are in the term's context, waiting for their normal forms,
reaches within three rounds the step of the normal form at the node over them. -/
theorem nKids_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (l : VLabel) (cs : List Val) :
    Reach P F 3
      (mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node l cs)]
        (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))))
      (encOpt (((cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node l cs)
        (Internal.readStep k l (rs.map Prod.fst), rs.any Prod.snd)).map encNF)) := by
  refine reach_step (adv16 _ _ _ _) ?_
  have hm : (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))).map F =
      (cs.map (o.nf Γ k)).map fun r ↦ encOpt (r.map encNF) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun c _ ↦ hF.nf_some Γ k c
  rw [hm]
  rcases mapM_some_or_none (o.nf Γ k) cs with ⟨ys, h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, List.map_map]
    have htrue : (ys.all fun _ ↦ true) = true := List.all_eq_true.mpr fun _ _ ↦ rfl
    have hall : «Base.allT» «Prelude.isSome»
        (ys.map ((fun r : Option (Term × Bool) ↦ encOpt (r.map encNF)) ∘ some)) = ofBool true :=
      htrue ▸ allT_map «Prelude.isSome» _ (fun _ ↦ true) ys fun y _ ↦ by
        mirror_simp [Function.comp_apply]
    have hterms : «Base.mapT» (fun r ↦ «Machine.nfTerm» («Prelude.get» r))
        (ys.map ((fun r : Option (Term × Bool) ↦ encOpt (r.map encNF)) ∘ some)) =
        (ys.map Prod.fst).map encTerm := by
      mirror_simp [«Machine.nfTerm», encNF, Function.comp_apply]
    have hany : «Base.anyT» (fun r ↦ «Machine.nfMark» («Prelude.get» r))
        (ys.map ((fun r : Option (Term × Bool) ↦ encOpt (r.map encNF)) ∘ some)) =
        ofBool (ys.any Prod.snd) := by
      rw [anyT_eq _ (fun t ↦ («Machine.nfMark» («Prelude.get» t)).label != 0) _ fun x hx ↦ by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨t, b⟩ := y
        cases b <;> rfl, List.any_map]
      congr 2
      funext y
      obtain ⟨t, b⟩ := y
      cases b <;> rfl
    have hs : «Machine.nKids» P.rw Γ (leaf k) (encVal (RoseTree.node l cs))
        (ys.map ((fun r : Option (Term × Bool) ↦ encOpt (r.map encNF)) ∘ some)) =
        «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node l cs))
          (encTerm (Internal.readStep k l (ys.map Prod.fst))) (ofBool (ys.any Prod.snd)) := by
      simp only [«Machine.nKids», hall, hterms, hany, ofBool_true, label_leaf, ne_eq,
        one_ne_zero, not_false_eq_true, ↓reduceIte]
      rw [encVal_node, readStep_eq]
    rw [hs, Option.bind_some]
    exact nPost_reach hP hF Γ k (RoseTree.node l cs)
      (Internal.readStep k l (ys.map Prod.fst), ys.any Prod.snd)
  · have hall : «Base.allT» «Prelude.isSome»
        ((cs.map (o.nf Γ k)).map fun r ↦ encOpt (r.map encNF)) = ofBool false := by
      rw [List.map_map, ← h₂]
      exact allT_map «Prelude.isSome» _ (fun c ↦ (o.nf Γ k c).isSome) cs fun c _ ↦ by
        mirror_simp [Function.comp_apply, Option.isSome_map]
    have hs : «Machine.nKids» P.rw Γ (leaf k) (encVal (RoseTree.node l cs))
        ((cs.map (o.nf Γ k)).map fun r ↦ encOpt (r.map encNF)) =
        «Machine.msDone» (encOpt none) := by
      simp only [«Machine.nKids», hall, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
        ↓reduceIte, none_eq]
    rw [hs, h₁]
    exact reach_done _ _

/-- The state of a fold of a natural number waiting for the normal forms of its start and of
its number reaches, within five rounds, the step of the normal form at the fold's. -/
theorem nFoldNat_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (s : Term) (k' : ℕ) (z m : Val) (env : List Val) :
    Reach P F 5
      (mk 13 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.natRec s k') (z :: m :: env))]
        [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal z))),
          «Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))])
      (encOpt (((o.nfNode G n Γ k (Internal.vnode (.natRec s k') (z :: m :: env))).bind
        (post rw o Γ k (Internal.vnode (.natRec s k') (z :: m :: env)))).map encNF)) := by
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt none) →
      (o.nfNode G n Γ k (Internal.vnode (.natRec s k') (z :: m :: env))) = none →
      Reach P F r t (encOpt (((o.nfNode G n Γ k (Internal.vnode (.natRec s k')
        (z :: m :: env))).bind (post rw o Γ k (Internal.vnode (.natRec s k')
          (z :: m :: env)))).map encNF)) :=
    fun h h' ↦ by
      rw [h, h']
      exact reach_done _ _
  refine reach_step (adv13 _ _ _ _) ?_
  simp only [List.map_cons, List.map_nil, hF.nf_some]
  rw [hP.G_eq, hP.n_eq]
  rcases hz : o.nf Γ k z with _ | ⟨z', bz⟩
  · refine stuck (by mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none]) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      Option.bind_eq_bind, Option.bind_none]
  rcases hm : o.nf Γ k m with _ | ⟨m', bm⟩
  · refine stuck (by mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some])
      ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  rcases hc : Internal.typeIn G n Γ z' with _ | c
  · refine stuck (by
      mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some,
        «Machine.nfTerm», encNF, typeIn_eq, hc]) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, hc, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  have hs : «Machine.nFold» (encGlobals G) (leaf n) Γ (leaf k)
      (encVal (Internal.vnode (.natRec s k') (z :: m :: env)))
      [encOpt (Option.map encNF (some (z', bz))), encOpt (Option.map encNF (some (m', bm)))] =
      mk 14 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.natRec s k') (z :: m :: env)),
          RoseTree.node 0 (c :: Γ), leaf (k + 1),
          RoseTree.node 0 [encTerm z', encTerm m', ofBool (bz || bm)]]
        [encJobE s (Internal.vnode (.free k) [] :: env) k'] := by
    mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_some, «Machine.nfTerm»,
      «Machine.nfMark», encNF, typeIn_eq, hc, level_eq, «Machine.jobE», encJobE]
  have hEq : (o.nfNode G n Γ k (Internal.vnode (.natRec s k') (z :: m :: env))).bind
      (post rw o Γ k (Internal.vnode (.natRec s k') (z :: m :: env))) =
      ((o.eval s (Internal.vnode (.free k) [] :: env) k').bind (o.nf (c :: Γ) (k + 1))).bind
        fun x ↦ post rw o Γ k (Internal.vnode (.natRec s k') (z :: m :: env))
          (Term.natRec z' x.1 m', bz || bm) := by
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rcases o.eval s (RoseTree.node (.free k) [] :: env) k' with _ | v
    · rfl
    · simp only [Option.bind_some]
      rcases o.nf (c :: Γ) (k + 1) v with _ | ⟨s', bs⟩ <;> rfl
  rw [hs, hEq]
  exact nBody_reach hP hF Γ k _ (c :: Γ) (k + 1) _ s _ k'
    (fun x ↦ (Term.natRec z' x.1 m', bz || bm))
    (fun x ↦ by mach_simp [«Machine.nBuildT», Internal.vnode, vdata, «Machine.nfTerm», encNF,
      mNatRec_eq])
    (fun x ↦ by mach_simp [«Machine.nBuildB», Internal.vnode, vdata])

/-- The state of a fold of a list waiting for the normal forms of its start and of its list
reaches, within five rounds, the step of the normal form at the fold's. -/
theorem nFoldList_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree)
    (k : ℕ) (s : Term) (k' : ℕ) (z m : Val) (env : List Val) :
    Reach P F 5
      (mk 13 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.listRec s k') (z :: m :: env))]
        [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal z))),
          «Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))])
      (encOpt (((o.nfNode G n Γ k (Internal.vnode (.listRec s k') (z :: m :: env))).bind
        (post rw o Γ k (Internal.vnode (.listRec s k') (z :: m :: env)))).map encNF)) := by
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt none) →
      (o.nfNode G n Γ k (Internal.vnode (.listRec s k') (z :: m :: env))) = none →
      Reach P F r t (encOpt (((o.nfNode G n Γ k (Internal.vnode (.listRec s k')
        (z :: m :: env))).bind (post rw o Γ k (Internal.vnode (.listRec s k')
          (z :: m :: env)))).map encNF)) :=
    fun h h' ↦ by
      rw [h, h']
      exact reach_done _ _
  refine reach_step (adv13 _ _ _ _) ?_
  simp only [List.map_cons, List.map_nil, hF.nf_some]
  rw [hP.G_eq, hP.n_eq]
  rcases hz : o.nf Γ k z with _ | ⟨z', bz⟩
  · refine stuck (by mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none]) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      Option.bind_eq_bind, Option.bind_none]
  rcases hm : o.nf Γ k m with _ | ⟨m', bm⟩
  · refine stuck (by mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some])
      ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  rcases hc : Internal.typeIn G n Γ z' with _ | c
  · refine stuck (by
      mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some,
        «Machine.nfTerm», encNF, typeIn_eq, hc]) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, hc, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  rcases ha : (Internal.typeIn G n Γ m').bind Internal.listPart with _ | a
  · have ha' : «Base.bindO» (encOpt (Internal.typeIn G n Γ m')) «Language.listPart» =
        encOpt none := by
      rw [← ha]
      rcases Internal.typeIn G n Γ m' with _ | p
      · rfl
      · mach_simp [listPart_eq]
    refine stuck (by
      mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some,
        «Machine.nfTerm», encNF, typeIn_eq, hc, ha']) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, hc, ha, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  have ha' : «Base.bindO» (encOpt (Internal.typeIn G n Γ m')) «Language.listPart» =
      encOpt (some a) := by
    rw [← ha]
    rcases Internal.typeIn G n Γ m' with _ | p
    · rfl
    · mach_simp [listPart_eq]
  have hs : «Machine.nFold» (encGlobals G) (leaf n) Γ (leaf k)
      (encVal (Internal.vnode (.listRec s k') (z :: m :: env)))
      [encOpt (Option.map encNF (some (z', bz))), encOpt (Option.map encNF (some (m', bm)))] =
      mk 14 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.listRec s k') (z :: m :: env)),
          RoseTree.node 0 (c :: a :: Γ), leaf (k + 2),
          RoseTree.node 0 [encTerm z', encTerm m', ofBool (bz || bm)]]
        [encJobE s (Internal.vnode (.free ((k + 1 : ℕ) : ℤ)) [] ::
          Internal.vnode (.free k) [] :: env) k'] := by
    mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_some, «Machine.nfTerm»,
      «Machine.nfMark», encNF, typeIn_eq, hc, ha', level_eq, «Machine.jobE», encJobE]
  have hEq : (o.nfNode G n Γ k (Internal.vnode (.listRec s k') (z :: m :: env))).bind
      (post rw o Γ k (Internal.vnode (.listRec s k') (z :: m :: env))) =
      ((o.eval s (Internal.vnode (.free ((k + 1 : ℕ) : ℤ)) [] ::
          Internal.vnode (.free k) [] :: env) k').bind (o.nf (c :: a :: Γ) (k + 2))).bind
        fun x ↦ post rw o Γ k (Internal.vnode (.listRec s k') (z :: m :: env))
          (Term.listRec z' x.1 m', bz || bm) := by
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hz,
      hm, hc, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rcases o.eval s (RoseTree.node (.free ((k + 1 : ℕ) : ℤ)) [] ::
      RoseTree.node (.free k) [] :: env) k' with _ | v
    · rfl
    · simp only [Option.bind_some]
      rcases o.nf (c :: a :: Γ) (k + 2) v with _ | ⟨s', bs⟩ <;> rfl
  rw [hs, hEq]
  exact nBody_reach hP hF Γ k _ (c :: a :: Γ) (k + 2) _ s _ k'
    (fun x ↦ (Term.listRec z' x.1 m', bz || bm))
    (fun x ↦ by mach_simp [«Machine.nBuildT», Internal.vnode, vdata, «Machine.nfTerm», encNF,
      mListRec_eq])
    (fun x ↦ by mach_simp [«Machine.nBuildB», Internal.vnode, vdata])

/-- The state of a fold of a rose tree waiting for the normal form of its tree reaches, within
five rounds, the step of the normal form at the fold's. -/
theorem nFoldRose_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree)
    (k : ℕ) (c : Tree) (s : Term) (k' : ℕ) (m : Val) (env : List Val) :
    Reach P F 5
      (mk 13 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.roseRec c s k') (m :: env))]
        [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))])
      (encOpt (((o.nfNode G n Γ k (Internal.vnode (.roseRec c s k') (m :: env))).bind
        (post rw o Γ k (Internal.vnode (.roseRec c s k') (m :: env)))).map encNF)) := by
  have stuck : ∀ {r : ℕ} {t : Tree}, t = «Machine.msDone» (encOpt none) →
      (o.nfNode G n Γ k (Internal.vnode (.roseRec c s k') (m :: env))) = none →
      Reach P F r t (encOpt (((o.nfNode G n Γ k (Internal.vnode (.roseRec c s k')
        (m :: env))).bind (post rw o Γ k (Internal.vnode (.roseRec c s k')
          (m :: env)))).map encNF)) :=
    fun h h' ↦ by
      rw [h, h']
      exact reach_done _ _
  refine reach_step (adv13 _ _ _ _) ?_
  simp only [List.map_cons, List.map_nil, hF.nf_some]
  rw [hP.G_eq, hP.n_eq]
  rcases hm : o.nf Γ k m with _ | ⟨m', bm⟩
  · refine stuck (by mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none]) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hm,
      Option.bind_eq_bind, Option.bind_none]
  rcases hp : (Internal.typeIn G n Γ m').bind Internal.roseParts with _ | p
  · have hp' : «Base.bindO» (encOpt (Internal.typeIn G n Γ m')) «Language.roseLabel» =
        encOpt none := by
      have h := congrArg (Option.map Prod.fst) hp
      rw [Option.map_none] at h
      rw [← h]
      rcases Internal.typeIn G n Γ m' with _ | q
      · rfl
      · mach_simp [roseLabel_eq]
    refine stuck (by
      mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_none, bindS_some,
        «Machine.nfTerm», encNF, typeIn_eq, hp']) ?_
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hm,
      hp, Option.bind_eq_bind, Option.bind_some, Option.bind_none]
  have hp' : «Base.bindO» (encOpt (Internal.typeIn G n Γ m')) «Language.roseLabel» =
      encOpt (some p.1) := by
    have h := congrArg (Option.map Prod.fst) hp
    rw [Option.map_some] at h
    rw [← h]
    rcases Internal.typeIn G n Γ m' with _ | q
    · rfl
    · mach_simp [roseLabel_eq]
  have hs : «Machine.nFold» (encGlobals G) (leaf n) Γ (leaf k)
      (encVal (Internal.vnode (.roseRec c s k') (m :: env)))
      [encOpt (Option.map encNF (some (m', bm)))] =
      mk 14 [RoseTree.node 0 Γ, leaf k, encVal (Internal.vnode (.roseRec c s k') (m :: env)),
          RoseTree.node 0 (prod p.1 (list c) :: Γ), leaf (k + 1),
          RoseTree.node 0 [encTerm m', ofBool bm]]
        [encJobE s (Internal.vnode (.free k) [] :: env) k'] := by
    mach_simp [«Machine.nFold», Internal.vnode, vdata, bindS_some, «Machine.nfTerm»,
      «Machine.nfMark», encNF, typeIn_eq, hp', level_eq, «Machine.jobE», encJobE,
      Theory.mirror_prod, Theory.mirror_list]
  have hEq : (o.nfNode G n Γ k (Internal.vnode (.roseRec c s k') (m :: env))).bind
      (post rw o Γ k (Internal.vnode (.roseRec c s k') (m :: env))) =
      ((o.eval s (Internal.vnode (.free k) [] :: env) k').bind
          (o.nf (prod p.1 (list c) :: Γ) (k + 1))).bind
        fun x ↦ post rw o Γ k (Internal.vnode (.roseRec c s k') (m :: env))
          (Term.roseRec c x.1 m', bm) := by
    simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node, hm,
      hp, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rcases o.eval s (RoseTree.node (.free k) [] :: env) k' with _ | v
    · rfl
    · simp only [Option.bind_some]
      rcases o.nf (prod p.1 (list c) :: Γ) (k + 1) v with _ | ⟨s', bs⟩ <;> rfl
  rw [hs, hEq]
  exact nBody_reach hP hF Γ k _ (prod p.1 (list c) :: Γ) (k + 1) _ s _ k'
    (fun x ↦ (Term.roseRec c x.1 m', bm))
    (fun x ↦ by mach_simp [«Machine.nBuildT», Internal.vnode, vdata, «Machine.nfTerm», encNF,
      mRoseRec_eq])
    (fun x ↦ by mach_simp [«Machine.nBuildB», Internal.vnode, vdata])

set_option maxRecDepth 8000 in
/-- The state of a weak head normal form's normal form reaches, within five rounds, the step of
the normal form at its node's. -/
theorem nNode_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (w : Val) :
    Reach P F 5 («Machine.nNode» P.rw Γ (leaf k) (encVal w))
      (encOpt (((o.nfNode G n Γ k w).bind (post rw o Γ k w)).map encNF)) := by
  obtain ⟨l, cs, rfl⟩ := exists_node w
  cases l with
  | free l =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.free l) cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node (.free l) cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node (.free l) cs)).bind
        (post rw o Γ k (RoseTree.node (.free l) cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node (.free l) cs)
          (Internal.readStep k (.free l) (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k (.free l) cs) (by omega)
  | star =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .star cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .star cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .star cs)).bind
        (post rw o Γ k (RoseTree.node .star cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .star cs)
          (Internal.readStep k .star (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .star cs) (by omega)
  | pair =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .pair cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .pair cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .pair cs)).bind
        (post rw o Γ k (RoseTree.node .pair cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .pair cs)
          (Internal.readStep k .pair (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .pair cs) (by omega)
  | clo a b k' =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.clo a b k') cs)) =
        mk 14 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node (.clo a b k') cs),
            RoseTree.node 0 (a :: Γ), leaf (k + 1), RoseTree.node 0 []]
          [encJobE b (Internal.vnode (.free k) [] :: cs) k'] := by
      mach_simp [«Machine.nNode», vdata, level_eq, «Machine.jobE», encJobE, Internal.vnode]
    have hEq : (o.nfNode G n Γ k (RoseTree.node (.clo a b k') cs)).bind
        (post rw o Γ k (RoseTree.node (.clo a b k') cs)) =
        ((o.eval b (Internal.vnode (.free k) [] :: cs) k').bind (o.nf (a :: Γ) (k + 1))).bind
          fun x ↦ post rw o Γ k (RoseTree.node (.clo a b k') cs) (Term.lam a x.1, x.2) := by
      simp only [Machine.nfNode, Internal.vnode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases o.eval b (RoseTree.node (.free k) [] :: cs) k' with _ | v
      · rfl
      · simp only [Option.bind_some]
        rcases o.nf (a :: Γ) (k + 1) v with _ | ⟨t, bt⟩ <;> rfl
    rw [hs, hEq]
    exact reach_le (nBody_reach hP hF Γ k _ (a :: Γ) (k + 1) [] b _ k'
      (fun x ↦ (Term.lam a x.1, x.2))
      (fun x ↦ by mach_simp [«Machine.nBuildT», vdata, «Machine.nfTerm», encNF, mLam_eq])
      (fun x ↦ by mach_simp [«Machine.nBuildB», vdata, «Machine.nfMark», encNF])) (by omega)
  | arr j θ =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.arr j θ) cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node (.arr j θ) cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node (.arr j θ) cs)).bind
        (post rw o Γ k (RoseTree.node (.arr j θ) cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node (.arr j θ) cs)
          (Internal.readStep k (.arr j θ) (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k (.arr j θ) cs) (by omega)
  | app =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .app cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .app cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .app cs)).bind
        (post rw o Γ k (RoseTree.node .app cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .app cs)
          (Internal.readStep k .app (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .app cs) (by omega)
  | fst =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .fst cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .fst cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .fst cs)).bind
        (post rw o Γ k (RoseTree.node .fst cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .fst cs)
          (Internal.readStep k .fst (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .fst cs) (by omega)
  | snd =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .snd cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .snd cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .snd cs)).bind
        (post rw o Γ k (RoseTree.node .snd cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .snd cs)
          (Internal.readStep k .snd (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .snd cs) (by omega)
  | natRec s k' =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    case cons.cons =>
      have hs : «Machine.nNode» P.rw Γ (leaf k)
          (encVal (RoseTree.node (.natRec s k') (z :: m :: env))) =
          mk 13 [RoseTree.node 0 Γ, leaf k,
              encVal (Internal.vnode (.natRec s k') (z :: m :: env))]
            [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal z))),
              «Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.nNode», vdata, Internal.vnode]
      rw [hs]
      exact nFoldNat_reach hP hF Γ k s k' z m env
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.natRec s k') [])) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.natRec s k') []))
            (encTerm (Internal.readBack k (RoseTree.node (.natRec s k') []))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.natRec s k') [])
        (Internal.readBack k (RoseTree.node (.natRec s k') []), false)) (by omega)
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.natRec s k') [z])) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.natRec s k') [z]))
            (encTerm (Internal.readBack k (RoseTree.node (.natRec s k') [z]))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.natRec s k') [z])
        (Internal.readBack k (RoseTree.node (.natRec s k') [z]), false)) (by omega)
  | listRec s k' =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    case cons.cons =>
      have hs : «Machine.nNode» P.rw Γ (leaf k)
          (encVal (RoseTree.node (.listRec s k') (z :: m :: env))) =
          mk 13 [RoseTree.node 0 Γ, leaf k,
              encVal (Internal.vnode (.listRec s k') (z :: m :: env))]
            [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal z))),
              «Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.nNode», vdata, Internal.vnode]
      rw [hs]
      exact nFoldList_reach hP hF Γ k s k' z m env
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.listRec s k') [])) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.listRec s k') []))
            (encTerm (Internal.readBack k (RoseTree.node (.listRec s k') []))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.listRec s k') [])
        (Internal.readBack k (RoseTree.node (.listRec s k') []), false)) (by omega)
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.listRec s k') [z])) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.listRec s k') [z]))
            (encTerm (Internal.readBack k (RoseTree.node (.listRec s k') [z]))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.listRec s k') [z])
        (Internal.readBack k (RoseTree.node (.listRec s k') [z]), false)) (by omega)
  | roseRec c s k' =>
    rcases cs with _ | ⟨m, env⟩
    case cons =>
      have hs : «Machine.nNode» P.rw Γ (leaf k)
          (encVal (RoseTree.node (.roseRec c s k') (m :: env))) =
          mk 13 [RoseTree.node 0 Γ, leaf k,
              encVal (Internal.vnode (.roseRec c s k') (m :: env))]
            [«Machine.jobN» Γ (leaf k) (encOpt (some (encVal m)))] := by
        mach_simp [«Machine.nNode», vdata, Internal.vnode]
      rw [hs]
      exact nFoldRose_reach hP hF Γ k c s k' m env
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.roseRec c s k') [])) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.roseRec c s k') []))
            (encTerm (Internal.readBack k (RoseTree.node (.roseRec c s k') [])))
            (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.roseRec c s k') [])
        (Internal.readBack k (RoseTree.node (.roseRec c s k') []), false)) (by omega)
  | defn j θ =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.defn j θ) cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node (.defn j θ) cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node (.defn j θ) cs)).bind
        (post rw o Γ k (RoseTree.node (.defn j θ) cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node (.defn j θ) cs)
          (Internal.readStep k (.defn j θ) (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k (.defn j θ) cs) (by omega)
  | eq =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .eq cs)) =
        mk 16 [RoseTree.node 0 Γ, leaf k, encVal (RoseTree.node .eq cs)]
          (cs.map fun c ↦ «Machine.jobN» Γ (leaf k) (encOpt (some (encVal c)))) := by
      mach_simp [«Machine.nNode», vdata, «Machine.jobN»]
    have hEq : (o.nfNode G n Γ k (RoseTree.node .eq cs)).bind
        (post rw o Γ k (RoseTree.node .eq cs)) =
        (cs.mapM (o.nf Γ k)).bind fun rs ↦ post rw o Γ k (RoseTree.node .eq cs)
          (Internal.readStep k .eq (rs.map Prod.fst), rs.any Prod.snd) := by
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.pure_def]
      rcases cs.mapM (o.nf Γ k) with _ | rs <;> rfl
    rw [hs, hEq]
    exact reach_le (nKids_reach hP hF Γ k .eq cs) (by omega)
  | term t k' =>
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node (.term t k') cs)) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node (.term t k') cs))
            (encTerm (Internal.readBack k (RoseTree.node (.term t k') cs))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node (.term t k') cs)
        (Internal.readBack k (RoseTree.node (.term t k') cs), false)) (by omega)
  | delay =>
    · have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .delay cs)) =
          «Machine.nPost» P.rw Γ (leaf k) (encVal (RoseTree.node .delay cs))
            (encTerm (Internal.readBack k (RoseTree.node .delay cs))) (ofBool false) := by
        rw [← readBack_eq]
        mach_simp [«Machine.nNode», vdata]
        rfl
      rw [hs]
      simp only [Machine.nfNode, RoseTree.label_node, RoseTree.children_node, Option.bind_some]
      exact reach_le (nPost_reach hP hF Γ k (RoseTree.node .delay cs)
        (Internal.readBack k (RoseTree.node .delay cs), false)) (by omega)
  | fail =>
    have hs : «Machine.nNode» P.rw Γ (leaf k) (encVal (RoseTree.node .fail cs)) =
        «Machine.msDone» (encOpt none) := by
      mach_simp [«Machine.nNode», vdata]
    rw [hs]
    simp only [Machine.nfNode, RoseTree.label_node, Option.bind_none, Option.map_none]
    exact reach_done _ _

/-- The rounds of the state a normal form starts in are the step of the machine's normal form,
at a function of jobs related to the operations of the depth below. -/
theorem nStart_reach (hP : PRel P G n unfold kl kc rw) (hF : JRel F o) (Γ : List Tree) (k : ℕ)
    (ov : Option Val) :
    Reach P F 6 («Machine.msStart» (encJobN Γ k ov))
      (encOpt ((ov.bind (Machine.nfStep G n rw o Γ k)).map encNF)) := by
  have hs : «Machine.msStart» (encJobN Γ k ov) =
      mk 12 [RoseTree.node 0 Γ, leaf k] [encJobW ov] := by
    mach_simp [«Machine.msStart», encJobN, encJobW, «Machine.jobW»]
  rw [hs]
  refine reach_step (adv12 _ _ _) ?_
  rw [hF.whnf]
  rcases ov with _ | v
  · rw [Option.bind_none, Option.map_none, bindS_none]
    exact reach_done _ _
  · rw [Option.bind_some, Option.bind_some, nfStep_eq]
    rcases o.whnf v with _ | w
    · rw [Option.map_none, bindS_none]
      exact reach_done _ _
    · rw [Option.map_some, bindS_some, Option.bind_some]
      exact nNode_reach hP hF Γ k w

end Nf

/-! The machine at every depth, and the reduction. -/

section Reduce

variable {P : Params} {G : Internal.Globals} {n : ℕ} {unfold : ℕ → Bool} {kl kc : ℕ}
  {rw : List Tree → ℕ → Term → Option Term}

/-- The mirror's result of a job within a depth of recursion is the machine's operation at that
depth: the value of a term, the weak head normal form of an optional value, and the normal form
of an optional value's term. -/
theorem machJ_rel (hP : PRel P G n unfold kl kc rw) (fuel : ℕ) :
    JRel (machJ P fuel) (Internal.machine G n unfold kl kc rw fuel) :=
  Nat.rec
    ⟨fun _ _ _ ↦ rfl, fun ov ↦ by cases ov <;> rfl, fun _ _ ov ↦ by cases ov <;> rfl⟩
    (fun m ih ↦
      ⟨fun t vs k ↦ result_of_reach (eStart_reach hP ih t vs k) (by omega),
        fun ov ↦ by
          have hs : «Machine.msStart» (encJobW ov) =
              «Machine.bindS» (encOpt (ov.map encVal)) «Machine.wStart» := by
            mach_simp [«Machine.msStart», encJobW]
          change «Machine.msResult» ((advBy P (machJ P m))^[6] («Machine.msStart» (encJobW ov))) = _
          rw [hs]
          rcases ov with _ | v
          · rw [Option.map_none, bindS_none]
            exact result_of_reach (reach_done 0 _) (by omega)
          · rw [Option.map_some, bindS_some]
            exact result_of_reach (wStart_reach hP ih v) (by omega),
        fun Γ k ov ↦ result_of_reach (nStart_reach hP ih Γ k ov) le_rfl⟩) fuel

/-- The mirror's reduction of an encoded term in a context by the machine within a depth of
recursion, at related parameters, is the encoding of the machine's reduction. -/
theorem machineReduce_eq (hP : PRel P G n unfold kl kc rw) (fuel : ℕ) (Γ : List Tree)
    (t : Term) :
    «Machine.machineReduce» P.G P.n P.unf P.kl P.kc P.rw (leaf fuel) Γ (encTerm t) =
      encOpt ((Internal.machineReduce G n unfold kl kc rw fuel Γ t).map encTerm) := by
  have hJ := machJ_rel hP fuel
  have he := hJ.eval t [] 0
  have hn := hJ.nf Γ 0 ((Internal.machine G n unfold kl kc rw fuel).eval t [] 0)
  simp only [«Machine.machineReduce», machB_eq, single_eq, List.map_cons, List.map_nil, at_eq,
    List.getD_cons_zero]
  rw [show «Machine.jobE» (encTerm t) [] (leaf 0) = encJobE t [] 0 from rfl, he, jobN_eq, hn]
  simp only [Internal.machineReduce, Option.bind_eq_bind]
  rcases (Internal.machine G n unfold kl kc rw fuel).eval t [] 0 with _ | v
  · rfl
  · simp only [Option.bind_some]
    rcases (Internal.machine G n unfold kl kc rw fuel).nf Γ 0 v with _ | ⟨u, b⟩
    · rfl
    · mach_simp [«Machine.nfTerm», encNF]

end Reduce

end GebTests.Prototypes.FreeTopos.Agreement.Machine

end
