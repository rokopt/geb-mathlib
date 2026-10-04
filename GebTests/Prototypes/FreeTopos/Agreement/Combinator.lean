/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic
public import GebTests.Prototypes.FreeTopos.Agreement.Infer
public import GebTests.Prototypes.FreeTopos.Agreement.Theory
public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import Geb.Prototypes.FreeTopos.Prover

set_option doc.verso true in
/-!
# The combinator prover written in Geb

The functions of {lit}`bootstrap/free-topos/combinator.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the prover of the theory of an elementary topos
({name}`Geb.FreeTopos.Prover.normalize` and the definitions beside it) at every encoded input and
related state. A computation of the prover is a function from a scope and a state to the optional
pair of its value and the state after it; the mirror's is a function of trees, related to the
prover's when at every scope and related states the two fail together or give the value's
encoding and related states. The mirror's state records typings and normal forms in association
lists, the latest first, where the prover's records them in hash tables, a list related to a table
when their lookups agree.

## Main definitions

* {lit}`TRel`, {lit}`SRel` — the relations of association lists to tables and of the mirror's
  states to the prover's.
* {lit}`PMRel` — the relation of the mirror's computations to the prover's.
* {lit}`encTy`, {lit}`encMS` — the encodings of typings and of a match's states.

## Main statements

* {lit}`typers_rel`, {lit}`typeTerm_rel` — the typing agrees.
* {lit}`matchPat_eq`, {lit}`bridge_rel`, {lit}`applyRule_rel`, {lit}`rewriteRoot_rel` — the match
  and the rewriting agree.
* {lit}`normalizers_rel`, {lit}`normalize_rel` — the normalization agrees.
* {lit}`byNorm_rel`, {lit}`byNatInduction_rel`, {lit}`byListParamInduction_rel` and the proofs
  beside them agree.
* {lit}`proveSeq_eq`, {lit}`normalizeThm_eq`, {lit}`libraryWith_eq` — the developments agree.

## Tags

prover, elementary topos, partial Horn logic, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Combinator

open Geb Geb.Kernel Geb.FreeTopos Geb.FreeTopos.Prover
  GebTests.Prototypes.FreeTopos.Agreement.Encode GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.PartialHorn GebTests.Prototypes.FreeTopos.Agreement.Theory
  GebTests.Prototypes.FreeTopos.Agreement.Infer GebTests.Prototypes.FreeTopos.Agreement.Fold
open Geb.PartialHorn (Table Scope Seq Eqn Development Defn Sig)
open scoped FinEnum

/-! Tables. -/

/-- A list of keys with values, the latest first, and a table agree at every key. -/
def TRel {β : Type} (l : List (Tree × β)) (tb : Table β) : Prop :=
  0 < tb.buckets.size ∧ ∀ t, (l.find? (·.1 == t)).map Prod.snd = tb.find? t

/-- The empty list and the empty table agree. -/
theorem tRel_empty {β : Type} : TRel ([] : List (Tree × β)) {} := by
  refine ⟨by change 0 < (Array.replicate 4096 []).size; rw [Array.size_replicate]; decide,
    fun t ↦ ?_⟩
  simp only [List.find?_nil, Option.map_none, Table.find?, Array.getElem?_replicate]
  split <;> simp

/-- Adding a key's value to agreeing lists and tables keeps them agreeing. -/
theorem tRel_insert {β : Type} (l : List (Tree × β)) (tb : Table β) (h : TRel l tb) (t : Tree)
    (b : β) : TRel ((t, b) :: l) (tb.insert t b) := by
  obtain ⟨hs, hf⟩ := h
  have hsz : (tb.insert t b).buckets.size = tb.buckets.size := Array.size_modify ..
  refine ⟨hsz ▸ hs, fun t' ↦ ?_⟩
  have hidx : ∀ u, (tb.insert t b).index u = tb.index u := fun u ↦ by
    simp only [Table.index, hsz]
  have hlt : tb.index t < tb.buckets.size := Nat.mod_lt _ hs
  have hfind : (tb.insert t b).find? t' =
      (((tb.buckets[tb.index t']?.map fun l ↦
          if tb.index t = tb.index t' then (t, b) :: l else l).bind
        fun l ↦ l.find? (fun p : Tree × β ↦ p.1 == t')).map Prod.snd) := by
    simp only [Table.find?]
    rw [hidx t']
    simp only [Table.insert, Array.getElem?_modify]
    split <;> simp_all
  rw [hfind, List.find?_cons]
  by_cases htt : t = t'
  · subst htt
    simp only [beq_self_eq_true, Option.map_some, ite_true, Array.getElem?_eq_getElem hlt,
      Option.bind_some, List.find?_cons]
  · have hb : (t == t') = false := beq_false_of_ne htt
    simp only [hb]
    rw [hf t']
    simp only [Table.find?]
    rcases tb.buckets[tb.index t']? with _ | bk
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      split <;> simp only [List.find?_cons, hb]

/-! Encodings and the relations of states and computations. -/

/-- A scope as the node of its variables' sorts and its hypotheses. -/
def encScope (sc : Scope) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (sc.ctx.map leaf), RoseTree.node 0 (sc.hyps.map encEqn)]

/-- A typing as the node of its term, sort, definedness certificate and bounds with their
certificates. -/
def encTy (y : Ty) : Tree :=
  RoseTree.node 0 [y.term, leaf y.sort, y.dfd, y.lo, y.loCert, y.hi, y.hiCert]

/-- A key with its value as the node of the key and the value's encoding. -/
def encKV {β : Type} (e : β → Tree) (p : Tree × β) : Tree := RoseTree.node 0 [p.1, e p.2]

/-- A state written in Geb and a state are related: the tables agree with lists of their keys'
values, and the state written in Geb is the node of the development's entries, those lists, the
definitions in force, the extended signature and whether the typing is inferred. -/
def SRel (st' : Tree) (st : St) : Prop :=
  ∃ (lm : List (Tree × Ty)) (ln : List (Tree × (Tree × Tree))), TRel lm st.memo ∧
    TRel ln st.nfs ∧ st' = RoseTree.node 0 [RoseTree.node 0 (st.dev.toList.map encDevEntry),
      RoseTree.node 0 (lm.map (encKV encTy)), RoseTree.node 0 (ln.map (encKV encPair)),
      RoseTree.node 0 (st.defs.map encDefn), RoseTree.node 0 (st.sig.map encOpSig),
      ofBool st.infer]

/-- A computation written in Geb and a computation are related, at an encoding of values, when
at every scope and related states they fail together or give the value's encoding and related
states. -/
def PMRel {α : Type} (e : α → Tree) (m' : Tree → Tree → Tree) (m : PM α) : Prop :=
  ∀ sc st' st, SRel st' st → match (m.run sc).run st with
    | none => m' (encScope sc) st' = leaf 0
    | some (a, st₂) => ∃ st₂', SRel st₂' st₂ ∧
        m' (encScope sc) st' = RoseTree.node 1 [RoseTree.node 0 [e a, st₂']]

/-! The monad. -/

/-- The mirror's computation of a value. -/
theorem pmPure_rel {α : Type} (e : α → Tree) (a : α) :
    PMRel e («Combinator.pmPure» (e a)) (pure a) := fun sc st' st h ↦ by
  simp only [ReaderT.run_pure, StateT.run_pure]
  exact ⟨st', h, rfl⟩

/-- The mirror's failure. -/
theorem pmFail_rel {α : Type} (e : α → Tree) :
    PMRel e «Combinator.pmFail» (failure : PM α) := fun _ _ _ _ ↦ by
  simp only [ReaderT.run_failure, StateT.run_failure]
  rfl

/-- The mirror's composition of a computation with a computation from its value. -/
theorem pmBind_rel {α β : Type} (e₁ : α → Tree) (e₂ : β → Tree) (m' : Tree → Tree → Tree)
    (m : PM α) (hm : PMRel e₁ m' m) (k' : Tree → Tree → Tree → Tree) (k : α → PM β)
    (hk : ∀ a, PMRel e₂ (k' (e₁ a)) (k a)) :
    PMRel e₂ («Combinator.pmBind» m' k') (m >>= k) := by
  intro sc st' st h
  have h1 := hm sc st' st h
  simp only [ReaderT.run_bind, StateT.run_bind]
  rcases hr : (m.run sc).run st with _ | ⟨a, st₂⟩
  · rw [hr] at h1
    simp only [«Combinator.pmBind», h1]
    rfl
  · rw [hr] at h1
    obtain ⟨st₂', h2, h3⟩ := h1
    simp only [«Combinator.pmBind», h3]
    exact hk a sc st₂' st₂ h2

/-- The mirror's first of two computations that succeeds. -/
theorem pmOr_rel {α : Type} (e : α → Tree) (a' b' : Tree → Tree → Tree) (a b : PM α)
    (ha : PMRel e a' a) (hb : PMRel e b' b) :
    PMRel e («Combinator.pmOr» a' b') (a <|> b) := by
  intro sc st' st h
  have h1 := ha sc st' st h
  simp only [ReaderT.run_orElse, StateT.run_orElse]
  rcases hr : (a.run sc).run st with _ | ⟨x, st₂⟩
  · rw [hr] at h1
    simp only [«Combinator.pmOr», h1]
    exact hb sc st' st h
  · rw [hr] at h1
    obtain ⟨st₂', h2, h3⟩ := h1
    simp only [«Combinator.pmOr», h3]
    exact ⟨st₂', h2, rfl⟩

/-- The mirror's values of computations from a list's elements, in turn. -/
theorem pmMapM_rel {α β : Type} (e : α → Tree) (g : β → Tree) (f' : Tree → Tree → Tree → Tree)
    (f : β → PM α) :
    ∀ xs : List β, (∀ x ∈ xs, PMRel e (f' (g x)) (f x)) →
      PMRel (fun ys ↦ RoseTree.node 0 (ys.map e)) («Combinator.pmMapM» f' (xs.map g))
        (xs.mapM f) := by
  refine List.rec (fun _ ↦ ?_) fun x xs ih hx ↦ ?_
  · simp only [«Combinator.pmMapM», List.map_nil, foldr_eq, List.foldr_nil, List.mapM_nil]
    exact pmPure_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) []
  · have ih' := ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
    simp only [«Combinator.pmMapM», foldr_eq] at ih' ⊢
    simp only [List.map_cons, List.foldr_cons, List.mapM_cons]
    refine pmBind_rel e _ _ _ (hx x List.mem_cons_self) _ _ fun y ↦ ?_
    refine pmBind_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) _ _ _ ih' _ _ fun ys ↦ ?_
    simp only [children_node]
    exact pmPure_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) (y :: ys)

/-- The mirror's guard. -/
theorem pmGuard_rel (b : Bool) :
    PMRel (fun _ ↦ leaf 0) («Combinator.pmGuard» (ofBool b)) (guard b : PM Unit) := by
  intro sc st' st h
  cases b
  · simp only [guard, ite_false, Bool.false_eq_true, ReaderT.run_failure, StateT.run_failure]
    rfl
  · simp only [guard, ite_true, ReaderT.run_pure, StateT.run_pure]
    exact ⟨st', h, rfl⟩

/-! Certificates, scopes and lemmas. -/

@[simp] theorem cHyp_eq (i : ℕ) : «Combinator.cHyp» (leaf i) = PartialHorn.Cert.hyp i :=
  rfl

@[simp] theorem cRefl_eq (i : ℕ) :
    «Combinator.cRefl» (leaf i) = PartialHorn.Cert.refl i := rfl

@[simp] theorem cSymm_eq (p : Tree) : «Combinator.cSymm» p = PartialHorn.Cert.symm p := rfl

@[simp] theorem cTrans_eq (p q : Tree) :
    «Combinator.cTrans» p q = PartialHorn.Cert.trans p q := rfl

@[simp] theorem cCong_eq (d : Tree) (ps : List Tree) :
    «Combinator.cCong» d ps = PartialHorn.Cert.cong d ps := rfl

@[simp] theorem cStrict_eq (j : ℕ) (p : Tree) :
    «Combinator.cStrict» (leaf j) p = PartialHorn.Cert.strict j p := rfl

@[simp] theorem cAx_eq (j : ℕ) (ts ds hs : List Tree) :
    «Combinator.cAx» (leaf j) ts ds hs = PartialHorn.Cert.ax j ts ds hs := by
  simp only [«Combinator.cAx», append_eq, PartialHorn.Cert.ax, List.append_assoc]
  rfl

@[simp] theorem cThm_eq (j : ℕ) (ts ds hs : List Tree) :
    «Combinator.cThm» (leaf j) ts ds hs = PartialHorn.Cert.thm j ts ds hs := by
  simp only [«Combinator.cThm», append_eq, PartialHorn.Cert.thm, List.append_assoc]
  rfl

@[simp] theorem scCtx_eq (sc : Scope) :
    «Combinator.scCtx» (encScope sc) = sc.ctx.map leaf := by
  simp [«Combinator.scCtx», encScope]

@[simp] theorem scHyps_eq (sc : Scope) :
    «Combinator.scHyps» (encScope sc) = sc.hyps.map encEqn := by
  simp [«Combinator.scHyps», encScope]

@[simp] theorem scSeq_eq (sc : Scope) (q : Eqn) :
    «Combinator.scSeq» (encScope sc) (encEqn q) = encSeq (sc.seq q) := by
  simp [«Combinator.scSeq», Scope.seq]

@[simp] theorem scCite_eq (sc : Scope) (j : ℕ) :
    «Combinator.scCite» (encScope sc) (leaf j) = sc.cite j := by
  simp [«Combinator.scCite», Scope.cite, Function.comp_def]

/-- The failure of an optional value. -/
theorem option_failure {α : Type} : (failure : Option α) = none := rfl

/-- The run of reading the state. -/
theorem stateT_get_run (st : St) : (StateT.get : StateT St Option St).run st = some (st, st) :=
  rfl

/-- The run of writing the state. -/
theorem stateT_set_run (st st₁ : St) :
    (StateT.set st₁ : StateT St Option PUnit).run st = some (⟨⟩, st₁) := rfl

/-- The unfolding of the prover's monad: reading the scope, the state's reading and writing,
composition and values, with the given lemmas. -/
local macro "pm_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [read, readThe, MonadReaderOf.read, get, getThe, MonadStateOf.get, set, modify,
    modifyGet, MonadStateOf.modifyGet, bind_pure_comp, ReaderT.run_bind, ReaderT.run_read,
    ReaderT.run_monadLift, monadLift_self, ReaderT.run_map, ReaderT.run_pure, pure_bind,
    StateT.run_bind, StateT.run_map, StateT.run_pure, StateT.run_get, StateT.run_set,
    StateT.run_modifyGet, Option.map_eq_map, Option.bind_eq_bind, Option.bind_some,
    Option.map_some, stateT_get_run, stateT_set_run, Option.pure_def, option_failure,
    Option.bind_none, ReaderT.run_failure, StateT.run_failure, $ls,*])

/-- The run of adding a lemma. -/
theorem addLemma_run (q : Eqn) (c : Tree) (sc : Scope) (st : St) :
    ((addLemma q c).run sc).run st =
      some (sc.cite st.dev.size, { st with dev := st.dev.push (sc.seq q, c) }) := by
  pm_simp [addLemma]

/-- The mirror's addition of a lemma. -/
theorem addLemma_rel (q : Eqn) (c : Tree) :
    PMRel id («Combinator.addLemma» (encEqn q) c) (addLemma q c) := by
  intro sc st' st h
  rw [addLemma_run]
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  refine ⟨_, ⟨lm, ln, hm, hn, rfl⟩, ?_⟩
  mirror_simp [«Combinator.addLemma», «Combinator.stDev»,
    «Combinator.withDev», «Combinator.pst», «Theory.l2», scSeq_eq,
    scCite_eq, Array.toList_push, Array.size_eq_length_toList, List.map_append, List.map_cons,
    List.map_nil, encDevEntry, id]
  rfl

/-! The table of typings and the certificates of definedness and of equations. -/

/-- The mirror's value of a key in a list of keys with encoded values, the latest first. -/
theorem tableFind_eq {β : Type} (e : β → Tree) (t : Tree) :
    ∀ l : List (Tree × β), «Combinator.tableFind» (l.map (encKV e)) t =
      encOpt ((l.find? (·.1 == t)).map (e ∘ Prod.snd)) :=
  List.rec rfl fun p l ih ↦ by
    simp only [«Combinator.tableFind», foldr_eq, List.map_cons, List.foldr_cons,
      List.find?_cons] at ih ⊢
    rw [ih]
    by_cases h : p.1 = t
    · simp [encKV, h]
      rfl
    · simp [encKV, h, beq_false_of_ne h]

/-- The mirror's typing of a term, if it has been typed. -/
theorem lookup_rel (t : Tree) :
    PMRel (fun o ↦ encOpt (o.map encTy)) («Combinator.lookup» t) (lookup t) := by
  intro sc st' st h
  pm_simp [lookup]
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  refine ⟨_, ⟨lm, ln, hm, hn, rfl⟩, ?_⟩
  mirror_simp [«Combinator.lookup», «Combinator.stMemo», «Theory.l2»,
    tableFind_eq, ← hm.2 t, Option.map_map]
  rfl

/-- The mirror's record of a typing. -/
theorem memoize_rel (y : Ty) :
    PMRel (fun _ ↦ leaf 0) («Combinator.memoize» (encTy y)) (memoize y) := by
  intro sc st' st h
  pm_simp [memoize]
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  refine ⟨_, ⟨(y.term, y) :: lm, ln, tRel_insert lm st.memo hm y.term y, hn, rfl⟩, ?_⟩
  mirror_simp [«Combinator.memoize», «Combinator.stMemo»,
    «Combinator.withMemo», «Combinator.tableInsert», «Combinator.pst»,
    «Theory.l2», «Combinator.tyT»]
  rfl

/-- The fields of an encoded state. -/
theorem stInfer_srel {st' : Tree} {st : St} (h : SRel st' st) :
    «Combinator.stInfer» st' = ofBool st.infer := by
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  mirror_simp [«Combinator.stInfer»]

/-- The mirror's record of a typing, and the typing. -/
theorem memoRet_rel (y : Ty) :
    PMRel encTy («Combinator.memoRet» (encTy y)) (memoize y >>= fun _ ↦ pure y) := by
  unfold «Combinator.memoRet»
  exact pmBind_rel _ _ _ _ (memoize_rel y) _ _ fun _ ↦ pmPure_rel encTy y

/-- The mirror's certificate of a term's definedness. -/
theorem dfdCert_rel (t c : Tree) :
    PMRel id («Combinator.dfdCert» t c) (dfdCert t c) := by
  intro sc st' st h
  have hi := stInfer_srel h
  pm_simp [dfdCert]
  cases hb : st.infer
  · have := addLemma_rel (dfd t) c sc st' st h
    mirror_simp [«Combinator.dfdCert», hi, hb, dfd_eq] at this ⊢
    exact this
  · mirror_simp [«Combinator.dfdCert», hi, hb]
    exact ⟨st', h, rfl⟩

/-- The mirror's certificate of an equation between objects of one canonical form. -/
theorem eqCert_rel (q : Eqn) (c : Tree) :
    PMRel id («Combinator.eqCert» (encEqn q) c) (eqCert q c) := by
  intro sc st' st h
  have hi := stInfer_srel h
  pm_simp [eqCert]
  cases hb : st.infer
  · have := addLemma_rel q c sc st' st h
    mirror_simp [«Combinator.eqCert», hi, hb] at this ⊢
    exact this
  · mirror_simp [«Combinator.eqCert», hi, hb]
    exact ⟨st', h, rfl⟩

/-- The mirror's quotient of numbers. -/
@[simp] theorem div_leaf (a b : ℕ) : Const.div (leaf a) (leaf b) = leaf (a / b) := rfl

/-- The mirror's remainder of numbers. -/
@[simp] theorem mod_leaf (a b : ℕ) : Const.mod (leaf a) (leaf b) = leaf (a % b) := rfl

@[simp] theorem tyT_eq (y : Ty) : «Combinator.tyT» (encTy y) = y.term := by
  simp [«Combinator.tyT», encTy]

@[simp] theorem tySort_eq (y : Ty) : «Combinator.tySort» (encTy y) = leaf y.sort := by
  simp [«Combinator.tySort», encTy]

@[simp] theorem tyDfd_eq (y : Ty) : «Combinator.tyDfd» (encTy y) = y.dfd := by
  simp [«Combinator.tyDfd», encTy]

@[simp] theorem tyLo_eq (y : Ty) : «Combinator.tyLo» (encTy y) = y.lo := by
  simp [«Combinator.tyLo», encTy]

@[simp] theorem tyLoC_eq (y : Ty) : «Combinator.tyLoC» (encTy y) = y.loCert := by
  simp [«Combinator.tyLoC», encTy]

@[simp] theorem tyHi_eq (y : Ty) : «Combinator.tyHi» (encTy y) = y.hi := by
  simp [«Combinator.tyHi», encTy]

@[simp] theorem tyHiC_eq (y : Ty) : «Combinator.tyHiC» (encTy y) = y.hiCert := by
  simp [«Combinator.tyHiC», encTy]

@[simp] theorem pty_eq (t : Tree) (s : ℕ) (d lo lc hi hc : Tree) :
    «Combinator.pty» t (leaf s) d lo lc hi hc = encTy ⟨t, s, d, lo, lc, hi, hc⟩ := rfl

/-- The simplification of the mirror's prover: the mirror's primitives, the certificates, the
scopes and the typings, with the given lemmas. -/
local macro "comb_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  mirror_simp [cHyp_eq, cRefl_eq, cSymm_eq, cTrans_eq, cCong_eq, cStrict_eq, cAx_eq, cThm_eq,
    scCtx_eq, scHyps_eq, scSeq_eq, scCite_eq, div_leaf, mod_leaf, tyT_eq, tySort_eq, tyDfd_eq,
    tyLo_eq, tyLoC_eq, tyHi_eq, tyHiC_eq, pty_eq, «Theory.l2», «Theory.l3»,
    «Theory.l4», $ls,*] $(loc)?)

/-- The mirror's certificate of an equation between two objects, from their typings. -/
theorem objEq_rel (l r : Ty) :
    PMRel id («Combinator.objEq» (encTy l) (encTy r)) (objEq l r) := by
  intro sc st' st h
  have hi := stInfer_srel h
  pm_simp [objEq, guard, ReaderT.run_failure, StateT.run_failure]
  have key : (l.sort == Sorts.obj && r.sort == Sorts.obj && l.lo == r.lo) =
      decide (l.sort = 0 ∧ r.sort = 0 ∧ l.lo = r.lo) := by
    simp only [Bool.beq_eq_decide_eq, Bool.and_assoc, Bool.decide_and]
  have key' : (l.sort == 0 && (r.sort == 0 && decide (l.lo = r.lo))) =
      decide (l.sort = 0 ∧ r.sort = 0 ∧ l.lo = r.lo) := by
    simp only [Bool.beq_eq_decide_eq, Bool.decide_and]
  by_cases hc : l.sort = 0 ∧ r.sort = 0 ∧ l.lo = r.lo
  · simp only [key, decide_eq_true hc, ↓reduceIte]
    cases hb : st.infer
    · pm_simp [hb, Bool.false_eq_true, ↓reduceIte]
      comb_simp [«Combinator.objEq», hi, hb, key', decide_eq_true hc]
      exact ⟨st', h, rfl⟩
    · pm_simp [hb, ↓reduceIte]
      comb_simp [«Combinator.objEq», hi, hb, key', decide_eq_true hc]
      exact ⟨st', h, rfl⟩
  · simp only [key, decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    pm_simp []
    comb_simp [«Combinator.objEq», key', decide_eq_false hc]
    rfl

/-- The definitions in force of an encoded state. -/
theorem stDefs_srel {st' : Tree} {st : St} (h : SRel st' st) :
    «Combinator.stDefs» st' = st.defs.map encDefn := by
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  mirror_simp [«Combinator.stDefs»]

set_option maxRecDepth 100000 in
/-- The mirror's axiom of an index of the theory extended by the definitions in force. -/
theorem axiomAt_rel (j : ℕ) : PMRel encSeq («Combinator.axiomAt» (leaf j)) (axiomAt j) := by
  intro sc st' st h
  have hd := stDefs_srel h
  unfold axiomAt «Combinator.axiomAt»
  rw [axioms_eq, sig_eq]
  generalize axioms = A
  generalize sig = S
  by_cases hj : j < A.length
  · rw [dite_eq_left_of_eq_true (eq_true hj)]
    pm_simp []
    comb_simp [hj, «Combinator.pmPure»]
    refine ⟨st', h, ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false hj)]
    comb_simp [hj, «Combinator.pmBind», «Combinator.pmGet», hd]
    simp only [decide_false, Bool.false_eq_true, ↓reduceIte, some_eq, bindO_eq, Option.elim_some,
      RoseTree.children_node, List.getD_cons_zero, List.getD_cons_succ, hd, List.getElem?_map]
    pm_simp []
    rcases hdm : st.defs[(j - A.length) / 2]? with _ | d
    · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      pm_simp []
      rfl
    · simp only [Option.map_some, Option.isSome_some, ↓reduceIte, Option.getD_some,
        pdAxioms_eq, List.getElem?_map]
      rcases ham : (Defn.axioms (List.length S + (j - A.length) / 2) d)[(j - A.length) % 2]? with
        _ | a
      · simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        pm_simp []
        rfl
      · simp only [Option.map_some, Option.isSome_some, ↓reduceIte, Option.getD_some]
        pm_simp []
        exact ⟨st', h, rfl⟩

/-- The mirror's computation from the state read. -/
theorem pmGetBind_rel {α : Type} (e : α → Tree) (k' : Tree → Tree → Tree → Tree)
    (k : St → PM α) (hk : ∀ st' st, SRel st' st → PMRel e (k' st') (k st)) :
    PMRel e («Combinator.pmBind» «Combinator.pmGet» k') (get >>= k) := by
  intro sc st' st h
  have := hk st' st h sc st' st h
  pm_simp []
  simp only [«Combinator.pmBind», «Combinator.pmGet», some_eq, bindO_eq,
    Option.elim_some, «Theory.l2», at_eq]
  exact this

/-! The typing of patterns and terms. -/

/-- A pattern typer written in Geb and a pattern typer are related when they agree at every list
of typings and side. -/
def PatRel (pt' : List Tree → Tree → Tree → Tree → Tree) (pt : List Ty → Tree → PM Ty) : Prop :=
  ∀ tys p, PMRel encTy (pt' (tys.map encTy) p) (pt tys p)

/-- The mirror's certificate of an axiom's hypothesis at typed arguments. -/
theorem proveHyp_rel (pt' : List Tree → Tree → Tree → Tree → Tree) (pt : List Ty → Tree → PM Ty)
    (hpt : PatRel pt' pt) (tys : List Ty) (q : Eqn) :
    PMRel id («Combinator.proveHyp» pt' (tys.map encTy) (encEqn q))
      (proveHyp pt tys q) := by
  unfold «Combinator.proveHyp» proveHyp
  simp only [eqLhs_eq, eqRhs_eq]
  refine pmBind_rel encTy id _ _ (hpt tys q.lhs) _ _ fun l ↦ ?_
  by_cases hq : q.lhs = q.rhs
  · simp only [hq, beq_self_eq_true, ↓reduceIte, equal_eq, decide_true]
    comb_simp []
    exact pmPure_rel id l.dfd
  · simp only [beq_false_of_ne hq, Bool.false_eq_true, ↓reduceIte]
    comb_simp [hq]
    exact pmBind_rel encTy id _ _ (hpt tys q.rhs) _ _ fun r ↦ objEq_rel l r

set_option maxRecDepth 100000 in
/-- The mirror's canonical bound of an application by an axiom, with its certificate. -/
theorem pBound_rel (pt' : List Tree → Tree → Tree → Tree → Tree) (pt : List Ty → Tree → PM Ty)
    (hpt : PatRel pt' pt) (tys : List Ty) (k j : ℕ) (d : Tree) :
    PMRel encPair («Combinator.pBound» pt' (tys.map encTy) (leaf k) (leaf j) d)
      (Prover.bound pt tys k j d) := by
  unfold «Combinator.pBound» Prover.bound
  refine pmBind_rel encSeq encPair _ _ (axiomAt_rel j) _ _ fun a ↦ ?_
  simp only [seqHyps_eq, seqConcl_eq, eqRhs_eq, length_eq, List.length_map, opVars_eq, dfd_eq]
  refine pmBind_rel (fun hs ↦ RoseTree.node 0 (hs.map id)) encPair _ _
    (pmMapM_rel id encEqn _ _ a.hyps fun q _ ↦ ?_) _ _ fun hs ↦ ?_
  · by_cases hq : q = dfd (PartialHorn.opVars k tys.length)
    · simp only [hq, equal_eq, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte, beq_self_eq_true]
      exact pmPure_rel id d
    · have hne : (q == dfd (PartialHorn.opVars k tys.length)) = false := beq_false_of_ne hq
      simp only [hne, equal_eq, encEqn_inj, hq, decide_false, ofBool_false, label_leaf, ne_eq,
        not_true_eq_false, ↓reduceIte, Bool.false_eq_true]
      exact proveHyp_rel pt' pt hpt tys q
  · simp only [children_node, List.map_id, mapT_eq, List.map_map, Function.comp_def, tyT_eq,
      tyDfd_eq, cAx_eq]
    refine pmBind_rel encTy encPair _ _ (hpt tys a.concl.rhs) _ _ fun r ↦ ?_
    comb_simp [List.map_id]
    exact pmPure_rel encPair
      (r.lo, PartialHorn.Cert.trans (PartialHorn.Cert.ax j (tys.map Ty.term) (tys.map Ty.dfd) hs)
        r.loCert)

/-- The mirror's typing of an application of a definition in force. -/
theorem typeDefined_rel (pt' : List Tree → Tree → Tree → Tree → Tree)
    (pt : List Ty → Tree → PM Ty) (hpt : PatRel pt' pt) (i s : ℕ) (tys : List Ty) :
    PMRel encTy («Combinator.typeDefined» pt' (leaf i) (leaf s) (tys.map encTy))
      (typeDefined pt i s tys) := by
  unfold «Combinator.typeDefined» typeDefined
  refine pmGetBind_rel _ _ _ fun st' st h ↦ ?_
  have hd := stDefs_srel h
  simp only [hd, nth_eq, List.getElem?_map]
  rcases hdi : st.defs[i]? with _ | dfn
  · comb_simp []
    exact pmFail_rel encTy
  · comb_simp [pdBody_eq, sig_eq]
    refine pmBind_rel encTy encTy _ _ (hpt tys dfn.body) _ _ fun b ↦ ?_
    refine pmGetBind_rel _ _ _ fun st₁' st₁ h₁ ↦ ?_
    have hi := stInfer_srel h₁
    comb_simp [hi, phOp_eq, eqn_eq, defAxIdx_eq, dfd_eq, mirror_dom, mirror_cod]
    cases hinf : st₁.infer
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine pmBind_rel id encTy _ _ (addLemma_rel _ _) _ _ fun e ↦ ?_
      refine pmBind_rel id encTy _ _ (addLemma_rel _ _) _ _ fun d ↦ ?_
      by_cases hs : s = 0
      · simp only [hs, beq_self_eq_true, ↓reduceIte]
        refine pmBind_rel id encTy _ _ (addLemma_rel _ _) _ _ fun c ↦ ?_
        simp only [pure_bind]
        exact memoRet_rel _
      · simp only [beq_false_of_ne hs, Bool.false_eq_true, ↓reduceIte]
        refine pmBind_rel id encTy _ _ (addLemma_rel _ _) _ _ fun dc ↦ ?_
        refine pmBind_rel id encTy _ _ (addLemma_rel _ _) _ _ fun cc ↦ ?_
        simp only [pure_bind]
        exact memoRet_rel _
    · simp only [↓reduceIte]
      by_cases hs : s = 0
      · simp only [hs, beq_self_eq_true, ↓reduceIte]
        exact memoRet_rel _
      · simp only [beq_false_of_ne hs, Bool.false_eq_true, ↓reduceIte]
        exact memoRet_rel _

/-- The extended signature of an encoded state. -/
theorem stSig_srel {st' : Tree} {st : St} (h : SRel st' st) :
    «Combinator.stSig» st' = st.sig.map encOpSig := by
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  mirror_simp [«Combinator.stSig»]

/-- The mirror's failure, at a failure composed with a computation. -/
theorem pmFailBind_rel {α β : Type} (e : β → Tree) (k : α → PM β) :
    PMRel e «Combinator.pmFail» (failure >>= k) := by
  intro sc st' st h
  pm_simp []
  rfl

set_option maxRecDepth 100000 in
/-- The mirror's certificate of an application's definedness. -/
theorem typeOpDfd_rel (pt' : List Tree → Tree → Tree → Tree → Tree)
    (pt : List Ty → Tree → PM Ty) (hpt : PatRel pt' pt) (k : ℕ) (tys : List Ty) :
    PMRel id («Combinator.typeOpDfd» pt' (leaf k) (tys.map encTy))
      (typeOpDfd pt k tys) := by
  unfold «Combinator.typeOpDfd» typeOpDfd
  simp only [dfdRules_eq, nth_eq, List.getElem?_map]
  generalize dfdRules[k]? = r
  rcases r with _ | _ | (j | j | j)
  · comb_simp []
    exact pmFail_rel id
  · comb_simp []
    exact pmFail_rel id
  · comb_simp [encDfdRule]
    refine pmBind_rel encSeq id _ _ (axiomAt_rel j) _ _ fun a ↦ ?_
    simp only [seqHyps_eq]
    refine pmBind_rel (fun hs ↦ RoseTree.node 0 (hs.map id)) id _ _
      (pmMapM_rel id encEqn _ _ a.hyps fun q _ ↦ proveHyp_rel pt' pt hpt tys q) _ _ fun hs ↦ ?_
    comb_simp [List.map_id, mapT_eq, List.map_map, Function.comp_def]
    exact pmPure_rel id _
  · comb_simp [encDfdRule, mapT_eq, List.map_map, Function.comp_def]
    exact pmPure_rel id _
  · comb_simp [encDfdRule]
    exact pmPure_rel id _

/-- The mirror's typing of an object applied to typed terms. -/
theorem typeOpObj_rel (k : ℕ) (t d : Tree) (tys : List Ty) :
    PMRel encTy («Combinator.typeOpObj» (leaf k) t d (tys.map encTy))
      (typeOpObj k t d tys) := by
  unfold «Combinator.typeOpObj» typeOpObj
  comb_simp [mapT_eq, List.map_map, Function.comp_def, phOp_eq, eqn_eq, ofBool_bne, Sorts.obj]
  simp only [Bool.beq_eq_decide_eq]
  split_ifs
  · exact pmPure_rel encTy _
  · exact pmBind_rel id encTy _ _ (eqCert_rel _ _) _ _ fun e ↦ pmPure_rel encTy _

set_option maxRecDepth 100000 in
/-- The mirror's typing of an application of an operation, from its sort and its certificate of
definedness. -/
theorem typeOpTy_rel (pt' : List Tree → Tree → Tree → Tree → Tree)
    (pt : List Ty → Tree → PM Ty) (hpt : PatRel pt' pt) (k s : ℕ) (t d : Tree) (tys : List Ty) :
    PMRel encTy («Combinator.typeOpTy» pt' (leaf k) (leaf s) t d (tys.map encTy))
      (typeOpTy pt k s t d tys) := by
  unfold «Combinator.typeOpTy» typeOpTy
  by_cases hs : s = 0
  · subst hs
    simp only [eq_leaf, beq_self_eq_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, ↓reduceIte, Sorts.obj]
    rcases k with _ | _ | k <;> rcases tys with _ | ⟨f, _ | ⟨g, gs⟩⟩ <;>
      comb_simp [List.length_cons, List.length_nil, beq_iff_eq, Nat.add_one_ne_zero,
        Nat.add_right_cancel_iff, List.getD_cons_zero]
    · exact typeOpObj_rel 0 t d []
    · exact pmPure_rel encTy _
    · rw [ite_eq_right (by omega)]
      exact typeOpObj_rel 0 t d _
    · exact typeOpObj_rel 1 t d []
    · exact pmPure_rel encTy _
    · rw [ite_eq_right (by omega)]
      exact typeOpObj_rel 1 t d _
    · exact typeOpObj_rel _ t d []
    · rw [ite_eq_right (by omega)]
      exact typeOpObj_rel _ t d _
    · simp only [Bool.and_eq_true, beq_iff_eq]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact typeOpObj_rel _ t d _
  · have hs' : (s == 0) = false := beq_false_of_ne hs
    simp only [Sorts.obj, domRules_eq, codRules_eq, nth_eq, List.getElem?_map]
    generalize domRules[k]? = od
    generalize codRules[k]? = oc
    rcases od with _ | _ | jd <;> rcases oc with _ | _ | jc <;> comb_simp [hs']
    all_goals try exact pmFail_rel encTy
    refine pmBind_rel encPair encTy _ _ (pBound_rel pt' pt hpt tys k jd d) _ _ fun dp ↦ ?_
    refine pmBind_rel encPair encTy _ _ (pBound_rel pt' pt hpt tys k jc d) _ _ fun cp ↦ ?_
    comb_simp [encPair, mirror_dom, mirror_cod, eqn_eq]
    refine pmBind_rel id encTy _ _ (eqCert_rel _ _) _ _ fun de ↦ ?_
    refine pmBind_rel id encTy _ _ (eqCert_rel _ _) _ _ fun ce ↦ ?_
    exact pmPure_rel encTy _

set_option maxRecDepth 100000 in
/-- The mirror's typing of an application of an operation. -/
theorem typeOp_rel (pt' : List Tree → Tree → Tree → Tree → Tree)
    (pt : List Ty → Tree → PM Ty) (hpt : PatRel pt' pt) (k : ℕ) (tys : List Ty) :
    PMRel encTy («Combinator.typeOp» pt' (leaf k) (tys.map encTy)) (typeOp pt k tys) := by
  unfold «Combinator.typeOp» typeOp
  refine pmGetBind_rel _ _ _ fun st' st h ↦ ?_
  simp only [stSig_srel h, nth_eq, List.getElem?_map]
  cases st.sig[k]? with
  | none =>
    comb_simp []
    exact pmFail_rel encTy
  | some o =>
    obtain ⟨as, s⟩ := o
    comb_simp [opArgs_eq, opSort_eq, mapT_eq, List.map_map, Function.comp_def, sig_eq, phOp_eq]
    by_cases hg : tys.map Ty.sort = as
    · simp only [hg, decide_true, ↓reduceIte, beq_self_eq_true, guard, pure_bind]
      by_cases hk : sig.length ≤ k
      · simp only [show ¬k < sig.length by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
          hk]
        exact typeDefined_rel pt' pt hpt _ s tys
      · simp only [show k < sig.length by omega, decide_true, ↓reduceIte, hk]
        refine pmBind_rel id encTy _ _ (typeOpDfd_rel pt' pt hpt k tys) _ _ fun dc ↦ ?_
        refine pmBind_rel id encTy _ _ (dfdCert_rel _ dc) _ _ fun d ↦ ?_
        refine pmBind_rel encTy encTy _ _ (typeOpTy_rel pt' pt hpt k s _ d tys) _ _ fun ty ↦ ?_
        exact memoRet_rel ty
    · simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte, guard, beq_iff_eq]
      exact pmFailBind_rel encTy _

/-- The mirror's values of a list's computations, in turn. -/
theorem pmSeq_rel {α : Type} (e : α → Tree) :
    ∀ xs : List (Tree × (Tree → Tree → Tree) × PM α), (∀ x ∈ xs, PMRel e x.2.1 x.2.2) →
      PMRel (fun ys ↦ RoseTree.node 0 (ys.map e))
        («Combinator.pmSeq» (xs.map fun x ↦ x.2.1))
        ((xs.map fun x ↦ (x.1, x.2.2)).mapM Prod.snd) := by
  refine List.rec (fun _ ↦ ?_) fun x xs ih hx ↦ ?_
  · simp only [«Combinator.pmSeq», List.map_nil, foldr_eq, List.foldr_nil, List.mapM_nil]
    exact pmPure_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) []
  · have ih' := ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
    simp only [«Combinator.pmSeq», foldr_eq] at ih' ⊢
    simp only [List.map_cons, List.foldr_cons, List.mapM_cons]
    refine pmBind_rel e _ _ _ (hx x List.mem_cons_self) _ _ fun y ↦ ?_
    refine pmBind_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) _ _ _ ih' _ _ fun ys ↦ ?_
    simp only [children_node]
    exact pmPure_rel (fun ys ↦ RoseTree.node 0 (ys.map e)) (y :: ys)

/-- The mirror's step of typing, at a related pattern typer, related typings of variables and a
term computed from the node as the mirror computes it. -/
theorem typeStep_rel (pt' : List Tree → Tree → Tree → Tree → Tree) (pt : List Ty → Tree → PM Ty)
    (hpt : PatRel pt' pt) (lf' : Tree → Tree → Tree → Tree) (lf : ℕ → PM Ty)
    (hlf : ∀ n, PMRel encTy (lf' (leaf n)) (lf n)) (term' term : Tree → Tree)
    (hterm : ∀ t, term' t = term t) (l : ℕ)
    (xs : List (Tree × (Tree → Tree → Tree) × PM Ty)) (hx : ∀ x ∈ xs, PMRel encTy x.2.1 x.2.2) :
    PMRel encTy («Combinator.typeStep» pt' lf' term' (RoseTree.node l (xs.map Prod.fst))
        (xs.map fun x ↦ x.2.1))
      (typeStep pt lf term l (xs.map fun x ↦ (x.1, x.2.2))) := by
  rcases l with _ | k
  · rcases xs with _ | ⟨⟨i, v, w⟩, _ | ⟨y, ys⟩⟩
    · comb_simp [«Combinator.typeStep», typeStep]
      exact pmFail_rel encTy
    · comb_simp [«Combinator.typeStep», typeStep]
      exact hlf i.label
    · comb_simp [«Combinator.typeStep», typeStep]
      exact pmFail_rel encTy
  · comb_simp [«Combinator.typeStep», typeStep, hterm]
    simp only [show (k + 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Nat.add_sub_cancel]
    refine pmBind_rel (fun o : Option Ty ↦ encOpt (o.map encTy)) encTy _ _ (lookup_rel _) _ _
      fun o ↦ ?_
    rcases o with _ | y
    · comb_simp []
      refine pmBind_rel (fun ys ↦ RoseTree.node 0 (ys.map encTy)) encTy _ _
        (pmSeq_rel encTy xs hx) _ _ fun ys ↦ ?_
      rw [RoseTree.children_node]
      exact typeOp_rel pt' pt hpt k ys
    · comb_simp []
      exact pmPure_rel encTy y

/-- The mirror's index of the first element of a list passing a test. -/
theorem findIdxT_eq {α : Type} (f' : Tree → Tree) (g : α → Tree) (p : α → Bool)
    (hf : ∀ x, f' (g x) = ofBool (p x)) :
    ∀ xs : List α,
      «Combinator.findIdxT» f' (xs.map g) = encOpt ((xs.findIdx? p).map leaf) := by
  have gen : ∀ (ys : List α) (m : ℕ), Const.foldr (fun (x : Tree) (s : Tree × Tree) ↦
      (Const.sub s.1 (leaf 1), if (f' x).label ≠ 0 then
        «Prelude.some» (Const.sub s.1 (leaf 1)) else s.2))
      (leaf (m + ys.length), «Prelude.none») (ys.map g) =
      (leaf m, encOpt ((ys.findIdx? p).map fun k ↦ leaf (k + m))) := by
    refine List.rec (fun m ↦ ?_) fun y ys ih m ↦ ?_
    · rfl
    · have := ih (m + 1)
      simp only [foldr_eq] at this ⊢
      rw [List.map_cons, List.foldr_cons, List.length_cons,
        show m + (ys.length + 1) = m + 1 + ys.length by omega, this, List.findIdx?_cons, hf,
        sub_leaf, Nat.add_sub_cancel]
      cases p y
      · simp only [ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte,
          Bool.false_eq_true, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1 m]
      · simp only [ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte,
          Option.map_some, Nat.zero_add]
        rfl
  intro xs
  simp only [«Combinator.findIdxT», length_eq, List.length_map]
  have := gen xs 0
  simp only [Nat.zero_add, Nat.add_zero] at this
  rw [this]

/-- The run of a computation from the state read. -/
theorem run_get_bind {α : Type} (k : St → PM α) (sc : Scope) (st : St) :
    ((get >>= k).run sc).run st = ((k st).run sc).run st := rfl

/-- The mirror's canonical bound of a variable's domain or codomain. -/
theorem varSide_rel (tt' : Tree → Tree → Tree → Tree) (tt : Tree → PM Ty)
    (htt : ∀ t, PMRel encTy (tt' t) (tt t)) (inf : Bool) (i o j : ℕ) :
    PMRel encPair («Combinator.varSide» tt' (leaf i) (ofBool inf) (leaf o) (leaf j))
      (varSide tt inf i o j) := by
  intro sc st' st h
  unfold «Combinator.varSide» varSide
  simp only [read, readThe, MonadReaderOf.read, ReaderT.run_bind, ReaderT.run_read, pure_bind]
  comb_simp [scHyps_eq, phOp_eq, phVar_eq, single_eq]
  rw [findIdxT_eq _ encEqn (fun q : Eqn ↦ q.lhs == PartialHorn.op o [PartialHorn.var i])
    (fun q ↦ by simp [eqLhs_eq, Bool.beq_eq_decide_eq])]
  cases List.findIdx? (fun q : Eqn ↦ q.lhs == PartialHorn.op o [PartialHorn.var i]) sc.hyps with
  | none =>
    simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_bne, Bool.false_eq_true,
      ↓reduceIte]
    pm_simp []
    exact ⟨st', h, rfl⟩
  | some hi =>
    simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_bne, ↓reduceIte, get_eq,
      nth_eq, List.getElem?_map]
    cases sc.hyps[hi]? with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      pm_simp []
      rfl
    | some q =>
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, get_eq, eqRhs_eq]
      refine (pmBind_rel encTy encPair _ _ (htt q.rhs) _ _ fun r ↦ ?_) sc st' st h
      cases inf
      · comb_simp []
        exact pmPure_rel encPair (r.lo, PartialHorn.Cert.trans (PartialHorn.Cert.hyp hi) r.loCert)
      · comb_simp []
        exact pmPure_rel encPair
          (r.lo, RoseTree.node PartialHorn.Rule.objEq [PartialHorn.op o [PartialHorn.var i], r.lo])

/-- The mirror's typing of a variable of the scope, at a related typer of terms. -/
theorem typeVar_rel (tt' : Tree → Tree → Tree → Tree) (tt : Tree → PM Ty)
    (htt : ∀ t, PMRel encTy (tt' t) (tt t)) (i : ℕ) :
    PMRel encTy («Combinator.typeVar» tt' (leaf i)) (typeVar tt i) := by
  intro sc st' st h
  unfold «Combinator.typeVar» typeVar
  simp only [read, readThe, MonadReaderOf.read, ReaderT.run_bind, ReaderT.run_read, pure_bind,
    scCtx_eq, nth_eq, List.getElem?_map]
  cases sc.ctx[i]? with
  | none =>
    simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_false, label_leaf, ne_eq,
      not_true_eq_false, ↓reduceIte]
    pm_simp []
    rfl
  | some s =>
    simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, get_eq, eq_leaf]
    rcases s with _ | _ | s
    · simp only [beq_self_eq_true, ofBool_true, label_leaf, one_ne_zero, not_false_eq_true,
        ↓reduceIte]
      pm_simp []
      exact ⟨st', h, rfl⟩
    · simp only [Nat.zero_add, Nat.reduceBEq, beq_self_eq_true, ofBool_true, ofBool_false,
        label_leaf, one_ne_zero, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      rw [run_get_bind, stInfer_srel h]
      refine (pmBind_rel encPair encTy _ _ (varSide_rel tt' tt htt st.infer i 0 0) _ _
        fun p ↦ ?_) sc st' st h
      refine pmBind_rel encPair encTy _ _ (varSide_rel tt' tt htt st.infer i 1 1) _ _
        fun p' ↦ ?_
      comb_simp [encPair]
      exact pmPure_rel encTy _
    · have h0 : (s + 1 + 1 == 0) = false := rfl
      have h1 : (s + 1 + 1 == 1) = false := rfl
      simp only [h0, h1, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte]
      pm_simp []
      rfl

/-- Typers written in Geb and typers are related when their pattern typers and their typers of
terms are. -/
def TypersRel (p' : (List Tree → Tree → Tree → Tree → Tree) × (Tree → Tree → Tree → Tree))
    (p : (List Ty → Tree → PM Ty) × (Tree → PM Ty)) : Prop :=
  PatRel p'.1 p.1 ∧ ∀ t, PMRel encTy (p'.2 t) (p.2 t)

/-- The mirror's typers at every fuel. -/
theorem typers_rel (n : ℕ) : TypersRel («Combinator.typers» (leaf n)) (typers n) := by
  unfold «Combinator.typers» typers
  simp only [Const.iter, label_leaf]
  refine Nat.rec ⟨fun _ _ ↦ pmFail_rel encTy, fun _ ↦ pmFail_rel encTy⟩ (fun _ ih ↦ ?_) n
  refine ⟨fun tys p ↦ ?_, fun t ↦ ?_⟩
  · refine para_rel (PMRel encTy) _ _ (fun l xs hx ↦ ?_) p
    refine typeStep_rel _ _ ih.1 _ _ (fun k ↦ ?_) _ _ (fun t ↦ ?_) l xs hx
    · simp only [nth_eq, List.getElem?_map]
      rcases tys[k]? with _ | y
      · comb_simp []
        exact pmFail_rel encTy
      · comb_simp [get_eq]
        exact pmPure_rel encTy y
    · simp only [mapT_eq, List.map_map, Function.comp_def, tyT_eq, phSubst_eq]
  · exact para_rel (PMRel encTy) _ _ (fun l xs hx ↦
      typeStep_rel _ _ ih.1 _ _ (typeVar_rel _ _ ih.2) _ _ (fun _ ↦ rfl) l xs hx) t

/-- The mirror's typing of a term of the scope. -/
theorem typeTerm_rel (t : Tree) : PMRel encTy («Combinator.typeTerm» t) (typeTerm t) :=
  (typers_rel typingFuel).2 t

/-- The mirror's typing of an axiom's side instantiated at typed arguments. -/
theorem typePattern_rel : PatRel (fun env p ↦ «Combinator.typePattern» env p) typePattern :=
  (typers_rel typingFuel).1

/-- The mirror's typings of terms, in turn. -/
theorem typeTerms_rel (σ : List Tree) :
    PMRel (fun ys ↦ RoseTree.node 0 (ys.map encTy))
      («Combinator.pmMapM» «Combinator.typeTerm» σ) (σ.mapM typeTerm) := by
  have h := pmMapM_rel encTy id «Combinator.typeTerm» typeTerm σ fun x _ ↦ typeTerm_rel x
  rwa [List.map_id] at h

/-! Rules and the match of a rule's side. -/

/-- A match's state as the node of the node of its assignment's optional terms and the node of
its deferred pairs of objects. -/
def encMS (ms : MatchSt) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (ms.σ.map encOpt), RoseTree.node 0 (ms.objs.map encPair)]

@[simp] theorem rwSrc_eq (r : RwRule) : «Combinator.rwSrc» (encRw r) = encSrc r.src := by
  simp [«Combinator.rwSrc», encRw]

@[simp] theorem rwFlip_eq (r : RwRule) : «Combinator.rwFlip» (encRw r) = ofBool r.flip := by
  simp [«Combinator.rwFlip», encRw]

@[simp] theorem rwAvoid_eq (r : RwRule) :
    «Combinator.rwAvoid» (encRw r) = r.avoid.map leaf := by
  simp [«Combinator.rwAvoid», encRw]

@[simp] theorem msSigma_eq (ms : MatchSt) :
    «Combinator.msSigma» (encMS ms) = ms.σ.map encOpt := by
  simp [«Combinator.msSigma», encMS]

@[simp] theorem msObjs_eq (ms : MatchSt) :
    «Combinator.msObjs» (encMS ms) = ms.objs.map encPair := by
  simp [«Combinator.msObjs», encMS]

@[simp] theorem msDefer_eq (ms : MatchSt) (p t : Tree) :
    «Combinator.msDefer» (encMS ms) p t = encMS { ms with objs := (p, t) :: ms.objs } := by
  simp only [«Combinator.msDefer», «Combinator.matchSt», «Theory.l2»,
    msSigma_eq, msObjs_eq, node_leaf]
  rfl

/-- The development of an encoded state. -/
theorem stDev_srel {st' : Tree} {st : St} (h : SRel st' st) :
    «Combinator.stDev» st' = st.dev.toList.map encDevEntry := by
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  mirror_simp [«Combinator.stDev»]

set_option maxRecDepth 100000 in
/-- The mirror's sequent of a rule's source. -/
theorem srcSeq_rel (s : Src) : PMRel encSeq («Combinator.srcSeq» (encSrc s)) s.seq := by
  rcases s with j | j
  · have e :
        «Combinator.srcSeq» (encSrc (.ax j)) = «Combinator.axiomAt» (leaf j) := by
      simp only [«Combinator.srcSeq», encSrc, label_eq, RoseTree.label_node, eq_leaf,
        children_node, at_eq, List.getD_cons_zero, beq_self_eq_true, ofBool_true, label_leaf, ne_eq,
        one_ne_zero, not_false_eq_true, ↓reduceIte]
    rw [e]
    exact axiomAt_rel j
  · simp only [«Combinator.srcSeq», encSrc, label_eq, RoseTree.label_node, eq_leaf,
      children_node, at_eq, List.getD_cons_zero, Nat.reduceBEq, ofBool_false, label_leaf, ne_eq,
      not_true_eq_false, ↓reduceIte, Src.seq]
    refine pmGetBind_rel _ _ _ fun st' st h ↦ ?_
    simp only [stDev_srel h, nth_eq, List.getElem?_map, Array.getElem?_toList]
    rcases st.dev[j]? with _ | e
    · comb_simp []
      exact pmFail_rel encSeq
    · comb_simp [get_eq, encDevEntry]
      exact pmPure_rel encSeq e.1

@[simp] theorem srcCert_eq (s : Src) (ts ds hs : List Tree) :
    «Combinator.srcCert» (encSrc s) ts ds hs = s.cert ts ds hs := by
  rcases s with j | j <;> comb_simp [«Combinator.srcCert», encSrc, Src.cert]

/-- A match written in Geb and a match are related when they agree at every term and encoded
state. -/
def MFRel (f' : Tree → Tree → Tree) (f : Tree → MatchSt → Option MatchSt) : Prop :=
  ∀ t ms, f' t (encMS ms) = encOpt ((f t ms).map encMS)

/-- The mirror's match of the children's matches against a term's children, in turn. -/
theorem matchKids_eq :
    ∀ xs : List (Tree × (Tree → Tree → Tree) × (Tree → MatchSt → Option MatchSt)),
      (∀ x ∈ xs, MFRel x.2.1 x.2.2) → ∀ us ms,
      «Combinator.matchKids» (xs.map fun x ↦ x.2.1) us (encMS ms) =
        encOpt ((((xs.map fun (x : Tree × (Tree → Tree → Tree) ×
          (Tree → MatchSt → Option MatchSt)) ↦ (x.1, x.2.2)).zip us).foldlM
          (fun (ms : MatchSt) ((c, u) : (Tree × (Tree → MatchSt → Option MatchSt)) × Tree) ↦
            c.2 u ms) ms).map encMS) := by
  refine List.rec (fun _ us ms ↦ ?_) fun x xs ih hx us ms ↦ ?_
  · simp [«Combinator.matchKids», some_eq]
  · rcases us with _ | ⟨u, us⟩
    · simp [«Combinator.matchKids», Const.lcase, some_eq]
    · have ih' := ih fun y hy ↦ hx y (List.mem_cons_of_mem x hy)
      simp only [«Combinator.matchKids», foldr_eq, Const.lcase] at ih' ⊢
      simp only [List.map_cons, List.foldr_cons, List.zip_cons_cons, List.foldlM_cons,
        hx x List.mem_cons_self u ms, bindO_eq]
      rcases x.2.2 u ms with _ | ms₂
      · rfl
      · exact ih' us ms₂

/-- The mirror's match of a rule's side, in a context of sorts, against a term. -/
theorem matchPat_eq (S : Sig) (ctx : List ℕ) (p : Tree) :
    MFRel («Combinator.matchPat» (S.map encOpSig) (ctx.map leaf) p) (matchPat S ctx p) := by
  refine para_rel MFRel _ _ (fun l xs hx t ms ↦ ?_) p
  rcases l with _ | k
  · rcases xs with _ | ⟨⟨i, v, w⟩, _ | ⟨y, ys⟩⟩
    · comb_simp [«Combinator.matchStepP»]
      rfl
    · comb_simp [«Combinator.matchStepP», msSigma_eq, msObjs_eq, msDefer_eq,
        Prove.setAt_eq, List.getElem?_map, some_eq, encOpt_inj]
      rcases hσ : ms.σ[i.label]? with _ | _ | u
      · rfl
      · simp [encMS, «Combinator.matchSt», List.map_set]
      · by_cases hu : u = t
        · simp [hu]
        · rcases hc : ctx[i.label]? with _ | c
          · simp [hu]
            rfl
          · by_cases hc0 : c = 0
            · simp [hu, hc0, Sorts.obj]
            · simp [hu, hc0, Sorts.obj, leaf_inj]
              rfl
    · comb_simp [«Combinator.matchStepP»]
      rfl
  · comb_simp [«Combinator.matchStepP», msDefer_eq, sortOf_eq, some_eq, encOpt_inj,
      Nat.add_one_ne_zero, beq_iff_eq]
    have tail : (if (t.label == k + 1 && t.children.length == xs.length) = true then
        «Combinator.matchKids» (xs.map fun x ↦ x.2.1) t.children (encMS ms)
        else «Prelude.none») = encOpt (Option.map encMS
          (if (t.label == k + 1 && t.children.length == xs.length) = true then
            ((xs.map fun x ↦ (x.1, x.2.2)).zip t.children).foldlM (fun ms x ↦ x.1.2 x.2 ms) ms
          else none)) := by
      by_cases hl : (t.label == k + 1 && t.children.length == xs.length) = true
      · simp only [hl, ↓reduceIte]
        exact matchKids_eq xs hx _ ms
      · simp only [hl]
        rfl
    rcases hs : PartialHorn.sortOf S ctx (RoseTree.node (k + 1) (xs.map Prod.fst)) with _ | c
    · simpa using tail
    · by_cases hc0 : c = 0
      · simp [hc0, Sorts.obj]
      · simpa [hc0, Sorts.obj, leaf_inj] using tail

/-! The certificate of a term's equation with a rule's side. -/

/-- A bridge written in Geb and a bridge are related when they agree at every term. -/
def BRel (f' : Tree → Tree → Tree → Tree) (f : Tree → PM Tree) : Prop :=
  ∀ t, PMRel id (f' t) (f t)

/-- The mirror's certificates of the children's equations, in turn. -/
theorem bridgeKids_rel :
    ∀ xs : List (Tree × (Tree → Tree → Tree → Tree) × (Tree → PM Tree)),
      (∀ x ∈ xs, BRel x.2.1 x.2.2) → ∀ us,
      PMRel (RoseTree.node 0) («Combinator.bridgeKids» (xs.map fun x ↦ x.2.1) us)
        (((xs.map fun (x : Tree × (Tree → Tree → Tree → Tree) × (Tree → PM Tree)) ↦
          (x.1, x.2.2)).zip us).mapM
          fun ((c, u) : (Tree × (Tree → PM Tree)) × Tree) ↦ c.2 u) := by
  refine List.rec (fun _ us ↦ ?_) fun x xs ih hx us ↦ ?_
  · simp only [«Combinator.bridgeKids», List.map_nil, foldr_eq, List.foldr_nil,
      List.zip_nil_left, List.mapM_nil, node_leaf]
    exact pmPure_rel (RoseTree.node 0) []
  · rcases us with _ | ⟨u, us⟩
    · simp only [«Combinator.bridgeKids», List.map_cons, foldr_eq, List.foldr_cons,
        Const.lcase, List.zip_nil_right, List.mapM_nil, node_leaf]
      exact pmPure_rel (RoseTree.node 0) []
    · have ih' := ih (fun y hy ↦ hx y (List.mem_cons_of_mem x hy)) us
      simp only [«Combinator.bridgeKids», foldr_eq] at ih' ⊢
      simp only [List.map_cons, List.foldr_cons, Const.lcase, List.zip_cons_cons, List.mapM_cons,
        node_leaf]
      refine pmBind_rel id _ _ _ (hx x List.mem_cons_self u) _ _ fun y ↦ ?_
      refine pmBind_rel (RoseTree.node 0) _ _ _ ih' _ _ fun ys ↦ ?_
      simp only [children_node, id]
      exact pmPure_rel (RoseTree.node 0) (y :: ys)

/-- The mirror's certificate that a term equals the instance of a rule's side at typed
arguments. -/
theorem bridge_rel (tys : List Ty) (p : Tree) :
    BRel («Combinator.bridge» (tys.map encTy) p) (bridge tys p) := by
  refine para_rel BRel _ _ (fun l xs hx t ↦ ?_) p
  simp only [«Combinator.bridgeStep», List.map_map, Function.comp_def]
  refine pmBind_rel encTy id _ _ (typeTerm_rel t) _ _ fun ty ↦ ?_
  comb_simp [mapT_eq, List.map_map, Function.comp_def, phSubst_eq]
  by_cases h1 : PartialHorn.subst (tys.map Ty.term) (RoseTree.node l (xs.map Prod.fst)) = t
  · simp only [h1, decide_true, beq_self_eq_true, ↓reduceIte]
    exact pmPure_rel id ty.dfd
  · simp only [h1, decide_false, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : ty.sort = 0
    · simp only [h2, ↓reduceIte, Sorts.obj]
      exact pmBind_rel encTy id _ _ (typePattern_rel tys _) _ _ fun py ↦ objEq_rel ty py
    · simp only [h2, Sorts.obj, ↓reduceIte]
      rw [show (l == 0 || !(t.children.length == xs.length)) =
        (l == 0 || t.children.length != xs.length) from rfl]
      cases (l == 0 || t.children.length != xs.length)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine pmBind_rel (RoseTree.node 0) id _ _ (bridgeKids_rel xs hx t.children) _ _
          fun cs ↦ ?_
        rw [RoseTree.children_node]
        exact pmPure_rel id _
      · simp only [↓reduceIte]
        exact pmFail_rel id

/-! Rewriting at a term's root. -/

/-- The mirror's initial state of a match. -/
theorem initMS_eq (ctx : List ℕ) :
    «Combinator.matchSt» (RoseTree.node 0 (ctx.map fun _ ↦ «Prelude.none»))
      (RoseTree.node 0 []) = encMS ⟨ctx.map fun _ ↦ none, []⟩ := by
  simp [«Combinator.matchSt», encMS]
  rfl

/-- The mirror's rewriting step at a term's root by a rule. -/
theorem applyRule_rel (r : RwRule) (t : Tree) :
    PMRel encPair («Combinator.applyRule» (encRw r) t) (applyRule r t) := by
  unfold «Combinator.applyRule» applyRule
  refine pmBind_rel (fun _ ↦ leaf 0) encPair _ _ ?_ _ _ fun _ ↦ ?_
  · rw [rwAvoid_eq, anyT_eq _ (fun x ↦ t.label == x.label) _ (fun x hx ↦ ?_), not_eq]
    · have e : (r.avoid.map leaf).any (fun x ↦ t.label == x.label) = r.avoid.contains t.label := by
        simp only [List.any_map, Function.comp_def, label_leaf, List.contains_eq_any_beq]
      rw [e]
      exact pmGuard_rel _
    · obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
      rfl
  · simp only [rwSrc_eq, rwFlip_eq]
    refine pmBind_rel encSeq encPair _ _ (srcSeq_rel r.src) _ _ fun a ↦ ?_
    comb_simp [seqConcl_eq, eqLhs_eq, eqRhs_eq, seqCtx_eq, seqHyps_eq]
    rw [show (if r.flip = true then (a.concl.rhs, a.concl.lhs) else (a.concl.lhs, a.concl.rhs)) =
      (if r.flip = true then a.concl.rhs else a.concl.lhs,
        if r.flip = true then a.concl.lhs else a.concl.rhs) by cases r.flip <;> rfl]
    generalize (if r.flip = true then a.concl.rhs else a.concl.lhs) = p
    generalize (if r.flip = true then a.concl.lhs else a.concl.rhs) = q
    refine pmGetBind_rel _ _ _ fun st' st h ↦ ?_
    simp only [stSig_srel h, initMS_eq]
    rw [matchPat_eq st.sig a.ctx p t _]
    cases matchPat st.sig a.ctx p t ⟨a.ctx.map fun _ ↦ none, []⟩ with
    | none =>
      simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_bne, Bool.false_eq_true,
        ↓reduceIte]
      exact pmFail_rel encPair
    | some ms =>
      simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_bne, ↓reduceIte, get_eq,
        msSigma_eq, msObjs_eq]
      rw [show ms.σ.map encOpt = ms.σ.map (fun x ↦ encOpt (id x)) from rfl, allSomeT_eq]
      cases ms.σ.mapM id with
      | none =>
        simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_bne,
          Bool.false_eq_true, ↓reduceIte]
        exact pmFail_rel encPair
      | some σ =>
        simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_bne, ↓reduceIte,
          get_eq, RoseTree.children_node]
        refine pmBind_rel _ encPair _ _ (typeTerms_rel σ) _ _ fun tys ↦ ?_
        simp only [RoseTree.children_node]
        refine pmBind_rel (fun cs ↦ RoseTree.node 0 (cs.map id)) encPair _ _
          (pmMapM_rel id encPair _ _ ms.objs fun ou _ ↦ ?_) _ _ fun _ ↦ ?_
        · simp only [encPair, RoseTree.children_node, List.getD_cons_zero, List.getD_cons_succ]
          exact pmBind_rel encTy id _ _ (typePattern_rel tys ou.1) _ _ fun lo ↦
            pmBind_rel encTy id _ _ (typeTerm_rel ou.2) _ _ fun lu ↦ objEq_rel lo lu
        · refine pmBind_rel id encPair _ _ (bridge_rel tys p t) _ _ fun b ↦ ?_
          refine pmBind_rel (fun hs ↦ RoseTree.node 0 (hs.map id)) encPair _ _
            (pmMapM_rel id encEqn _ _ a.hyps fun q' _ ↦ proveHyp_rel _ _ typePattern_rel tys q')
            _ _ fun hs ↦ ?_
          comb_simp [List.map_id, mapT_eq, List.map_map, Function.comp_def, srcCert_eq,
            phSubst_eq]
          exact pmPure_rel encPair (PartialHorn.subst σ q, PartialHorn.Cert.trans b
            (if r.flip then PartialHorn.Cert.symm (r.src.cert σ (tys.map Ty.dfd) hs)
              else r.src.cert σ (tys.map Ty.dfd) hs))

/-- The mirror's first rule of a list that applies at a term's root. -/
theorem firstRule_rel (t : Tree) : ∀ rules : List RwRule,
    PMRel encPair («Combinator.firstRule» (rules.map encRw) t) (firstRule rules t) := by
  refine List.rec ?_ fun r rules ih ↦ ?_
  · exact pmFail_rel encPair
  · simp only [«Combinator.firstRule», firstRule, foldr_eq, List.map_cons,
      List.foldr_cons] at ih ⊢
    exact pmOr_rel encPair _ _ _ _ (applyRule_rel r t) ih

/-- A quadruple of trees as the node of its components. -/
def encQuad (q : Tree × Tree × Tree × Tree) : Tree := RoseTree.node 0 [q.1, q.2.1, q.2.2.1, q.2.2.2]

/-- The mirror's instance of associativity at a term {lit}`comp a (comp b x)`. -/
theorem assocLeft_rel (t : Tree) :
    PMRel encQuad («Combinator.assocLeft» t) (assocLeft t) := by
  unfold «Combinator.assocLeft» assocLeft
  by_cases hl : t.label = 4
  · rcases hc : t.children with _ | ⟨a, _ | ⟨bx, _ | ⟨z, zs⟩⟩⟩
    · comb_simp [hl, hc]
      exact pmFail_rel encQuad
    · comb_simp [hl, hc]
      exact pmFail_rel encQuad
    · by_cases hl' : bx.label = 4
      · rcases hc' : bx.children with _ | ⟨b, _ | ⟨x, _ | ⟨z, zs⟩⟩⟩
        · comb_simp [hl, hc, hl', hc']
          exact pmFail_rel encQuad
        · comb_simp [hl, hc, hl', hc']
          exact pmFail_rel encQuad
        · comb_simp [hl, hc, hl', hc']
          refine pmBind_rel encTy encQuad _ _ (typeTerm_rel _) _ _ fun d ↦ ?_
          refine pmBind_rel encTy encQuad _ _ (typeTerm_rel a) _ _ fun ya ↦ ?_
          refine pmBind_rel encTy encQuad _ _ (typeTerm_rel b) _ _ fun yb ↦ ?_
          refine pmBind_rel encTy encQuad _ _ (typeTerm_rel x) _ _ fun yx ↦ ?_
          comb_simp [encQuad]
          exact pmPure_rel encQuad (a, b, x, _)
        · have h3 : ¬zs.length + 1 + 1 + 1 = 2 := by omega
          comb_simp [hl, hc, hl', hc', beq_iff_eq, h3]
          exact pmFail_rel encQuad
      · comb_simp [hl, hc, hl', Bool.and_eq_true, beq_iff_eq, false_and]
        split
        · rename_i heq _
          exact absurd heq hl'
        · exact pmFail_rel encQuad
    · have h3 : ¬zs.length + 1 + 1 + 1 = 2 := by omega
      comb_simp [hl, hc, beq_iff_eq, h3]
      exact pmFail_rel encQuad
  · comb_simp [hl, Bool.and_eq_true, beq_iff_eq, false_and]
    split
    · rename_i heq _
      exact absurd heq hl
    · exact pmFail_rel encQuad

/-- The mirror's rewriting step at a term's root. -/
theorem rewriteRoot_rel (rules : List RwRule) (t : Tree) :
    PMRel encPair («Combinator.rewriteRoot» (rules.map encRw) t) (rewriteRoot rules t) := by
  unfold «Combinator.rewriteRoot» rewriteRoot
  refine pmOr_rel encPair _ _ _ _ (firstRule_rel t rules) ?_
  refine pmBind_rel encQuad encPair _ _ (assocLeft_rel t) _ _ fun ⟨a, b, x, c⟩ ↦ ?_
  comb_simp [encQuad, mirror_comp]
  refine pmBind_rel encPair encPair _ _ (firstRule_rel _ rules) _ _ fun ⟨u, cu⟩ ↦ ?_
  refine pmBind_rel encTy encPair _ _ (typeTerm_rel _) _ _ fun ab ↦ ?_
  refine pmBind_rel encTy encPair _ _ (typeTerm_rel _) _ _ fun yx ↦ ?_
  comb_simp [encPair, mirror_comp]
  exact pmPure_rel encPair
    (comp u x, PartialHorn.Cert.trans c (PartialHorn.Cert.cong ab.dfd [cu, yx.dfd]))

/-! Normalization. -/

/-- The mirror's normal form of a term, if recorded in the scope. -/
theorem lookupNf_rel (t : Tree) :
    PMRel (fun o ↦ encOpt (o.map encPair)) («Combinator.lookupNf» t) (lookupNf t) := by
  intro sc st' st h
  pm_simp [lookupNf]
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  refine ⟨_, ⟨lm, ln, hm, hn, rfl⟩, ?_⟩
  mirror_simp [«Combinator.lookupNf», «Combinator.stNfs», «Theory.l2»,
    tableFind_eq, ← hn.2 t, Option.map_map]
  rfl

/-- The mirror's record of a normal form with its certificate in the table of normal forms. -/
theorem nfsInsert_rel (t n c : Tree) :
    PMRel encPair (fun _ st ↦ «Prelude.some» (Const.node (leaf 0)
        («Theory.l2» (Const.node (leaf 0) («Theory.l2» n c))
          («Combinator.withNfs» st («Combinator.tableInsert»
            («Combinator.stNfs» st) t (Const.node (leaf 0) («Theory.l2» n c)))))))
      (do modify fun st ↦ { st with nfs := st.nfs.insert t (n, c) }; pure (n, c)) := by
  intro sc st' st h
  pm_simp []
  obtain ⟨lm, ln, hm, hn, rfl⟩ := h
  refine ⟨_, ⟨lm, (t, (n, c)) :: ln, hm, tRel_insert ln st.nfs hn t (n, c), rfl⟩, ?_⟩
  mirror_simp [«Combinator.stNfs», «Combinator.withNfs»,
    «Combinator.tableInsert», «Combinator.pst», «Theory.l2»]
  rfl

/-- The mirror's record of a term's normal form. -/
theorem memoizeNf_rel (t n c : Tree) :
    PMRel encPair («Combinator.memoizeNf» t n c) (memoizeNf t n c) := by
  unfold «Combinator.memoizeNf» memoizeNf
  by_cases hn : t = n
  · simp only [hn, equal_eq, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, ↓reduceIte, beq_self_eq_true]
    exact pmBind_rel id encPair _ _ (pmPure_rel id c) _ _ fun c₁ ↦ nfsInsert_rel n n c₁
  · simp only [equal_eq, hn, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
      ↓reduceIte, beq_false_of_ne hn, Bool.false_eq_true, eqn_eq]
    exact pmBind_rel id encPair _ _ (addLemma_rel ⟨t, n⟩ c) _ _ fun c₁ ↦ nfsInsert_rel t n c₁

/-- The mirror's optional value of a computation, none when it fails. -/
theorem pmOpt_rel {α : Type} (e : α → Tree) (m' : Tree → Tree → Tree) (m : PM α)
    (hm : PMRel e m' m) :
    PMRel (fun o ↦ encOpt (o.map e)) («Combinator.pmOr»
        («Combinator.pmBind» m' fun x ↦ «Combinator.pmPure»
          («Prelude.some» x)) («Combinator.pmPure» «Prelude.none»))
      ((some <$> m) <|> pure none) := by
  rw [map_eq_bind_pure_comp]
  exact pmOr_rel _ _ _ _ _ (pmBind_rel e _ _ _ hm _ _ fun a ↦ pmPure_rel _ (some a))
    (pmPure_rel _ none)

/-- A normalizer written in Geb and a normalizer are related when they agree at every term. -/
def NRel (f' : Tree → Tree → Tree → Tree) (f : Tree → PM (Tree × Tree)) : Prop :=
  ∀ t, PMRel encPair (f' t) (f t)

/-- The mirror's step of normalization, at a related normalizer of the rewritten terms. -/
theorem normStep_rel (rules : List RwRule) (rec' : Tree → Tree → Tree → Tree)
    (rec : Tree → PM (Tree × Tree)) (hrec : NRel rec' rec) (l : ℕ)
    (xs : List (Tree × (Tree → Tree → Tree) × PM (Tree × Tree)))
    (hx : ∀ x ∈ xs, PMRel encPair x.2.1 x.2.2) :
    PMRel encPair («Combinator.normStepP» (rules.map encRw) rec'
        (RoseTree.node l (xs.map Prod.fst)) (xs.map fun x ↦ x.2.1))
      (normStep rules rec l (xs.map fun x ↦ (x.1, x.2.2))) := by
  unfold «Combinator.normStepP» normStep
  simp only [List.map_map, Function.comp_def]
  refine pmBind_rel (fun o ↦ encOpt (o.map encPair)) encPair _ _
    (lookupNf_rel (RoseTree.node l (xs.map Prod.fst))) _ _ fun o ↦ ?_
  rcases o with _ | r
  · comb_simp []
    refine pmBind_rel encTy encPair _ _ (typeTerm_rel _) _ _ fun ty ↦ ?_
    by_cases hs : ty.sort = 0
    · comb_simp [hs, Sorts.obj]
      exact pmPure_rel encPair (ty.lo, ty.loCert)
    · by_cases hl : l = 0
      · comb_simp [hs, hl, Sorts.obj, beq_iff_eq]
        exact pmPure_rel encPair (RoseTree.node 0 (xs.map Prod.fst), ty.dfd)
      · comb_simp [hs, hl, Sorts.obj, beq_iff_eq]
        refine pmBind_rel (fun (ys : List (Tree × Tree)) ↦ RoseTree.node 0 (ys.map encPair))
          encPair _ _
          (pmSeq_rel encPair xs hx) _ _ fun rs ↦ ?_
        comb_simp [RoseTree.children_node, List.map_map, Function.comp_def, encPair]
        refine pmBind_rel (fun o ↦ encOpt (o.map encPair)) encPair _ _
          (pmOpt_rel encPair _ _ (rewriteRoot_rel rules (RoseTree.node l (rs.map Prod.fst)))) _ _
          fun o ↦ ?_
        have hc₁ : ∀ c, PMRel encPair («Combinator.memoizeNf»
            (RoseTree.node l (xs.map Prod.fst)) (RoseTree.node l (rs.map Prod.fst)) c)
            (memoizeNf (RoseTree.node l (xs.map Prod.fst)) (RoseTree.node l (rs.map Prod.fst)) c) :=
          fun c ↦ memoizeNf_rel _ _ c
        by_cases hc : RoseTree.node l (rs.map Prod.fst) = RoseTree.node l (xs.map Prod.fst)
        · rcases o with _ | ⟨t₂, c₂⟩
          · comb_simp [decide_eq_true_eq, hc]
            exact memoizeNf_rel _ _ _
          · comb_simp [get_eq, encPair, decide_eq_true_eq, hc]
            refine pmBind_rel encPair encPair _ _ (hrec t₂) _ _ fun q ↦ ?_
            comb_simp [encPair]
            exact memoizeNf_rel _ _ _
        · rcases o with _ | ⟨t₂, c₂⟩
          · comb_simp [decide_eq_true_eq, hc]
            exact hc₁ _
          · comb_simp [get_eq, encPair, decide_eq_true_eq, hc]
            refine pmBind_rel encPair encPair _ _ (hrec t₂) _ _ fun q ↦ ?_
            comb_simp [encPair]
            exact memoizeNf_rel _ _ _
  · comb_simp [get_eq]
    exact pmPure_rel encPair r

/-- The mirror's normalizers at every fuel. -/
theorem normalizers_rel (rules : List RwRule) (n : ℕ) :
    NRel («Combinator.normalizers» (rules.map encRw) (leaf n)) (normalizers rules n) := by
  unfold «Combinator.normalizers» normalizers
  simp only [Const.iter, label_leaf]
  refine Nat.rec (fun _ ↦ pmFail_rel encPair) (fun _ ih t ↦ ?_) n
  simp only [Nat.repeat]
  refine para_rel (PMRel encPair) _ _ (fun l xs hx ↦ ?_) t
  exact normStep_rel rules _ _ ih l xs hx

/-- The mirror's normal form of a term under rules. -/
theorem normalize_rel (rules : List RwRule) (t : Tree) :
    PMRel encPair («Combinator.pNormalize» (rules.map encRw) t) (normalize rules t) := by
  unfold «Combinator.pNormalize» normalize normFuel
  exact normalizers_rel rules 64 t

/-! The tactics. -/

@[simp] theorem srcAx_eq (j : ℕ) : «Combinator.srcAx» (leaf j) = encSrc (.ax j) := rfl

@[simp] theorem srcThm_eq (j : ℕ) : «Combinator.srcThm» (leaf j) = encSrc (.thm j) := rfl

/-- The mirror's index of the terminal object's first axiom. -/
theorem beforeTerminal_eq : «Combinator.beforeTerminal» = leaf (axIdx beforeTerminal 0) :=
  rfl

/-- The mirror's index of the products' first axiom. -/
theorem beforeProduct_eq : «Combinator.beforeProduct» = leaf (axIdx beforeProduct 0) :=
  rfl

/-- The mirror's index of the exponentials' first axiom. -/
theorem beforeExponential_eq :
    «Combinator.beforeExponential» = leaf (axIdx beforeExponential 0) := rfl

/-- The mirror's index of the natural numbers object's first axiom. -/
theorem beforeNat_eq : «Combinator.beforeNat» = leaf (axIdx beforeNat 0) := rfl

/-- The mirror's index of the list objects' first axiom. -/
theorem beforeList_eq : «Combinator.beforeList» = leaf (axIdx beforeList 0) := rfl

/-- The index of an axiom of a block. -/
theorem axIdx_add (before : List (List Seq)) (k : ℕ) : axIdx before 0 + k = axIdx before k := by
  simp only [axIdx, Nat.add_zero]

/-- An equation with a certificate as the node of the equation and the certificate. -/
def encEqC (p : Eqn × Tree) : Tree := RoseTree.node 0 [encEqn p.1, p.2]

/-- The mirror's instance of a source's sequent at terms. -/
theorem inst_rel (s : Src) (σ : List Tree) :
    PMRel encEqC («Combinator.pInst» (encSrc s) σ) (inst s σ) := by
  unfold «Combinator.pInst» inst
  refine pmBind_rel encSeq encEqC _ _ (srcSeq_rel s) _ _ fun a ↦ ?_
  refine pmBind_rel _ encEqC _ _ (typeTerms_rel σ) _ _ fun tys ↦ ?_
  comb_simp [seqHyps_eq]
  refine pmBind_rel (fun hs ↦ RoseTree.node 0 (hs.map id)) encEqC _ _
    (pmMapM_rel id encEqn _ _ a.hyps fun q _ ↦ proveHyp_rel _ _ typePattern_rel tys q) _ _
    fun hs ↦ ?_
  comb_simp [List.map_id, seqConcl_eq, eqSubst_eq, mapT_eq, List.map_map, Function.comp_def,
    srcCert_eq]
  exact pmPure_rel encEqC (a.concl.subst σ, s.cert σ (tys.map Ty.dfd) hs)

/-- The mirror's expansion of an arrow into a product. -/
theorem etaExpand_rel (f : Tree) :
    PMRel encPair («Combinator.etaExpand» f) (etaExpand f) := by
  unfold «Combinator.etaExpand» etaExpand
  refine pmBind_rel encTy encPair _ _ (typeTerm_rel f) _ _ fun ty ↦ ?_
  by_cases hl : ty.hi.label = 7
  · rcases hc : ty.hi.children with _ | ⟨a, _ | ⟨b, _ | ⟨z, zs⟩⟩⟩
    · comb_simp [hl, hc]
      exact pmFail_rel encPair
    · comb_simp [hl, hc]
      exact pmFail_rel encPair
    · comb_simp [hl, hc, beforeProduct_eq, axIdx_add, srcAx_eq]
      generalize Src.ax (axIdx beforeProduct 11) = s
      refine pmBind_rel encEqC encPair _ _ (inst_rel s _) _ _ fun qc ↦ ?_
      comb_simp [encEqC, eqLhs_eq]
      exact pmPure_rel encPair (qc.1.lhs, PartialHorn.Cert.symm qc.2)
    · have h3 : ¬zs.length + 1 + 1 + 1 = 2 := by omega
      comb_simp [hl, hc, beq_iff_eq, h3]
      exact pmFail_rel encPair
  · comb_simp [hl, Bool.and_eq_true, beq_iff_eq, false_and]
    split
    · rename_i heq _
      exact (hl heq).elim
    · exact pmFail_rel encPair

@[simp] theorem deltaRule_eq (i : ℕ) :
    «Combinator.deltaRule» (leaf i) = encRw (deltaRule i) := by
  simp [«Combinator.deltaRule», «Combinator.rwAx», «Combinator.rwRule»,
    deltaRule, encRw, defAxIdx_eq]
  rfl

/-- The mirror's proof of an equation by normalization. -/
theorem byNorm_rel (rules : List RwRule) (q : Eqn) :
    PMRel id («Combinator.pByNorm» (rules.map encRw) (encEqn q)) (byNorm rules q) := by
  unfold «Combinator.pByNorm» byNorm
  simp only [eqLhs_eq, eqRhs_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel rules q.lhs) _ _ fun ⟨l, cl⟩ ↦ ?_
  refine pmBind_rel encPair id _ _ (normalize_rel rules q.rhs) _ _ fun ⟨r, cr⟩ ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ ?_ _ _ fun _ ↦ ?_
  · rw [← Bool.beq_eq_decide_eq]
    exact pmGuard_rel (l == r)
  · exact pmPure_rel id _

/-! Running the prover from a development. -/

/-- The mirror's initial state of a run is related to the initial state. -/
theorem runState_srel (dev : Development) (defs : List Defn) (infer : Bool) :
    SRel («Combinator.pst» (Const.node (leaf 0) (dev.map encDevEntry))
        (Const.node (leaf 0) []) (Const.node (leaf 0) []) (Const.node (leaf 0) (defs.map encDefn))
        (Const.node (leaf 0) («Prelude.append» «Theory.sig»
          («Base.mapT» (fun d ↦ «PartialHorn.opSig»
            (Const.node (leaf 0) («PartialHorn.pdCtx» d)) («PartialHorn.pdSort» d))
            (defs.map encDefn))))
        (ofBool infer))
      { dev := dev.toArray, defs := defs, sig := sig ++ defs.map (fun d ↦ (d.ctx, d.sort)),
        infer := infer } := by
  refine ⟨[], [], tRel_empty, tRel_empty, ?_⟩
  simp [«Combinator.pst», sig_eq, append_eq, mapT_eq, «PartialHorn.opSig», encOpSig,
    Function.comp_def]

/-- The mirror's run of a computation in a scope from a development. -/
theorem pmRun_eq {α : Type} (e : α → Tree) (m' : Tree → Tree → Tree) (m : PM α)
    (hm : PMRel e m' m) (sc : Scope) (dev : Development) (defs : List Defn) (infer : Bool) :
    «Combinator.pmRun» (encScope sc) (dev.map encDevEntry) m' (defs.map encDefn)
        (ofBool infer) =
      encOpt ((run sc dev m defs infer).map fun p ↦
        RoseTree.node 0 [e p.1, RoseTree.node 0 (p.2.map encDevEntry)]) := by
  have h1 := hm sc _ _ (runState_srel dev defs infer)
  unfold «Combinator.pmRun» Prover.run
  simp only []
  split at h1
  · rename_i heq
    rw [heq, h1]
    rfl
  · rename_i a st₂ heq
    obtain ⟨st₂', h2, h3⟩ := h1
    rw [heq, h3]
    change «Base.mapO» _ (encOpt (some _)) = _
    comb_simp [mapO_eq, stDev_srel h2]

/-- An index with a development as the node of the index and the node of the development's
entries. -/
def encIdxDev (p : ℕ × Development) : Tree :=
  RoseTree.node 0 [leaf p.1, RoseTree.node 0 (p.2.map encDevEntry)]

/-- The mirror's scope of a context and hypotheses. -/
@[simp] theorem scope_eq (ctx : List ℕ) (hyps : List Eqn) :
    «Combinator.scope» (RoseTree.node 0 (ctx.map leaf)) (RoseTree.node 0 (hyps.map encEqn)) =
      encScope ⟨ctx, hyps⟩ := rfl

/-- The mirror's proof of a sequent added to a development. -/
theorem proveSeq_eq (a : Seq) (m' : Tree → Tree → Tree) (m : PM Tree) (hm : PMRel id m' m)
    (defs : List Defn) (infer : Bool) (dev : Development) :
    «Combinator.proveSeq» (encSeq a) m' (defs.map encDefn) (ofBool infer)
        (dev.map encDevEntry) = encOpt ((proveSeq a m defs infer dev).map encIdxDev) := by
  unfold «Combinator.proveSeq» proveSeq
  simp only [seqCtx_eq, seqHyps_eq, node_leaf, scope_eq]
  rw [pmRun_eq id m' m hm]
  rcases Prover.run ⟨a.ctx, a.hyps⟩ dev m defs infer with _ | ⟨c, dev'⟩
  · rfl
  · comb_simp [bindO_eq, encIdxDev, encDevEntry, some_eq]
    simp [encIdxDev, encDevEntry, List.map_append]

/-- The mirror's normalization of a theorem's left side, added to a development. -/
theorem normalizeThm_eq (rules : List RwRule) (j : ℕ) (defs : List Defn) (infer : Bool)
    (dev : Development) :
    «Combinator.normalizeThm» (rules.map encRw) (leaf j) (defs.map encDefn) (ofBool infer)
        (dev.map encDevEntry) = encOpt ((normalizeThm rules j defs infer dev).map encIdxDev) := by
  unfold «Combinator.normalizeThm» normalizeThm
  simp only [nth_eq, List.getElem?_map]
  rcases dev[j]? with _ | ⟨a, c⟩
  · rfl
  · comb_simp [bindO_eq, encDevEntry, seqCtx_eq, seqHyps_eq, scope_eq, seqConcl_eq, eqLhs_eq,
      eqRhs_eq, Option.bind_eq_bind, Option.bind_some]
    rw [pmRun_eq encPair _ _ (normalize_rel rules a.concl.lhs)]
    rcases Prover.run ⟨a.ctx, a.hyps⟩ dev (normalize rules a.concl.lhs) defs infer with
      _ | ⟨⟨n, cn⟩, dev'⟩
    · rfl
    · comb_simp [bindO_eq, encIdxDev, encDevEntry, some_eq, encPair, eqn_eq]
      simp [encIdxDev, encDevEntry, List.map_append]

/-! Induction. -/

/-- The mirror's instance of a source's sequent, its hypotheses proved by the typing or by
normalization. -/
theorem instBy_rel (rules : List RwRule) (s : Src) (σ : List Tree) :
    PMRel encEqC («Combinator.instBy» (rules.map encRw) (encSrc s) σ)
      (instBy rules s σ) := by
  unfold «Combinator.instBy» instBy
  refine pmBind_rel encSeq encEqC _ _ (srcSeq_rel s) _ _ fun a ↦ ?_
  refine pmBind_rel _ encEqC _ _ (typeTerms_rel σ) _ _ fun tys ↦ ?_
  comb_simp [seqHyps_eq]
  refine pmBind_rel (fun hs ↦ RoseTree.node 0 (hs.map id)) encEqC _ _
    (pmMapM_rel id encEqn _ _ a.hyps fun q _ ↦
      pmOr_rel id _ _ _ _ (proveHyp_rel _ _ typePattern_rel tys q) ?_) _ _ fun hs ↦ ?_
  · rw [eqSubst_eq]
    exact byNorm_rel rules (q.subst σ)
  · comb_simp [List.map_id, seqConcl_eq, eqSubst_eq, mapT_eq, List.map_map, Function.comp_def,
      srcCert_eq]
    exact pmPure_rel encEqC (a.concl.subst σ, s.cert σ (tys.map Ty.dfd) hs)

/-- The mirror's certificate of an equation's rewriting inside a term. -/
theorem congBy_rel (e : Eqn) (ce p : Tree) :
    BRel («Combinator.congBy» (encEqn e) ce p) (congBy e ce p) := by
  refine para_rel BRel _ _ (fun l xs hx t ↦ ?_) p
  simp only [«Combinator.congStep», List.map_map, Function.comp_def]
  refine pmBind_rel encTy id _ _ (typeTerm_rel _) _ _ fun ty ↦ ?_
  comb_simp [eqLhs_eq, eqRhs_eq]
  simp only [Bool.beq_eq_decide_eq, bne, Bool.or_assoc, Sorts.obj]
  split_ifs
  · exact pmPure_rel id ty.dfd
  · exact pmPure_rel id ce
  · exact pmBind_rel encTy id _ _ (typeTerm_rel t) _ _ fun yt ↦ objEq_rel ty yt
  · exact pmFail_rel id
  · refine pmBind_rel (RoseTree.node 0) id _ _ (bridgeKids_rel xs hx t.children) _ _ fun cs ↦ ?_
    rw [RoseTree.children_node]
    exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's certificate that an arrow from the natural numbers object is a recursion. -/
theorem natRecUniq_rel (rules : List RwRule) (z s f : Tree) :
    PMRel id («Combinator.natRecUniq» (rules.map encRw) z s f) (natRecUniq rules z s f) := by
  unfold «Combinator.natRecUniq» natRecUniq
  comb_simp [beforeNat_eq, axIdx_add, srcAx_eq]
  generalize Src.ax (axIdx beforeNat 12) = src
  refine pmBind_rel encEqC id _ _ (instBy_rel rules src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC]
  exact pmPure_rel id qc.2

set_option maxRecDepth 100000 in
/-- The mirror's certificate that an arrow from a list object is a recursion. -/
theorem listRecUniq_rel (rules : List RwRule) (a z s f : Tree) :
    PMRel id («Combinator.listRecUniq» (rules.map encRw) a z s f)
      (listRecUniq rules a z s f) := by
  unfold «Combinator.listRecUniq» listRecUniq
  comb_simp [beforeList_eq, axIdx_add, srcAx_eq]
  generalize Src.ax (axIdx beforeList 13) = src
  refine pmBind_rel encEqC id _ _ (instBy_rel rules src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC]
  exact pmPure_rel id qc.2

set_option maxRecDepth 100000 in
/-- The mirror's proof by induction on the natural numbers object. -/
theorem byNatInduction_rel (rules : List RwRule) (z s : Tree) (q : Eqn) :
    PMRel id («Combinator.byNatInduction» (rules.map encRw) z s (encEqn q))
      (byNatInduction rules z s q) := by
  unfold «Combinator.byNatInduction» byNatInduction
  simp only [eqLhs_eq, eqRhs_eq]
  refine pmBind_rel id id _ _ (natRecUniq_rel rules z s q.lhs) _ _ fun cl ↦ ?_
  refine pmBind_rel id id _ _ (natRecUniq_rel rules z s q.rhs) _ _ fun cr ↦ ?_
  comb_simp []
  exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof by induction on a list object. -/
theorem byListInduction_rel (rules : List RwRule) (a z s : Tree) (q : Eqn) :
    PMRel id («Combinator.byListInduction» (rules.map encRw) a z s (encEqn q))
      (byListInduction rules a z s q) := by
  unfold «Combinator.byListInduction» byListInduction
  simp only [eqLhs_eq, eqRhs_eq]
  refine pmBind_rel id id _ _ (listRecUniq_rel rules a z s q.lhs) _ _ fun cl ↦ ?_
  refine pmBind_rel id id _ _ (listRecUniq_rel rules a z s q.rhs) _ _ fun cr ↦ ?_
  comb_simp []
  exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof by induction on a list object with a parameter. -/
theorem byListParamInduction_rel (rules : List RwRule) (a z s : Tree) (q : Eqn) :
    PMRel id («Combinator.byListParamInduction» (rules.map encRw) a z s (encEqn q))
      (byListParamInduction rules a z s q) := by
  unfold «Combinator.byListParamInduction» byListParamInduction
  simp only [eqLhs_eq, eqRhs_eq]
  refine pmBind_rel encTy id _ _ (typeTerm_rel q.lhs) _ _ fun ty ↦ ?_
  by_cases hl : ty.lo.label = 7
  · rcases hc : ty.lo.children with _ | ⟨l, _ | ⟨p, _ | ⟨w, ws⟩⟩⟩
    · comb_simp [hl, hc]
      exact pmFailBind_rel id _
    · comb_simp [hl, hc]
      exact pmFailBind_rel id _
    · comb_simp [hl, hc, beforeExponential_eq, axIdx_add, srcAx_eq, eqn_eq, mirror_exp,
        mirror_prod, mirror_curry, mirror_one, mirror_comp, mirror_cSnd, mirror_cFst, mirror_cPair,
        mirror_ev, pure_bind]
      generalize Src.ax (axIdx beforeExponential 7) = src
      refine pmBind_rel id id _ _ (byListInduction_rel rules a _ _ ⟨_, _⟩) _ _ fun cc ↦ ?_
      refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun bfp ↦ ?_
      refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun bgp ↦ ?_
      comb_simp [encEqC, eqLhs_eq, eqn_eq]
      refine pmBind_rel id id _ _ (congBy_rel _ cc _ _) _ _ fun mid ↦ ?_
      exact pmPure_rel id _
    · have h3 : ¬ws.length + 1 + 1 + 1 = 2 := by omega
      comb_simp [hl, hc, beq_iff_eq, h3]
      exact pmFailBind_rel id _
  · comb_simp [hl, Bool.and_eq_true, beq_iff_eq, false_and]
    split
    · rename_i heq _
      exact (hl heq).elim
    · exact pmFailBind_rel id _

/-! The library. -/

@[simp] theorem rwThm_eq (j : ℕ) :
    «Combinator.rwThm» (leaf j) = encRw { src := .thm j } := rfl

set_option maxRecDepth 100000 in
theorem baseRules_eq : «Combinator.baseRules» = baseRules.map encRw := rfl

/-- The mirror's distribution of a composite over a pairing. -/
theorem compPairSeq_eq : «Combinator.compPairSeq» = encSeq compPairSeq := rfl

/-- The mirror's pairing of a product's projections. -/
theorem pairFstSndSeq_eq : «Combinator.pairFstSndSeq» = encSeq pairFstSndSeq := rfl

/-- The mirror's evaluation after a pairing of a currying after an arrow. -/
theorem evCurrySeq_eq : «Combinator.evCurrySeq» = encSeq evCurrySeq := rfl

/-- The mirror's evaluation after a pairing of a currying. -/
theorem evCurry0Seq_eq : «Combinator.evCurry0Seq» = encSeq evCurry0Seq := rfl

/-- The mirror's naturality of currying. -/
theorem curryNatSeq_eq : «Combinator.curryNatSeq» = encSeq curryNatSeq := rfl

/-- The mirror's morphism from the terminal object to itself. -/
theorem bangOneSeq_eq : «Combinator.bangOneSeq» = encSeq bangOneSeq := rfl

@[simp] theorem seqLhs_eq (a : Seq) :
    «Combinator.seqLhs» (encSeq a) = a.concl.lhs := by
  simp [«Combinator.seqLhs», seqConcl_eq, eqLhs_eq]

@[simp] theorem seqRhs_eq (a : Seq) :
    «Combinator.seqRhs» (encSeq a) = a.concl.rhs := by
  simp [«Combinator.seqRhs», seqConcl_eq, eqRhs_eq]

/-- The mirror's guard of two trees' equality. -/
theorem pmGuardEq_rel (a b : Tree) :
    PMRel (fun _ ↦ leaf 0) («Combinator.pmGuard» (Const.equal a b))
      (guard (a == b) : PM Unit) := by
  rw [equal_eq, ← Bool.beq_eq_decide_eq]
  exact pmGuard_rel (a == b)

/-- The mirror's proof of {lit}`compPairSeq`. -/
theorem compPairProof_rel : PMRel id «Combinator.compPairProof» compPairProof := by
  unfold «Combinator.compPairProof» compPairProof
  simp only [compPairSeq_eq, seqLhs_eq, seqRhs_eq]
  refine pmBind_rel encPair id _ _ (etaExpand_rel _) _ _ fun ec ↦ ?_
  comb_simp [encPair, baseRules_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel baseRules _) _ _ fun nc ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ (pmGuardEq_rel _ _) _ _ fun _ ↦ ?_
  exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof of {lit}`pairFstSndSeq`. -/
theorem pairFstSndProof_rel : PMRel id «Combinator.pairFstSndProof» pairFstSndProof := by
  unfold «Combinator.pairFstSndProof» pairFstSndProof
  comb_simp [beforeProduct_eq, axIdx_add, srcAx_eq, mirror_prod, mirror_idt, mirror_x,
    pairFstSndSeq_eq, seqLhs_eq, baseRules_eq]
  generalize Src.ax (axIdx beforeProduct 11) = src
  refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC, eqLhs_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel baseRules _) _ _ fun nc ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ (pmGuardEq_rel _ _) _ _ fun _ ↦ ?_
  exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof of {lit}`evCurrySeq`. -/
theorem evCurryProof_rel (cp : ℕ) :
    PMRel id («Combinator.evCurryProof» (leaf cp)) (evCurryProof cp) := by
  unfold «Combinator.evCurryProof» evCurryProof
  comb_simp [beforeExponential_eq, axIdx_add, srcAx_eq, mirror_x, mirror_cPair, mirror_comp,
    evCurrySeq_eq, seqLhs_eq, baseRules_eq, rwThm_eq, append_eq, single_eq]
  rw [show baseRules.map encRw ++ [encRw { src := .thm cp }] =
    (baseRules ++ [({ src := .thm cp } : RwRule)]).map encRw by simp]
  generalize Src.ax (axIdx beforeExponential 7) = src
  refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC, eqLhs_eq, mirror_comp]
  refine pmBind_rel encPair id _ _ (normalize_rel _ _) _ _ fun nu ↦ ?_
  refine pmBind_rel encPair id _ _ (normalize_rel _ _) _ _ fun ng ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ (pmGuardEq_rel _ _) _ _ fun _ ↦ ?_
  refine pmBind_rel encTy id _ _ (typeTerm_rel _) _ _ fun du ↦ ?_
  refine pmBind_rel encTy id _ _ (typeTerm_rel _) _ _ fun dg ↦ ?_
  comb_simp []
  exact pmPure_rel id _

/-- The mirror's proof of {lit}`evCurry0Seq`. -/
theorem evCurry0Proof_rel (ec : ℕ) :
    PMRel id («Combinator.evCurry0Proof» (leaf ec)) (evCurry0Proof ec) := by
  unfold «Combinator.evCurry0Proof» evCurry0Proof
  comb_simp [srcThm_eq, mirror_x, mirror_idt, evCurry0Seq_eq, seqLhs_eq, seqRhs_eq, baseRules_eq]
  refine pmBind_rel encEqC id _ _ (inst_rel _ _) _ _ fun qc ↦ ?_
  comb_simp [encEqC, eqLhs_eq, eqRhs_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel baseRules _) _ _ fun nc ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ ?_ _ _ fun _ ↦ ?_
  · simp only [← Bool.beq_eq_decide_eq]
    exact pmGuard_rel _
  · exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof of {lit}`curryNatSeq`. -/
theorem curryNatProof_rel (cp ec : ℕ) :
    PMRel id («Combinator.curryNatProof» (leaf cp) (leaf ec)) (curryNatProof cp ec) := by
  unfold «Combinator.curryNatProof» curryNatProof
  comb_simp [beforeExponential_eq, axIdx_add, srcAx_eq, mirror_x, mirror_dom, mirror_cod,
    curryNatSeq_eq, seqLhs_eq, seqRhs_eq, baseRules_eq, rwThm_eq, append_eq]
  rw [show baseRules.map encRw ++ [encRw { src := .thm cp }, encRw { src := .thm ec }] =
    (baseRules ++ [({ src := .thm cp } : RwRule), { src := .thm ec }]).map encRw by simp]
  generalize Src.ax (axIdx beforeExponential 8) = src
  refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC, eqLhs_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel _ _) _ _ fun nc ↦ ?_
  refine pmBind_rel encPair id _ _ (normalize_rel _ _) _ _ fun rc ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ (pmGuardEq_rel _ _) _ _ fun _ ↦ ?_
  exact pmPure_rel id _

set_option maxRecDepth 100000 in
/-- The mirror's proof of {lit}`bangOneSeq`. -/
theorem bangOneProof_rel : PMRel id «Combinator.bangOneProof» bangOneProof := by
  unfold «Combinator.bangOneProof» bangOneProof
  comb_simp [beforeTerminal_eq, axIdx_add, srcAx_eq, mirror_idt, mirror_one, mirror_bang,
    baseRules_eq, single_eq]
  generalize Src.ax (axIdx beforeTerminal 3) = src
  refine pmBind_rel encEqC id _ _ (inst_rel src _) _ _ fun qc ↦ ?_
  comb_simp [encEqC, eqRhs_eq]
  refine pmBind_rel encPair id _ _ (normalize_rel baseRules _) _ _ fun nc ↦ ?_
  comb_simp [encPair]
  refine pmBind_rel (fun _ ↦ leaf 0) id _ _ (pmGuardEq_rel _ _) _ _ fun _ ↦ ?_
  exact pmPure_rel id _

/-- The mirror's rules of the axioms and of the library's derived equations. -/
theorem libRules_eq (i : LibIdx) :
    «Combinator.libRules» (encIdx i) = (rules i).map encRw := by
  simp [«Combinator.libRules», «Theory.l5», «Theory.l4»,
    «Theory.l3», «Theory.l2», encIdx, rules, baseRules_eq, append_eq]

/-- The mirror's proof of a sequent added to a development, with no definitions in force. -/
theorem proveSeq_nil (a : Seq) (m' : Tree → Tree → Tree) (m : PM Tree) (hm : PMRel id m' m)
    (infer : Bool) (d' : List Tree) (dev : Development) (h : d' = dev.map encDevEntry) :
    «Combinator.proveSeq» (encSeq a) m' [] (ofBool infer) d' =
      encOpt ((proveSeq a m [] infer dev).map encIdxDev) := by
  subst h
  exact proveSeq_eq a m' m hm [] infer dev

set_option maxRecDepth 100000 in
/-- The mirror's library. -/
theorem libraryWith_eq (infer : Bool) :
    «Combinator.libraryWith» (ofBool infer) = encLib (libraryWith infer) := by
  unfold «Combinator.libraryWith» libraryWith
  simp only [compPairSeq_eq, pairFstSndSeq_eq, evCurrySeq_eq, evCurry0Seq_eq, curryNatSeq_eq,
    bangOneSeq_eq, StateT.run_bind]
  rw [proveSeq_nil compPairSeq _ _ compPairProof_rel infer [] [] rfl]
  simp only [StateT.run]
  rcases proveSeq compPairSeq compPairProof [] infer [] with _ | ⟨cp, d1⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some]
  rw [proveSeq_nil pairFstSndSeq _ _ pairFstSndProof_rel infer _ d1 rfl]
  rcases proveSeq pairFstSndSeq pairFstSndProof [] infer d1 with _ | ⟨pf, d2⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some]
  rw [proveSeq_nil evCurrySeq _ _ (evCurryProof_rel cp) infer _ d2 rfl]
  rcases proveSeq evCurrySeq (evCurryProof cp) [] infer d2 with _ | ⟨ec, d3⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some]
  rw [proveSeq_nil evCurry0Seq _ _ (evCurry0Proof_rel ec) infer _ d3 rfl]
  rcases proveSeq evCurry0Seq (evCurry0Proof ec) [] infer d3 with _ | ⟨e0, d4⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some]
  rw [proveSeq_nil curryNatSeq _ _ (curryNatProof_rel cp ec) infer _ d4 rfl]
  rcases proveSeq curryNatSeq (curryNatProof cp ec) [] infer d4 with _ | ⟨cn, d5⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some]
  rw [proveSeq_nil bangOneSeq _ _ bangOneProof_rel infer _ d5 rfl]
  rcases proveSeq bangOneSeq bangOneProof [] infer d5 with _ | ⟨bo, d6⟩
  · rfl
  comb_simp [bindO_eq, encIdxDev, Option.bind_eq_bind, Option.bind_some, encLib, encIdx,
    «Theory.l6», some_eq]
  rfl

end GebTests.Prototypes.FreeTopos.Agreement.Combinator
