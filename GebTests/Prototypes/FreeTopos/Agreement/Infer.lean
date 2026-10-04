/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.PartialHorn
public import GebTests.Prototypes.FreeTopos.Agreement.Theory

set_option doc.verso true in
/-!
# The inference of typings in the checker written in Geb

The functions of {lit}`bootstrap/free-topos/infer.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the Lean inference of the typings of terms at every
encoded input: the rules by which the axioms prove an application defined and bound its domain
and codomain, the environment of a theory extended by definitions, and the inference of a
pattern instance's typing and of a term's at a fuel.

## Main definitions

* {lit}`PatRel`, {lit}`TreeRel` — the relations of the mirror's inference of a pattern instance's
  typing and of a term's to the inference's.

## Main statements

* {lit}`findAxiom_eq` — the first axiom passing a test.
* {lit}`envOfDefs_eq` — the environment of a theory extended by definitions.
* {lit}`infers_eq` — the inference of typings at a fuel.

## Tags

inference, typing, partial Horn logic, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Infer

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Base GebTests.Prototypes.FreeTopos.Agreement.PartialHorn
  GebTests.Prototypes.FreeTopos.Agreement.Theory GebTests.Prototypes.FreeTopos.Agreement.Fold
open scoped FinEnum

/-- The right fold that counts indices down from an encoded list's end finds the first element
passing a test, with its index. -/
theorem foldr_countdown {α : Type} (e : α → Tree) (f : Tree → Tree) (L : ℕ) :
    ∀ (ys : List α) (n : ℕ), n + ys.length = L →
      (ys.map e).foldr (fun (y : Tree) (s : Tree × Tree) ↦ (Const.sub s.1 (leaf 1),
        if (f y).label ≠ 0 then «Prelude.some» (Const.sub s.1 (leaf 1)) else s.2))
        (leaf L, «Prelude.none») =
        (leaf n, encOpt (((ys.zipIdx n).find? fun q ↦ (f (e q.1)).label != 0).map
          fun q ↦ leaf q.2)) :=
  List.rec (fun n h ↦ by simp only [List.length_nil, Nat.add_zero] at h; subst h; rfl)
    fun y ys ih n hn ↦ by
      rw [List.map_cons, List.foldr_cons, ih (n + 1) (by simp only [List.length_cons] at hn; omega)]
      simp only [sub_leaf, Nat.add_sub_cancel, List.zipIdx_cons, List.find?_cons]
      cases hb : (f (e y)).label != 0 <;> simp_all [some_eq]

/-- The mirror's index of the first axiom passing a test. -/
@[simp] theorem findAxiom_eq (f : Tree → Tree) :
    «Infer.findAxiom» f = encOpt ((indexedAxioms.find? fun q ↦
      (f (encSeq q.1)).label != 0).map fun q ↦ leaf q.2) := by
  simp only [«Infer.findAxiom», axioms_eq, length_eq, List.length_map, foldr_eq]
  rw [foldr_countdown encSeq f axioms.length axioms 0 (Nat.zero_add _)]
  rfl

/-- The mirror's argument sorts of an operation of the signature. -/
@[simp] theorem argSorts_eq (k : ℕ) :
    «Infer.argSorts» (leaf k) = (argSorts k).map leaf := by
  simp only [«Infer.argSorts», sig_eq, nth_eq, List.getElem?_map, argSorts]
  cases sig[k]? <;> simp [opArgs_eq]

/-- The mirror's rule by which the axioms prove an application of an operation defined. -/
theorem dfdRule_eq (k : ℕ) :
    «Infer.dfdRule» (leaf k) = encOpt ((dfdRule k).map encDfdRule) := by
  simp only [«Infer.dfdRule», argSorts_eq, length_eq, List.length_map, opVars_eq,
    findAxiom_eq, seqCtx_eq, seqHyps_eq, seqConcl_eq, eqLhs_eq, eqRhs_eq, equalTs_eq, equal_eq,
    and_eq, not_eq, isEmpty_eq, eq_leaf, label_eq, children_eq, single_eq, ofBool_bne,
    map_leaf_inj, isSome_eq, ofBool_label, dfdRule, List.isEmpty_map]
  simp only [bne, beq_eq_decide, Bool.and_assoc]
  generalize indexedAxioms.find? _ = o1
  generalize indexedAxioms.find? _ = o2
  generalize indexedAxioms.find? _ = o3
  rcases o1 with _ | ⟨a, j⟩ <;> rcases o2 with _ | ⟨b, i⟩ <;> rcases o3 with _ | ⟨c, h⟩ <;> rfl

/-- The mirror's axiom that bounds an application of an operation by another's. -/
theorem boundRule_eq (o k : ℕ) :
    «Infer.boundRule» (leaf o) (leaf k) = encOpt ((boundRule o k).map leaf) := by
  simp only [«Infer.boundRule», argSorts_eq, length_eq, List.length_map, opVars_eq,
    findAxiom_eq, and_label, equalTs_eq, ofBool_bne, map_leaf_inj, seqCtx_eq, seqConcl_eq,
    seqHyps_eq, eqLhs_eq, eqRhs_eq, equal_label, allT_label, List.all_map, Function.comp_def,
    phOp_eq, single_eq, boundRule]
  simp only [beq_eq_decide, Bool.and_assoc, Option.map_map, Function.comp_def]

/-- The mirror's definedness rules, by operation. -/
theorem dfdRules_eq :
    «Infer.dfdRules» = dfdRules.map fun r ↦ encOpt (r.map encDfdRule) := by
  simp only [«Infer.dfdRules», sig_eq, length_eq, List.length_map, range_eq, mapT_eq,
    List.map_map, Function.comp_def, dfdRule_eq, dfdRules]

/-- The mirror's domain rules, by operation. -/
theorem domRules_eq : «Infer.domRules» = domRules.map fun r ↦ encOpt (r.map leaf) := by
  simp only [«Infer.domRules», sig_eq, length_eq, List.length_map, range_eq, mapT_eq,
    List.map_map, Function.comp_def, boundRule_eq, domRules]

/-- The mirror's codomain rules, by operation. -/
theorem codRules_eq : «Infer.codRules» = codRules.map fun r ↦ encOpt (r.map leaf) := by
  simp only [«Infer.codRules», sig_eq, length_eq, List.length_map, range_eq, mapT_eq,
    List.map_map, Function.comp_def, boundRule_eq, codRules]

/-- The mirror's theory extended by definitions. -/
@[simp] theorem ext_eq (ds : List PartialHorn.Defn) :
    «Infer.ext» (ds.map encDefn) = encTheory (ext ds) := by
  simp only [«Infer.ext», Theory.toposTheory_eq, thyExtendAll_eq]

/-- The mirror's environment of the theory extended by definitions. -/
theorem envOfDefs_eq (ds : List PartialHorn.Defn) :
    «Infer.envOfDefs» (ds.map encDefn) = encExtEnv (ExtEnv.ofDefs ds) := by
  simp only [«Infer.envOfDefs», ext_eq, thyAxioms_eq, thySig_eq, dfdRules_eq,
    domRules_eq, codRules_eq]
  rfl

/-- The mirror's sort of a typing. -/
@[simp] theorem annSort_eq (a : Ann) : «Infer.annSort» (encAnn a) = leaf a.sort := by
  simp [«Infer.annSort», encAnn]

/-- The mirror's lower canonical form of a typing. -/
@[simp] theorem annLo_eq (a : Ann) : «Infer.annLo» (encAnn a) = a.lo := by
  simp [«Infer.annLo», encAnn]

/-- The mirror's upper canonical form of a typing. -/
@[simp] theorem annHi_eq (a : Ann) : «Infer.annHi» (encAnn a) = a.hi := by
  simp [«Infer.annHi», encAnn]

/-- The mirror's typing of its sort and canonical forms. -/
@[simp] theorem ann_eq (s : ℕ) (lo hi : Tree) :
    «Infer.ann» (leaf s) lo hi = encAnn ⟨s, lo, hi⟩ := rfl

/-- The mirror's term of a typed term. -/
@[simp] theorem tyTerm_eq (p : Tree × Ann) : «Infer.tyTerm» (encTyped p) = p.1 := by
  simp [«Infer.tyTerm», encTyped]

/-- The mirror's typing of a typed term. -/
@[simp] theorem tyAnn_eq (p : Tree × Ann) :
    «Infer.tyAnn» (encTyped p) = encAnn p.2 := by
  simp [«Infer.tyAnn», encTyped]

/-- The mirror's typed term of a term and a typing. -/
@[simp] theorem typed_eq (t : Tree) (a : Ann) :
    «Infer.typed» t (encAnn a) = encTyped (t, a) := rfl

/-- The mirror's definitions of an environment. -/
@[simp] theorem envDefs_eq (E : ExtEnv) :
    «Infer.envDefs» (encExtEnv E) = E.defs.map encDefn := by
  simp [«Infer.envDefs», encExtEnv]

/-- The mirror's axioms of an environment. -/
@[simp] theorem envAxs_eq (E : ExtEnv) :
    «Infer.envAxs» (encExtEnv E) = E.axs.toList.map encSeq := by
  simp [«Infer.envAxs», encExtEnv]

/-- The mirror's signature of an environment. -/
@[simp] theorem envSg_eq (E : ExtEnv) :
    «Infer.envSg» (encExtEnv E) = E.sg.toList.map encOpSig := by
  simp [«Infer.envSg», encExtEnv]

/-- The mirror's definedness rules of an environment. -/
@[simp] theorem envDfds_eq (E : ExtEnv) :
    «Infer.envDfds» (encExtEnv E) =
      E.dfds.toList.map fun r ↦ encOpt (r.map encDfdRule) := by
  simp [«Infer.envDfds», encExtEnv]

/-- The mirror's domain rules of an environment. -/
@[simp] theorem envDoms_eq (E : ExtEnv) :
    «Infer.envDoms» (encExtEnv E) = E.doms.toList.map fun r ↦ encOpt (r.map leaf) := by
  simp [«Infer.envDoms», encExtEnv]

/-- The mirror's codomain rules of an environment. -/
@[simp] theorem envCods_eq (E : ExtEnv) :
    «Infer.envCods» (encExtEnv E) = E.cods.toList.map fun r ↦ encOpt (r.map leaf) := by
  simp [«Infer.envCods», encExtEnv]

/-- The mirror's sorts of typed arguments. -/
@[simp] theorem argSortsOf_eq (args : List (Tree × Ann)) :
    «Infer.argSortsOf» (args.map encTyped) = (args.map (·.2.sort)).map leaf := by
  simp [«Infer.argSortsOf», List.map_map, Function.comp_def]

/-- An inference of the checker written in Geb represents an inference of pattern instances'
typings when, at every encoded arguments and pattern, it is the encoding of the Lean one's. -/
def PatRel (v : List Tree → Tree → Tree) (w : List (Tree × Ann) → Tree → Option (Tree × Ann)) :
    Prop :=
  ∀ args t, v (args.map encTyped) t = encOpt ((w args t).map encTyped)

/-- An inference of the checker written in Geb represents an inference of terms' typings when, at
every term, it is the encoding of the Lean one's. -/
def TreeRel (v : Tree → Tree) (w : Tree → Option Ann) : Prop :=
  ∀ t, v t = encOpt ((w t).map encAnn)

/-- The mirror's test of a hypothesis at typed arguments. -/
theorem hypOk_eq {v : List Tree → Tree → Tree} {w : List (Tree × Ann) → Tree → Option (Tree × Ann)}
    (hvw : PatRel v w) (args : List (Tree × Ann)) (h : PartialHorn.Eqn) :
    «Infer.hypOk» v (args.map encTyped) (encEqn h) = ofBool (hypOk w args h) := by
  simp only [«Infer.hypOk», eqLhs_eq, eqRhs_eq, hvw args, equal_eq, ofBool_label,
    decide_eq_true_eq, hypOk, beq_eq_decide]
  by_cases he : h.lhs = h.rhs
  · simp [he]
  · simp only [he, ↓reduceIte]
    cases w args h.lhs <;> cases w args h.rhs <;>
      simp [Sorts.obj, Bool.and_assoc, beq_eq_decide] <;> rfl

/-- The mirror's canonical bound of an application of an operation by an axiom. -/
theorem bound_eq {v : List Tree → Tree → Tree} {w : List (Tree × Ann) → Tree → Option (Tree × Ann)}
    (hvw : PatRel v w) (E : ExtEnv) (args : List (Tree × Ann)) (o k j : ℕ) :
    «Infer.bound» (encExtEnv E) v (args.map encTyped) (leaf o) (leaf k) (leaf j) =
      encOpt (bound E w args o k j) := by
  mirror_simp [«Infer.bound», envAxs_eq, argSortsOf_eq, bound]
  cases E.axs[j]? with
  | none => rfl
  | some a =>
    mirror_simp [Option.map_some, Option.elim_some, opVars_eq, phOp_eq, seqScoped_eq, seqCtx_eq,
      seqConcl_eq, seqHyps_eq, eqLhs_eq, eqRhs_eq, hvw args, Option.isSome_map, beq_eq_decide,
      Bool.and_assoc]
    split_ifs
    · cases w args a.concl.rhs with
      | none => rfl
      | some p =>
        mirror_simp [Option.map_some, Option.elim_some, tyAnn_eq, annSort_eq, annLo_eq]
        split_ifs <;> rfl
    · rfl

/-- The mirror's test that an axiom proves an application of an operation defined. -/
theorem dfdOk_eq {v : List Tree → Tree → Tree} {w : List (Tree × Ann) → Tree → Option (Tree × Ann)}
    (hvw : PatRel v w) (E : ExtEnv) (args : List (Tree × Ann)) (k : ℕ) :
    «Infer.dfdOk» (encExtEnv E) v (args.map encTyped) (leaf k) =
      ofBool (dfdOk E w args k) := by
  mirror_simp [«Infer.dfdOk», argSortsOf_eq, envDfds_eq, dfdOk]
  cases E.dfds[k]? with
  | none => rfl
  | some r =>
    cases r with
    | none => rfl
    | some rule =>
      cases rule with
      | direct j =>
        mirror_simp [encDfdRule, envAxs_eq]
        cases E.axs[j]? with
        | none => rfl
        | some a =>
          mirror_simp [seqScoped_eq, seqCtx_eq, seqConcl_eq, seqHyps_eq, eqLhs_eq, eqRhs_eq,
            opVars_eq, allT_map _ encEqn _ a.hyps fun h _ ↦ hypOk_eq hvw args h, beq_eq_decide,
            Bool.and_assoc]
      | strict j =>
        mirror_simp [encDfdRule, envAxs_eq]
        cases E.axs[j]? with
        | none => rfl
        | some a =>
          mirror_simp [seqCtx_eq, seqConcl_eq, seqHyps_eq, eqLhs_eq, opVars_eq, beq_eq_decide,
            Bool.and_assoc, bne]
      | rhs j =>
        mirror_simp [encDfdRule, envAxs_eq]
        cases E.axs[j]? with
        | none => rfl
        | some a =>
          mirror_simp [seqCtx_eq, seqConcl_eq, seqHyps_eq, eqRhs_eq, opVars_eq, beq_eq_decide,
            Bool.and_assoc]

/-- The mirror's typing of an object-valued application of an operation of the signature. -/
theorem inferObj_eq (k : ℕ) (args : List (Tree × Ann)) :
    «Infer.inferObj» (leaf k) (args.map encTyped) =
      encOpt ((inferObj k args).map encAnn) := by
  rcases k with _ | _ | k <;> rcases args with _ | ⟨p, _ | ⟨q, r⟩⟩ <;>
    first
    | (by_cases hs : p.2.sort = 1 <;>
        simp [«Infer.inferObj», inferObj, some_eq, none_eq, beq_eq_decide, Sorts.obj,
          Sorts.arr, Function.comp_def, ofBool_label_eq_zero, hs, -Nat.add_eq_right])
    | simp [«Infer.inferObj», inferObj, some_eq, beq_eq_decide, Sorts.obj,
        ofBool_label_eq_zero, -Nat.add_eq_right]

/-- The mirror's typing of an arrow-valued application of an operation of the signature. -/
theorem inferArr_eq {v : List Tree → Tree → Tree}
    {w : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hvw : PatRel v w) (E : ExtEnv)
    (k : ℕ) (args : List (Tree × Ann)) :
    «Infer.inferArr» (encExtEnv E) v (leaf k) (args.map encTyped) =
      encOpt ((inferArr E w k args).map encAnn) := by
  mirror_simp [«Infer.inferArr», envDoms_eq, envCods_eq, inferArr]
  rcases E.doms[k]? with _ | _ | jd <;> rcases E.cods[k]? with _ | _ | jc <;>
    mirror_simp [bound_eq hvw, Option.join, ann_eq, id_eq] <;>
    first
    | rfl
    | (cases bound E w args 0 k jd <;> cases bound E w args 1 k jc <;> rfl)
    | (cases bound E w args 0 k jd <;> rfl)

/-- The mirror's index of the first axiom of a definition. -/
@[simp] theorem defAxIdx_eq (i : ℕ) :
    «Infer.defAxIdx» (leaf i) = leaf (defAxIdx i) := by
  simp [«Infer.defAxIdx», axioms_eq, defAxIdx]

/-- The mirror's typing of an application of a definition. -/
theorem inferDef_eq {v : List Tree → Tree → Tree}
    {w : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hvw : PatRel v w) (E : ExtEnv)
    (k : ℕ) (args : List (Tree × Ann)) :
    «Infer.inferDef» (encExtEnv E) v (leaf k) (args.map encTyped) =
      encOpt ((inferDef E w k args).map encAnn) := by
  mirror_simp [«Infer.inferDef», envDefs_eq, envAxs_eq, sig_eq, defAxIdx_eq, inferDef]
  cases E.defs[k - sig.length]? with
  | none => cases E.axs[defAxIdx (k - sig.length)]? <;> rfl
  | some d =>
    cases E.axs[defAxIdx (k - sig.length)]? with
    | none => rfl
    | some a =>
      mirror_simp [pdBody_eq, seqScoped_eq, seqCtx_eq, seqHyps_eq, seqConcl_eq, argSortsOf_eq,
        eqn_eq, opVars_eq, hvw args, map_encEqn_inj, encEqn_inj, beq_eq_decide, Bool.and_assoc,
        tyAnn_eq]
      have hh : a.hyps.map encEqn = [encEqn ⟨d.body, d.body⟩] ↔ a.hyps = [⟨d.body, d.body⟩] := by
        exact map_encEqn_inj (hs' := [⟨d.body, d.body⟩])
      simp only [hh]
      split_ifs <;> simp [Option.map_map, Function.comp_def, none_eq]

/-- The mirror's typing of an application of an operation to typed arguments. -/
theorem inferOp_eq {v : List Tree → Tree → Tree}
    {w : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hvw : PatRel v w) (E : ExtEnv)
    (k : ℕ) (args : List (Tree × Ann)) :
    «Infer.inferOp» (encExtEnv E) v (leaf k) (args.map encTyped) =
      encOpt ((inferOp E w k args).map encAnn) := by
  mirror_simp [«Infer.inferOp», envSg_eq, inferOp]
  cases E.sg[k]? with
  | none => rfl
  | some o =>
    obtain ⟨as, srt⟩ := o
    mirror_simp [argSortsOf_eq, opArgs_eq, opSort_eq, sig_eq, dfdOk_eq hvw, inferObj_eq,
      inferArr_eq hvw, inferDef_eq hvw, beq_eq_decide, Sorts.obj, Sorts.arr, decide_eq_true_eq]
    split_ifs <;> simp [none_eq]

/-- The mirror's definedness of a term. -/
@[simp] theorem dfd_eq (t : Tree) : «Theory.dfd» t = encEqn (dfd t) := rfl

/-- The mirror's canonical form of a side, the domain or the codomain, of a variable of arrows:
the side's canonical form under the hypothesis that equates it with an object, or the side itself
when none does, where the axioms declare the side defined. -/
theorem inferSide_eq {tv : Tree → Tree} {tw : Tree → Option Ann} (htv : TreeRel tv tw)
    (E : ExtEnv) (H : List PartialHorn.Eqn) (v o : ℕ) :
    «Infer.inferSide» (encExtEnv E) (H.map encEqn) tv (leaf v) (leaf o) =
      encOpt (if (match E.axs[o]? with
          | some a =>
            a.ctx == [Sorts.arr] && a.hyps.isEmpty && a.concl == dfd (PartialHorn.op o [x 0])
          | none => false) then
        match H.find? (·.lhs == PartialHorn.op o [PartialHorn.var v]) with
        | some q => (tw q.rhs).bind fun a ↦ if a.sort == Sorts.obj then some a.lo else none
        | none => some (PartialHorn.op o [PartialHorn.var v])
      else none) := by
  mirror_simp [«Infer.inferSide», envAxs_eq]
  cases E.axs[o]? with
  | none => rfl
  | some a =>
    have hc : a.ctx.map leaf = [leaf 1] ↔ a.ctx = [Sorts.arr] :=
      map_leaf_inj (ys := [Sorts.arr])
    mirror_simp [seqCtx_eq, seqHyps_eq, seqConcl_eq, dfd_eq, mirror_x, phOp_eq, phVar_eq,
      encEqn_inj,
      hc, beq_eq_decide, Bool.and_assoc, some_eq, foldr_find, eqLhs_eq, eqRhs_eq]
    cases H.find? (fun y ↦ decide (y.lhs = PartialHorn.op o [PartialHorn.var v])) with
    | none =>
      mirror_simp [none_eq]
      split_ifs <;> rfl
    | some q =>
      mirror_simp [eqRhs_eq, htv q.rhs]
      split_ifs
      · cases tw q.rhs with
        | none => rfl
        | some b =>
          mirror_simp [annSort_eq, annLo_eq, Sorts.obj]
          split_ifs <;> rfl
      · rfl

/-- The typing of an arrow from its optional sides. -/
theorem sides_eq (lo hi : Option Tree) :
    (lo.elim (encOpt none) fun l ↦ encOpt (hi.map fun h ↦ encAnn ⟨1, l, h⟩)) =
      encOpt ((lo.bind fun l ↦ hi.map fun h ↦ (⟨Sorts.arr, l, h⟩ : Ann)).map encAnn) := by
  cases lo <;> cases hi <;> rfl

/-- The mirror's typing of a variable of a context under hypotheses. -/
theorem inferVar_eq {tv : Tree → Tree} {tw : Tree → Option Ann} (htv : TreeRel tv tw)
    (E : ExtEnv) (Γ : List ℕ) (H : List PartialHorn.Eqn) (v : ℕ) :
    «Infer.inferVar» (encExtEnv E) (Γ.map leaf) (H.map encEqn) tv (leaf v) =
      encOpt ((inferVar E Γ H tw v).map encAnn) := by
  mirror_simp [«Infer.inferVar», inferVar]
  rcases Γ[v]? with _ | _ | _ | s
  · rfl
  · mirror_simp [ann_eq, phVar_eq]
    rfl
  · mirror_simp [inferSide_eq htv, ann_eq, zero_add]
    exact sides_eq _ _
  · simp [none_eq, -Nat.add_eq_right]

/-- The trees of a list of trees with their results. -/
@[simp] theorem poTrees_eq (rs : List (Tree × Tree)) :
    «Infer.poTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Infer.poTrees», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The results of a list of trees with their results. -/
@[simp] theorem poValues_eq (rs : List (Tree × Tree)) :
    «Infer.poValues» rs = rs.map Prod.snd :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Infer.poValues», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The traversal of a list by optional images, encoded: the traversal of the list, encoded. -/
theorem mapM_map_option {α β γ : Type} (g : α → Option β) (e : β → γ) :
    ∀ xs : List α, xs.mapM (fun x ↦ (g x).map e) = (xs.mapM g).map (List.map e) :=
  List.rec rfl fun x r ih ↦ by
    rw [List.mapM_cons, List.mapM_cons, ih]
    cases g x <;> cases r.mapM g <;> rfl

/-- A traversal by optional images that succeeds keeps the list's length. -/
theorem mapM_length {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ys.length = xs.length :=
  List.rec (fun ys h ↦ by simp at h; simp [← h]) fun x r ih ys h ↦ by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hr : r.mapM f with
      | none => simp [hx, hr] at h
      | some zs =>
        have h' : b :: zs = ys := by simpa [hx, hr] using h
        rw [← h', List.length_cons, ih zs hr, List.length_cons]

/-- The right fold that pairs each of a list of terms with the typing at its position in a list
of typings of the same length, the typings reversed: the terms paired with their typings. -/
theorem foldr_zip (cs : List Tree) : ∀ (bs : List Ann) (rest : List Tree),
    cs.length = bs.length →
      cs.foldr (fun (c : Tree) (s : List Tree × List Tree) ↦
          («Prelude.tail» s.1,
            «Infer.typed» c («Prelude.at» s.1 (leaf 0)) :: s.2))
        ((bs.map encAnn).reverse ++ rest, []) = (rest, (cs.zip bs).map encTyped) :=
  cs.rec (fun bs rest h ↦ by
      obtain rfl := List.length_eq_zero_iff.mp h.symm
      rfl)
    fun c cs ih bs rest h ↦ by
      obtain ⟨b, bs', rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
      rw [List.foldr_cons, List.map_cons, List.reverse_cons, List.append_assoc,
        ih bs' _ (by simpa using h)]
      simp [tail_eq, at_eq, typed_eq]

/-- The mirror's inference of a pattern instance's typing at typed arguments. -/
theorem patInfer_eq {v : List Tree → Tree → Tree}
    {w : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hvw : PatRel v w) (E : ExtEnv)
    (env : List (Tree × Ann)) (p : Tree) :
    «Infer.patInfer» (encExtEnv E) v (env.map encTyped) p =
      encOpt ((RoseTree.para (patStep E w env) p).map encTyped) := by
  simp only [«Infer.patInfer»]
  apply fold_pair_snd (fun (a : Tree) (b : Option (Tree × Ann)) ↦ a = encOpt (b.map encTyped))
  · intro l rs
    simp
  intro l xs hx
  have hv : (xs.map fun x ↦ (x.1, x.2.1)).map Prod.snd =
      xs.map fun x ↦ encOpt (x.2.2.map encTyped) := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left hx
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;>
      first
      | (by_cases hc : x.1.children = [] <;> simp [patStep, none_eq, List.getElem?_map, hc])
      | simp [patStep, none_eq]
  | succ k =>
    mirror_simp [poTrees_eq, poValues_eq, hv, allSomeT_eq, mapM_map_option, patStep,
      beq_iff_eq, Nat.add_one_ne_zero, Nat.add_sub_cancel, List.mapM_map]
    cases xs.mapM (fun x ↦ x.2.2) with
    | none => rfl
    | some args =>
      mirror_simp [tyTerm_eq, phOp_eq, inferOp_eq hvw, typed_eq]
      cases h : inferOp E w k args <;> simp [h]

/-- The mirror's inference of a term's typing in a context under hypotheses. -/
theorem treeInfer_eq {v : List Tree → Tree → Tree}
    {w : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hvw : PatRel v w)
    {tv : Tree → Tree} {tw : Tree → Option Ann} (htv : TreeRel tv tw) (E : ExtEnv)
    (Γ : List ℕ) (H : List PartialHorn.Eqn) (t : Tree) :
    «Infer.treeInfer» (encExtEnv E) (Γ.map leaf) (H.map encEqn) v tv t =
      encOpt ((RoseTree.para (treeStep E Γ H w tw) t).map encAnn) := by
  simp only [«Infer.treeInfer»]
  apply fold_pair_snd (fun (a : Tree) (b : Option Ann) ↦ a = encOpt (b.map encAnn))
  · intro l rs
    simp
  intro l xs hx
  have hv : (xs.map fun x ↦ (x.1, x.2.1)).map Prod.snd =
      xs.map fun x ↦ encOpt (x.2.2.map encAnn) := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left hx
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;>
      first
      | (by_cases hc : x.1.children = [] <;>
          simp [treeStep, none_eq, hc, inferVar_eq htv E Γ H])
      | simp [treeStep, none_eq]
  | succ k =>
    mirror_simp [poTrees_eq, poValues_eq, hv, allSomeT_eq, mapM_map_option, treeStep,
      beq_iff_eq, Nat.add_one_ne_zero, Nat.add_sub_cancel, List.mapM_map]
    cases hm : xs.mapM (fun x ↦ x.2.2) with
    | none => rfl
    | some as =>
      have hz := foldr_zip (xs.map (·.1)) as [] (by simpa using (mapM_length _ xs as hm).symm)
      rw [List.append_nil] at hz
      mirror_simp [] at hz
      mirror_simp [hz, inferOp_eq hvw, Option.bind_eq_bind]

/-- The mirror's inferences at a fuel, of pattern instances' typings and of terms'. -/
theorem infers_eq (E : ExtEnv) (Γ : List ℕ) (H : List PartialHorn.Eqn) :
    ∀ fuel : ℕ,
      PatRel («Infer.infers» (encExtEnv E) (Γ.map leaf) (H.map encEqn) (leaf fuel)).1
        (infers E Γ H fuel).1 ∧
      TreeRel («Infer.infers» (encExtEnv E) (Γ.map leaf) (H.map encEqn) (leaf fuel)).2
        (infers E Γ H fuel).2 :=
  Nat.rec ⟨fun _ _ ↦ rfl, fun _ ↦ rfl⟩ fun n ih ↦ by
    simp only [«Infer.infers», iter_leaf] at ih ⊢
    rw [Nat.repeat]
    exact ⟨fun env p ↦ patInfer_eq ih.1 E env p, fun t ↦ treeInfer_eq ih.1 ih.2 E Γ H t⟩

end GebTests.Prototypes.FreeTopos.Agreement.Infer

end
