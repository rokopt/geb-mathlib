/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic.ProofHoles
public import GebTests.Prototypes.FreeTopos.Agreement.Conversion
public import GebTests.Prototypes.FreeTopos.Agreement.Tactics
public import Geb.Prototypes.FreeTopos.Internal.Holes.Closed

set_option doc.verso true in
/-!
# Agreement of the Geb proof-hole checker

The encoding preserves the finite premises of each conversion rule. Hole identities may be
arbitrary trees. The conversion checker's agreement applies to rules whose data can be
serialized, including normalization and machine steps with unprepared rewrite rules.

## Main statements

* {lit}`holes_eq` — the occurrence list retains premise order and multiplicity.
* {lit}`checks_eq` — the two checkers accept the same encoded sketches.
* {lit}`conditional_eq` — the fully closed theorem has the Lean checker's statement.

## Tags

proof sketch, conversion, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.ProofHoles

open Geb Geb.Kernel Geb.FreeTopos Geb.FreeTopos.Internal GebMirror.Metalogic
open Encode Base Language Derivation Provers Conversion
open Geb.FreeTopos.Internal.ProofHoles
open scoped FinEnum

variable {α : Type}

/-- Encode a sketch with the specified encoding of hole identities. -/
def encSketch (e : α → Tree) : Sketch α → Tree :=
  PFunctor.FreeM.rec (fun h ↦ RoseTree.node 42 [e h]) fun r _ cs ↦
    RoseTree.node (convData r.1).1 (RoseTree.node 0 (convData r.1).2 :: List.ofFn cs)

private theorem tag_lt (r : ConvRule) : (convData r).1 < 42 := by
  cases r with
  | base r => exact (ruleData_lt r).trans (by decide)
  | _ => simp [convData]

private def ruleTree (r : ConvRule) (cs : List Tree) : Tree :=
  RoseTree.node (convData r).1 (RoseTree.node 0 (convData r).2 :: cs)

private def sketchFold {β : Type} (h : Tree → β) (f : Tree → List β → β) : Tree → β :=
  Const.para fun x cs ↦ if (Const.eq (Const.label x) (leaf 42)).label ≠ 0
    then h (Const.child x (leaf 0)) else f x (Const.lcase cs [] fun _ tail ↦ tail)

private theorem fold_pure {β : Type} (h : Tree → β) (f : Tree → List β → β) (t : Tree) :
    sketchFold h f (RoseTree.node 42 [t]) = h t := by
  rw [sketchFold, Const.para_node]
  rfl

private theorem fold_rule {β : Type} (h : Tree → β) (f : Tree → List β → β)
    (r : ConvRule) (cs : List Tree) :
    sketchFold h f (ruleTree r cs) = f (ruleTree r cs) (cs.map (sketchFold h f)) := by
  unfold ruleTree sketchFold
  rw [Const.para_node]
  have hn := (tag_lt r).ne
  simp only [label_eq, RoseTree.label_node, eq_leaf, label_ne_zero, ofBool_bne,
    beq_iff_eq, hn, ↓reduceIte, List.map_cons, Const.lcase]

/-- The emitted checker collects exactly the declared occurrences of the sketch. -/
theorem holes_eq (e : α → Tree) (d : Sketch α) :
    «ProofHoles.holes» (encSketch e d) = (holes d).map e := by
  let collect := fun (_ : Tree) (cs : List (List Tree)) ↦
    Const.foldr «Prelude.append» ([] : List Tree) cs
  change sketchFold «Prelude.single» collect (encSketch e d) = _
  refine PFunctor.FreeM.rec (motive := fun d : Sketch α ↦
    sketchFold «Prelude.single» collect (encSketch e d) = (holes d).map e)
    (fun _ ↦ fold_pure _ _ _) ?_ d
  · intro r cs ih
    rcases r with ⟨r, k⟩
    change Fin k → Sketch α at cs
    change sketchFold _ _ (ruleTree r (List.ofFn fun i ↦ encSketch e (cs i))) =
      ((List.ofFn fun i ↦ holes (cs i)).flatten.map e)
    rw [fold_rule, List.map_ofFn]
    change (List.ofFn fun i ↦ sketchFold _ collect (encSketch e (cs i))).foldr
      «Prelude.append» [] = _
    change ∀ i : Fin k, _ at ih
    rw [show (fun i : Fin k ↦ sketchFold «Prelude.single» collect (encSketch e (cs i))) = _
      from funext ih]
    simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
    generalize List.ofFn _ = xs
    refine xs.rec rfl (fun x xs ih ↦ ?_)
    simp only [List.foldr_cons, append_eq, List.flatten_cons, ih]

/-- Well-formedness checks the object context and every formula in its own context. -/
theorem wellFormed_eq (G : Globals) (a : Thm) :
    «ProofHoles.wellFormed» (encGlobals G) (encThm a) = ofBool (a.wellFormed G) := by
  have ha := allT_map («Derivation.isFormula» (encGlobals G) (leaf a.arity) a.ctx) encTerm
    (fun ψ ↦ decide (typeIn G a.arity a.ctx ψ = some omega)) a.hyps
    fun ψ _ ↦ isFormula_eq G a.arity a.ctx ψ
  mirror_simp [«ProofHoles.wellFormed», Thm.wellFormed, thArity_eq, thCtx_eq,
    thHyps_eq, thConcl_eq, allT_isTy, ha, isFormula_eq, Bool.decide_and, Bool.and_assoc]

/-- Encodable conversion rules throughout a sketch. -/
def PlainSketch : Sketch α → Prop :=
  PFunctor.FreeM.rec (fun _ ↦ True) fun r _ cs ↦ RulePlain r.1 ∧ ∀ i, cs i

private def liftChecks (w : Checks) : FastChecks :=
  (fun Γ k Φ t ↦ w.1 Γ (Φ.map (weakenBy k)) t, w.2)

private theorem lift_checks (w : Checks) : (liftChecks w).checks = w := by
  simp only [liftChecks, FastChecks.checks, map_weakenBy_zero]

private theorem uniform_lift (w : Checks) : (liftChecks w).1.Uniform := by
  intro Γ k Φ t
  simp only [liftChecks, map_weakenBy_zero]

private theorem eq_lift (w : FastChecks) (h : w.1.Uniform) : w = liftChecks w.checks :=
  Prod.ext (funext fun Γ ↦ funext fun k ↦ funext fun Φ ↦ funext fun t ↦ h Γ k Φ t) rfl

private theorem hole_rel (G : Globals) (n : ℕ) (a : Thm) :
    FRel («ProofHoles.holeChecks» (encGlobals G) (leaf n) (encThm a))
      (liftChecks (holeChecks G n a)) := by
  refine ⟨fun _ _ _ _ ↦ rfl, fun Γ Φ φ ↦ ?_⟩
  change «Prelude.and» («ProofHoles.wellFormed» _ _) (Const.equal (encThm a)
    (encThm ⟨n, Γ, Φ, φ⟩)) = _
  simp only [wellFormed_eq, equal_eq, and_eq, Literals.encThm_eq_iff, liftChecks, holeChecks]

variable (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ)
variable (e : α → Tree) (g : α → Thm) (decl : Tree → Tree) (hg : ∀ h, decl (e h) = encThm (g h))

private theorem root_eq (d : Sketch α) :
    «ProofHoles.rootRule» (encSketch e d) =
      encConv (RoseTree.node (run G E R n g d).1 []) := by
  cases d with
  | pure h => rfl
  | liftBind r cs =>
    change «ProofHoles.rootRule» (ruleTree r.1 _) = encConv (RoseTree.node r.1 [])
    have hn := (tag_lt r.1).ne
    simp only [«ProofHoles.rootRule», ruleTree, «ProofHoles.holeTag», label_eq,
      RoseTree.label_node, eq_leaf, label_ne_zero, ofBool_bne, beq_iff_eq, hn, ↓reduceIte,
      single_eq, node_leaf, child_node, List.getD_cons_zero, encConv_node, List.map_nil]

private def mirrorRun (d : Sketch α) :=
  «ProofHoles.run» (encGlobals G) (E.toList.map encEntry) (R.map leaf) (leaf n) decl (encSketch e d)

include hg in
private theorem run_eq (d : Sketch α) (hd : PlainSketch d) :
    FRel (mirrorRun G E R n e decl d) (liftChecks (run G E R n g d).2) := by
  let hcase := fun t ↦ «ProofHoles.holeChecks» (encGlobals G) (leaf n) (decl t)
  let dummy : DV := fun _ _ _ _ _ ↦ leaf 0
  let rule := fun (nd : Tree) (cs : List DV) ↦ «Conversion.convStep» (encGlobals G)
    (E.toList.map encEntry) (R.map leaf) (leaf n)
    (Const.node (Const.label nd) (Const.child nd (leaf 0) ::
      «Base.mapT» «ProofHoles.rootRule» («Prelude.tail» (Const.children nd)))) (dummy :: cs)
  change FRel (sketchFold hcase rule (encSketch e d)) _
  refine PFunctor.FreeM.rec (motive := fun d : Sketch α ↦ PlainSketch d →
    FRel (sketchFold hcase rule (encSketch e d)) (liftChecks (run G E R n g d).2)) ?_ ?_ d hd
  · intro h _
    rw [show encSketch e (.pure h) = RoseTree.node 42 [e h] from rfl, fold_pure]
    change FRel («ProofHoles.holeChecks» _ _ (decl (e h))) (liftChecks (holeChecks G n (g h)))
    rw [hg]
    exact hole_rel G n (g h)
  · intro r cs ih hd
    rcases r with ⟨r, k⟩
    change Fin k → Sketch α at cs
    obtain ⟨hr, hc⟩ := hd
    let xs := List.ofFn fun i ↦
      (RoseTree.node (run G E R n g (cs i)).1 [], sketchFold hcase rule (encSketch e (cs i)),
        liftChecks (run G E R n g (cs i)).2)
    have hstep := convStep_eq G E R n r hr dummy xs fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact ih i (hc i)
    have hfast := convFastStep_eq G E R n r (xs.map fun x ↦ (x.1, x.2.2)) fun x hx ↦ by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact uniform_lift _
    rw [eq_lift _ hfast.1, hfast.2] at hstep
    change FRel (sketchFold _ _ (ruleTree r (List.ofFn fun i ↦ encSketch e (cs i)))) _
    rw [fold_rule]
    simp only [rule, ruleTree, label_eq, RoseTree.label_node, node_leaf, child_node,
      List.getD_cons_zero, children_eq, RoseTree.children_node, tail_eq, List.tail_cons,
      mapT_eq, List.map_ofFn, Function.comp_def, root_eq G E R n e g]
    change FRel _ (liftChecks (convStep G E R n r (List.ofFn fun i ↦
      (RoseTree.node (run G E R n g (cs i)).1 [], (run G E R n g (cs i)).2))))
    simp only [xs, List.map_ofFn, Function.comp_def, lift_checks] at hstep
    rw [encConv_node] at hstep
    simp only [List.map_ofFn, Function.comp_def] at hstep
    simpa only [rule, label_eq, node_leaf, children_eq, tail_eq, mapT_eq] using hstep

private theorem shaped_eq (d : Sketch α) : «ProofHoles.shaped» (encSketch e d) = ofBool true := by
  refine PFunctor.FreeM.rec (motive := fun d : Sketch α ↦
    «ProofHoles.shaped» (encSketch e d) = ofBool true) (fun _ ↦ rfl) ?_ d
  · intro r cs ih
    rcases r with ⟨r, k⟩
    change Fin k → Sketch α at cs
    change ∀ i : Fin k, _ at ih
    change «ProofHoles.shaped» (ruleTree r (List.ofFn fun i ↦ encSketch e (cs i))) = _
    unfold «ProofHoles.shaped» ruleTree
    rw [Const.para_node]
    have ht := tag_lt r
    have ha := allT_map id (fun i : Fin k ↦ «ProofHoles.shaped» (encSketch e (cs i)))
      (fun _ ↦ true) (List.finRange k) (fun i _ ↦ ih i)
    rw [← List.ofFn_eq_map, show (List.finRange k).all (fun _ ↦ true) = true from
      List.all_eq_true.mpr (fun _ _ ↦ rfl)] at ha
    change «Base.allT» (fun x ↦ x) (List.ofFn fun i ↦ «ProofHoles.shaped» (encSketch e (cs i))) = _
      at ha
    mirror_simp [«ProofHoles.holeTag», ht, beq_iff_eq, ht.ne, Nat.zero_lt_succ,
      List.map_ofFn, decide_true, ofBool_true]
    unfold «ProofHoles.shaped» at ha
    mirror_simp [«ProofHoles.holeTag», beq_iff_eq, ofBool_true] at ha
    rw [ha]
    rfl

include hg in
/-- The Geb checker and the Lean checker accept the same encoded proof sketches. -/
theorem checks_eq (a : Thm) (d : Sketch α) (hd : PlainSketch d) :
    «ProofHoles.checks» (encGlobals G) (E.toList.map encEntry) (R.map leaf) decl
      (encThm a) (encSketch e d) = ofBool (checks G E R g a d) := by
  have hr := (run_eq G E R a.arity e g decl hg d hd).2 a.ctx a.hyps a.concl
  have ha := allT_map (fun h ↦ «ProofHoles.wellFormed» (encGlobals G) (decl h)) e
    (fun h ↦ (g h).wellFormed G) (holes d) fun h _ ↦ (hg h) ▸ wellFormed_eq G (g h)
  simp only [mirrorRun, liftChecks] at hr
  simp only [«ProofHoles.checks», checks, shaped_eq, wellFormed_eq, holes_eq, ha, thArity_eq,
    thCtx_eq, thHyps_eq, thConcl_eq, hr, and_eq, Bool.true_and, Bool.and_assoc]

include hg in
/-- The emitted report agrees on rejection, the order of holes and their complete sequents. -/
theorem checkSketch_eq (a : Thm) (d : Sketch α) (hd : PlainSketch d) :
    «ProofHoles.checkSketch» (encGlobals G) (E.toList.map encEntry) (R.map leaf) decl
      (encThm a) (encSketch e d) = encOpt ((check G E R g a d).map fun hs ↦
        RoseTree.node 0 (hs.map fun (h, b) ↦ encPair (e h, encThm b))) := by
  simp only [«ProofHoles.checkSketch», checks_eq G E R e g decl hg a d hd, label_ne_zero,
    ofBool_bne, Geb.FreeTopos.Internal.ProofHoles.check, holes_eq, mapT_eq, List.map_map,
    Function.comp_def, hg, single_eq, node_leaf]
  split <;> simp only [Option.map_some, Option.map_none, List.map_map, Function.comp_def] <;> rfl

private theorem implications (o : ℕ) (hs : List Term) (p : Term) :
    (hs.map encTerm).foldr («Tactics.impL» (leaf o)) (encTerm p) =
      encTerm (hs.foldr (Logic.imp o) p) := by
  refine hs.rec rfl (fun x xs ih ↦ ?_)
  simp only [List.map_cons, List.foldr_cons, ih, Tactics.impL_eq]

/-- Closing a sequent quantifies its variables and discharges its hypotheses in the same order. -/
theorem condition_eq (o : ℕ) (a : Thm) :
    «HoleConditions.condition» (leaf o) (encThm a) = encTerm (condition o a) := by
  simp only [«HoleConditions.condition», condition, thCtx_eq, thHyps_eq, thConcl_eq,
    foldr_eq, implications, reverse_eq, List.foldr_reverse, single_eq, add_leaf]
  generalize a.hyps.foldr (Logic.imp o) a.concl = p
  generalize a.ctx = xs
  revert p
  refine xs.rec (fun _ ↦ rfl) (fun x xs ih p ↦ ?_)
  simp only [List.foldl_cons, mLam_eq]
  change List.foldl _ (encTerm (Logic.all o x (Term.lam x p))) xs = _
  exact ih _

include hg in
/-- The Geb translator targets precisely the universally closed conditional theorem. -/
theorem conditional_eq (o : ℕ) (a : Thm) (d : Sketch α) :
    «HoleConditions.conditional» (leaf o) decl (encThm a) (encSketch e d) =
      encThm (Closed.conditional o g a d) := by
  simp only [«HoleConditions.conditional», «HoleConditions.theoremAt», thArity_eq,
    condition_eq, foldr_eq, holes_eq, mapT_eq, List.map_map, Function.comp_def, hg]
  rw [show (fun h ↦ encTerm (condition o (g h))) = encTerm ∘ (fun h ↦ condition o (g h)) from rfl,
    ← List.map_map, implications]
  rfl

/-- Every returned certificate, including on raw tree inputs, passed the underlying Geb
conversion checker at the conditional theorem in the original environment. -/
theorem replays_of_certify (G : Tree) (E R : List Tree) (o j : Tree) (decl : Tree → Tree)
    (a d c : Tree) (h : «HoleCertificates.certify» G E R o j decl a d = encOpt (some c)) :
    («Conversion.thmConvChecks» G E R («HoleConditions.conditional» o decl a d) c).label ≠ 0 := by
  have hn : ∀ t : Tree, «Prelude.none» ≠ encOpt (some t) :=
    fun _ he ↦ Nat.zero_ne_one (congrArg RoseTree.label he)
  unfold «HoleCertificates.certify» at h
  split at h
  · unfold «Base.bindO» at h
    split at h
    · dsimp only at h
      split at h
      · have he := congrArg (fun x ↦ Const.child x (leaf 0)) h
        change _ = c at he
        exact he ▸ ‹_ ≠ 0›
      · exact (hn c h).elim
    · exact (hn c h).elim
  · exact (hn c h).elim

include hg in
/-- A plain certificate returned by the Geb translator proves the Lean conditional theorem. -/
theorem convChecks_of_certify (o j : ℕ) (a : Thm) (d : Sketch α) (c : ConvDeriv)
    (hc : Plain c) (h : «HoleCertificates.certify» (encGlobals G) (E.toList.map encEntry)
      (R.map leaf) (leaf o) (leaf j) decl (encThm a) (encSketch e d) = encOpt (some (encConv c))) :
    (Closed.conditional o g a d).convChecks G E R c = true := by
  have hr := replays_of_certify _ _ _ _ _ _ _ _ _ h
  simpa only [conditional_eq e g decl hg, thmConvChecks_eq G E R _ c hc, label_ne_zero,
    ofBool_bne] using hr

end GebTests.Prototypes.FreeTopos.Agreement.ProofHoles

end
