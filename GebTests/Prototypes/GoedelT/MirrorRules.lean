/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorDelta

set_option doc.verso true in
/-!
# The rules of Gödel's T written in Geb

The checker of Gödel's T written in Geb dispatches on a certificate node's label and number of
children to one of its rules. For each rule of {name}`Geb.GoedelT.checkCore` and
{name}`Geb.GoedelT.checkMore`, a lemma states that the mirror's branch, at a node of that label
over children whose checkers agree with the kernel's ({lit}`Agrees`), gives the encoding of the
kernel's conclusion. The macro {lit}`rule_dispatch` selects the branch, evaluating the mirror's
chain of tests of label and arity one test at a time without simplifying the branches it
discards; {lit}`rule_close` compares the two sides once each is stated through the same
conditions.

## Main definitions

* {lit}`Agrees` — a checker written in Geb agrees with a checker in Lean at encoded hypotheses.

## Tags

certificate, rule, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.GoedelT

namespace GebTests.Prototypes.GoedelT.MirrorRules

open Geb Geb.Kernel Geb.GoedelT GebTests.Prototypes.GoedelT.MirrorTyping
  GebTests.Prototypes.GoedelT.MirrorTerms GebTests.Prototypes.GoedelT.MirrorEquations
  GebTests.Prototypes.GoedelT.MirrorDelta
open scoped FinEnum

/-- A checker written in Geb, a function of the context and the list of hypotheses, agrees with a
checker in Lean in an environment: at encoded hypotheses it gives the encoded conclusion. -/
def Agrees (E : Env) (G : List Glob) (p : List Tree → List Tree → Tree) (P : Chk) : Prop :=
  ∀ Γ H, p Γ (H.map encEqn) = enc ((P E G Γ H).map encEqn)

/-- The mirror's checker of a premise by position, nothing when out of range. -/
theorem prem_eq (ps : List (Tree × (List Tree → List Tree → Tree))) (i : ℕ) :
    «Equations.prem» ps (leaf i) = (ps[i]?.map (·.2)).getD fun _ _ ↦ enc none := by
  have hdrop : ∀ i : ℕ, Nat.repeat «Equations/CRs.tail» i ps = ps.drop i :=
    Nat.rec rfl fun i ih ↦ by
      rw [Nat.repeat, ih, ← List.tail_drop]
      cases ps.drop i <;> rfl
  simp only [«Equations.prem», Const.iter, label_leaf, hdrop, Const.lcase]
  cases h : ps.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    simp [List.getElem?_eq_none h, none_eq]
  | cons r _ =>
    have : ps[i]? = some r := by
      rw [← List.head?_drop, h]
      rfl
    simp [this]

/-- The mirror's test of a certificate node's label and number of children. -/
theorem shape_label (a b c d : ℕ) :
    («Equations.shape» (leaf a) (leaf b) (leaf c) (leaf d)).label ≠ 0 ↔ a = c ∧ b = d := by
  simp only [«Equations.shape», and_label, eq_leaf]

/-- The mirror's element of an encoded list of hypotheses by position. -/
theorem nth_hyps (H : List Eqn) (i : Tree) :
    «Prelude.nth» (H.map encEqn) (Const.label i) = enc (H[i.label]?.map encEqn) := by
  rw [Const.label, nth_eq, List.getElem?_map]

/-- Selects the branch of the mirror's rules, and of the kernel's, at a certificate node of a
known label and known children. -/
macro (name := ruleDispatch) "rule_dispatch" : tactic => `(tactic|
  simp (config := { decide := true }) only [«Equations.checkCore»,
    «Equations.checkMore», ↓reduceIte, shape_label, and_label, eq_leaf, lt_leaf,
    length_eq, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, at_eq,
    List.getD_cons_zero, List.getD_cons_succ, prem_eq, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.map_some, Option.getD_some, false_and, true_and, and_false,
    and_true, Nat.zero_lt_succ, Nat.reduceEqDiff, checkCore, checkMore])

/-- Closes a rule's agreement once both sides are stated through the same conditions. -/
macro (name := ruleClose) "rule_close" : tactic => `(tactic|
  (split_ifs <;> (try simp only [Option.bind_some, Option.bind_none, Option.map_some,
    Option.map_none, ↓reduceIte, *]) <;> rfl))

/-- The mirror's type of a term in a context. -/
theorem typeIn_typeOf (G : List Glob) (Γ : Ctx) (t : Tree) :
    «Check.typeIn» (G.map (·.1)) Γ t = enc (typeOf G Γ t) :=
  typeIn_eq G Γ t

/-- The mirror's test of a type. -/
theorem isTy_label (A : Tree) : («Check.isTy» A).label ≠ 0 ↔ Ty.IsTy A = true := by
  rw [isTy_eq, ofBool_label]

/-- A node is the kernel's node of two children of its label exactly when it has two
children. -/
theorem node_eq_node2 (l l' : ℕ) (A B : Tree) :
    RoseTree.node l [A, B] = node2 l' A B ↔ l = l' := by
  rw [node2_eq]
  exact ⟨fun h ↦ by simpa using congrArg RoseTree.label h, fun h ↦ h ▸ rfl⟩

/-- The parts of a node of two children of a label, the mirror's test of that label and arity
deciding it. -/
theorem parts_mirror (F : Tree) (k : ℕ) :
    (match F.children with
      | [A, B] => if F = node2 k A B then some (A, B) else none
      | _ => none) =
    if («Prelude.and» (Const.eq (Const.label F) (leaf k))
        (Const.eq (Const.arity F) (leaf 2))).label ≠ 0 then
      some (Const.child F (leaf 0), Const.child F (leaf 1))
    else none := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, F = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children F).symm⟩
  simp only [RoseTree.children_node, and_label, label_node, arity_node, eq_leaf]
  rcases cs with _ | ⟨A, _ | ⟨B, _ | ⟨C, rest⟩⟩⟩
  · simp
  · simp
  · simp only [node_eq_node2, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
      and_true, child_node, List.getD_cons_zero, List.getD_cons_succ]
  · simp

/-- The parts of a function type, the mirror's test deciding it. -/
theorem arrowParts_mirror (F : Tree) :
    arrowParts F = if («Check.isArrow» F).label ≠ 0 then
      some (Const.child F (leaf 0), Const.child F (leaf 1)) else none :=
  parts_mirror F Label.tyArrow

/-- The parts of a product type, the mirror's test deciding it. -/
theorem prodParts_mirror (P : Tree) :
    prodParts P = if («Check.isProd» P).label ≠ 0 then
      some (Const.child P (leaf 0), Const.child P (leaf 1)) else none :=
  parts_mirror P Label.tyProd

/-- The mirror's rule of a hypothesis by index. -/
theorem core_hyp (E : Env) (G : List Glob) (i : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 0) [i] [(i, p)] Γ (H.map encEqn) =
      enc ((checkCore 0 [(i, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [nth_hyps]
  cases H[i.label]? with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.bind_some, bindO_some, typedIn_label]
    rule_close

/-- The mirror's rule of reflexivity. -/
theorem core_refl (E : Env) (G : List Glob) (t : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 1) [t] [(t, p)] Γ (H.map encEqn) =
      enc ((checkCore 1 [(t, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf]
  cases typeOf G Γ t <;> rfl

/-- The mirror's rule of symmetry. -/
theorem core_symm (E : Env) (G : List Glob) (a : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 2) [a] [(a, p)] Γ (H.map encEqn) =
      enc ((checkCore 2 [(a, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q => simp only [Option.map_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq]; rfl

/-- The mirror's rule of transitivity. -/
theorem core_trans (E : Env) (G : List Glob) (a b : Tree) (p p' : List Tree → List Tree → Tree)
    (P P' : Chk) (hp : Agrees E G p P) (hp' : Agrees E G p' P') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 3) [a, b] [(a, p), (b, p')] Γ
      (H.map encEqn) = enc ((checkCore 3 [(a, P), (b, P')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H, hp' Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    cases P' E G Γ H with
    | none => rfl
    | some q' =>
      simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
        equal_label]
      rule_close

/-- The mirror's rule of congruence of application. -/
theorem core_congApp (E : Env) (G : List Glob) (a b : Tree) (p p' : List Tree → List Tree → Tree)
    (P P' : Chk) (hp : Agrees E G p P) (hp' : Agrees E G p' P') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 4) [a, b] [(a, p), (b, p')] Γ
      (H.map encEqn) = enc ((checkCore 4 [(a, P), (b, P')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H, hp' Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    cases P' E G Γ H with
    | none => rfl
    | some q' =>
      simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
        equal_label, arrowParts_mirror]
      rule_close

/-- The mirror's rule of congruence of abstraction. -/
theorem core_congLam (E : Env) (G : List Glob) (A b : Tree) (pA p : List Tree → List Tree → Tree)
    (PA P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 5) [A, b] [(A, pA), (b, p)] Γ
      (H.map encEqn) = enc ((checkCore 5 [(A, PA), (b, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [mapT_eqWk, hp]
  simp only [isTy_label]
  cases P E G (A :: Γ) (H.map (Eqn.wk 1)) with
  | none => rule_close
  | some q =>
    simp only [Option.map_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq, tyArrow_eq]
    rule_close

/-- The mirror's rule of congruence of pairs. -/
theorem core_congPair (E : Env) (G : List Glob) (a b : Tree)
    (p p' : List Tree → List Tree → Tree) (P P' : Chk) (hp : Agrees E G p P)
    (hp' : Agrees E G p' P') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 6) [a, b] [(a, p), (b, p')] Γ
      (H.map encEqn) = enc ((checkCore 6 [(a, P), (b, P')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H, hp' Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    cases P' E G Γ H with
    | none => rfl
    | some q' =>
      simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
        tProd, node2_eq]
      rfl

/-- The mirror's rule of congruence of the first projection. -/
theorem core_congFst (E : Env) (G : List Glob) (a : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 7) [a] [(a, p)] Γ (H.map encEqn) =
      enc ((checkCore 7 [(a, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
      prodParts_mirror]
    rule_close

/-- The mirror's rule of congruence of the second projection. -/
theorem core_congSnd (E : Env) (G : List Glob) (a : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 8) [a] [(a, p)] Γ (H.map encEqn) =
      enc ((checkCore 8 [(a, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
      prodParts_mirror]
    rule_close

/-- The mirror's rule of congruence of lists. -/
theorem core_congCons (E : Env) (G : List Glob) (a b : Tree)
    (p p' : List Tree → List Tree → Tree) (P P' : Chk) (hp : Agrees E G p P)
    (hp' : Agrees E G p' P') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 9) [a, b] [(a, p), (b, p')] Γ
      (H.map encEqn) = enc ((checkCore 9 [(a, P), (b, P')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H, hp' Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    cases P' E G Γ H with
    | none => rfl
    | some q' =>
      simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
        equal_label, tyList_eq]
      rule_close

/-- The mirror's rule of congruence of the conditional. -/
theorem core_congCond (E : Env) (G : List Glob) (a b c : Tree)
    (p p' p'' : List Tree → List Tree → Tree) (P P' P'' : Chk) (hp : Agrees E G p P)
    (hp' : Agrees E G p' P') (hp'' : Agrees E G p'' P'') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 10) [a, b, c]
      [(a, p), (b, p'), (c, p'')] Γ (H.map encEqn) =
      enc ((checkCore 10 [(a, P), (b, P'), (c, P'')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H, hp' Γ H, hp'' Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    cases P' E G Γ H with
    | none => rfl
    | some q' =>
      cases P'' E G Γ H with
      | none => rfl
      | some q'' =>
        simp only [Option.map_some, Option.bind_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq,
          equal_label, show leaf 0 = tT from rfl]
        rule_close

/-- The mirror's rule of β-reduction. -/
theorem core_beta (E : Env) (G : List Glob) (A b a : Tree) (pA pb pa : List Tree → List Tree → Tree)
    (PA Pb Pa : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 11) [A, b, a]
      [(A, pA), (b, pb), (a, pa)] Γ (H.map encEqn) =
      enc ((checkCore 11 [(A, PA), (b, Pb), (a, Pa)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, typeIn_typeOf]
  cases typeOf G (A :: Γ) b with
  | none => rule_close
  | some B =>
    simp only [Option.map_some, bindO_some, subst_eq]
    rule_close

/-- The mirror's rule of η-expansion. -/
theorem core_eta (E : Env) (G : List Glob) (f : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 12) [f] [(f, p)] Γ (H.map encEqn) =
      enc ((checkCore 12 [(f, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf]
  cases typeOf G Γ f with
  | none => rfl
  | some F =>
    simp only [Option.bind_some, bindO_some, arrowParts_mirror, isTy_label, wk_eq, var_eq]
    rule_close

/-- The mirror's rule of the first projection of a pair. -/
theorem core_betaFst (E : Env) (G : List Glob) (a b : Tree) (pa pb : List Tree → List Tree → Tree)
    (Pa Pb : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 13) [a, b] [(a, pa), (b, pb)] Γ
      (H.map encEqn) = enc ((checkCore 13 [(a, Pa), (b, Pb)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf, typeIn_typeOf]
  cases typeOf G Γ a with
  | none => rfl
  | some A => cases typeOf G Γ b <;> rfl

/-- The mirror's rule of the second projection of a pair. -/
theorem core_betaSnd (E : Env) (G : List Glob) (a b : Tree) (pa pb : List Tree → List Tree → Tree)
    (Pa Pb : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 14) [a, b] [(a, pa), (b, pb)] Γ
      (H.map encEqn) = enc ((checkCore 14 [(a, Pa), (b, Pb)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf, typeIn_typeOf]
  cases typeOf G Γ a with
  | none => rfl
  | some A => cases typeOf G Γ b <;> rfl

/-- The mirror's rule of η-expansion of pairs. -/
theorem core_etaPair (E : Env) (G : List Glob) (t : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 15) [t] [(t, p)] Γ (H.map encEqn) =
      enc ((checkCore 15 [(t, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf]
  cases typeOf G Γ t with
  | none => rfl
  | some T =>
    simp only [Option.bind_some, bindO_some, prodParts_mirror]
    rule_close

/-- The mirror's rule of η-expansion of the unit type. -/
theorem core_etaUnit (E : Env) (G : List Glob) (t : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 16) [t] [(t, p)] Γ (H.map encEqn) =
      enc ((checkCore 16 [(t, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_label, show leaf 1 = tUnit from rfl]
  rule_close

/-- The mirror's rule of weakening by the innermost variable. -/
theorem core_weaken (E : Env) (G : List Glob) (a : Tree) (p : List Tree → List Tree → Tree)
    (P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 18) [a] [(a, p)] Γ (H.map encEqn) =
      enc ((checkCore 18 [(a, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  cases Γ with
  | nil => rfl
  | cons A Γ' =>
    have h := hp Γ' []
    rw [List.map_nil] at h
    simp only [Const.lcase, h]
    cases P E G Γ' [] with
    | none => rfl
    | some q => simp only [Option.map_some, bindO_some, eqWk_eq]; rfl

/-- The mirror's rule of cut. -/
theorem core_cut (E : Env) (G : List Glob) (a b : Tree) (p p' : List Tree → List Tree → Tree)
    (P P' : Chk) (hp : Agrees E G p P) (hp' : Agrees E G p' P') (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 19) [a, b] [(a, p), (b, p')] Γ
      (H.map encEqn) = enc ((checkCore 19 [(a, P), (b, P')] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [hp Γ H]
  cases P E G Γ H with
  | none => rfl
  | some q =>
    simp only [Option.map_some, Option.bind_some, bindO_some]
    rw [← List.map_cons, hp']

/-- The mirror's rule of instantiation of the innermost variable. -/
theorem core_instVar (E : Env) (G : List Glob) (u b : Tree) (pu p : List Tree → List Tree → Tree)
    (Pu P : Chk) (hp : Agrees E G p P) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 20) [u, b] [(u, pu), (b, p)] Γ
      (H.map encEqn) = enc ((checkCore 20 [(u, Pu), (b, P)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf]
  cases typeOf G Γ u with
  | none => rfl
  | some A =>
    simp only [Option.bind_some, bindO_some, mapT_eqWk]
    rw [hp]
    cases P E G (A :: Γ) (H.map (Eqn.wk 1)) with
    | none => rfl
    | some q => simp only [Option.map_some, bindO_some, eqTy_eq, eqLhs_eq, eqRhs_eq, subst_eq]; rfl

/-- The mirror's rule of the right fold at the empty list. -/
theorem core_foldrNil (E : Env) (G : List Glob) (A B g z : Tree)
    (pA pB pg pz : List Tree → List Tree → Tree) (PA PB Pg Pz : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 21) [A, B, g, z]
      [(A, pA), (B, pB), (g, pg), (z, pz)] Γ (H.map encEqn) =
      enc ((checkCore 21 [(A, PA), (B, PB), (g, Pg), (z, Pz)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, tyArrow_eq]
  rule_close

/-- The mirror's rule of the right fold at a list of a head and a tail. -/
theorem core_foldrCons (E : Env) (G : List Glob) (A B g z x xs : Tree)
    (pA pB pg pz px pxs : List Tree → List Tree → Tree) (PA PB Pg Pz Px Pxs : Chk) (Γ : Ctx)
    (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 22) [A, B, g, z, x, xs]
      [(A, pA), (B, pB), (g, pg), (z, pz), (x, px), (xs, pxs)] Γ (H.map encEqn) =
      enc ((checkCore 22 [(A, PA), (B, PB), (g, Pg), (z, Pz), (x, Px), (xs, Pxs)] E G Γ
        H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, tyArrow_eq, tyList_eq]
  rule_close

/-- The mirror's list literal. -/
theorem listLit_eq (xs : List Tree) : «Equations.listLit» xs = listLit xs := rfl

/-- The element type of a list type, the mirror's test deciding it. -/
theorem listParts_mirror (L : Tree) :
    listParts L = if («Check.isListTy» L).label ≠ 0 then
      some (Const.child L (leaf 0)) else none := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, L = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children L).symm⟩
  simp only [listParts, «Check.isListTy», RoseTree.children_node, and_label,
    label_node, arity_node, eq_leaf]
  rcases cs with _ | ⟨A, _ | ⟨B, rest⟩⟩
  · have h : ¬(l = 4 ∧ ([] : List Tree).length = 1) := fun h ↦ absurd h.2 (by decide)
    simp only [h, ↓reduceIte]
  · have : RoseTree.node l [A] = tList A ↔ l = Label.tyList := by
      rw [tList_eq]
      refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
      have := congrArg RoseTree.label h
      rwa [RoseTree.label_node, RoseTree.label_node] at this
    simp only [this, List.length_cons, List.length_nil, Nat.zero_add, and_true, child_node,
      List.getD_cons_zero]
  · have h : ¬(l = 4 ∧ (A :: B :: rest).length = 1) := fun h ↦
      absurd h.2 (by simp only [List.length_cons]; omega)
    simp only [h, ↓reduceIte]

/-- The mirror's comparison of an encoded optional equation with a present one. -/
theorem equal_enc (o : Option Eqn) (q : Eqn) :
    (Const.equal (enc (o.map encEqn)) («Prelude.some» (encEqn q))).label ≠ 0 ↔
      o = some q := by
  rw [equal_label, some_eq, show enc (some (encEqn q)) = enc ((some q).map encEqn) from rfl,
    enc_map_inj]

/-- The mirror's node of one child. -/
theorem mk1_eq (l : ℕ) (t : Tree) : «Equations.mk1» (leaf l) t = mk l [t] := rfl

/-- The mirror's node of two children. -/
theorem node2_mk (l : ℕ) (a b : Tree) : «Reader.node2» (leaf l) a b = mk l [a, b] := rfl

/-- The mirror's comparison with the type of trees. -/
theorem equal_tT (A : Tree) : (Const.equal A (leaf 0)).label ≠ 0 ↔ A = tT := equal_label A tT

/-- The mirror's comparison with the type of lists of trees. -/
theorem equal_tLT (A : Tree) :
    (Const.equal A («Check.tyList» (leaf 0))).label ≠ 0 ↔ A = tList tT := by
  rw [tyList_eq]
  exact equal_label A (tList tT)

/-- The mirror's rule of a primitive at literals. -/
theorem core_delta (E : Env) (G : List Glob) (k : Tree) (args : List Tree)
    (pk : List Tree → List Tree → Tree) (ps : List (Tree × (List Tree → List Tree → Tree)))
    (Pk : Chk) (qs : List (Tree × Chk)) (hqs : qs.map Prod.fst = args) (Γ : Ctx)
    (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 17) (k :: args) ((k, pk) :: ps) Γ
      (H.map encEqn) = enc ((checkCore 17 ((k, Pk) :: qs) E G Γ H).map encEqn) := by
  rule_dispatch
  subst hqs
  simp only [«Prelude.tail», Const.lcase]
  cases Γ with
  | cons A Γ' => rfl
  | nil =>
    simp only [«Reader.nonEmpty», Const.lcase, label_leaf, ne_eq, not_true_eq_false,
      ↓reduceIte, allT_label, isLit_label, List.all_eq_true, mk1_eq, apps_eq, typeIn_typeOf]
    split_ifs with hlit
    · rcases hm : infer G [] (apps (mk Label.prim [k]) (qs.map Prod.fst)) with _ | ⟨A, f⟩
      · simp only [typeOf, hm, Option.map_none, Option.bind_none]
        rfl
      · simp only [typeOf, hm, Option.map_some, Option.bind_some, bindO_some, equal_tT,
          equal_tLT, lit?]
        by_cases hA : A = tT
        · subst hA
          simp only [↓reduceIte, dite_true]
          rw [← delta_tree hlit hm ()]
          rfl
        · by_cases hL : A = tList tT
          · subst hL
            simp only [↓reduceIte, dite_true, hA, dite_false, listLit_eq, Const.children]
            rw [← delta_list hlit hm ()]
            rfl
          · simp only [hA, hL, ↓reduceIte, dite_false]
            rfl
    · rfl

/-- The mirror's rule of induction on a list. -/
theorem core_indList (E : Env) (G : List Glob) (s t c0 c1 : Tree)
    (ps pt p0 p1 : List Tree → List Tree → Tree) (Ps Pt P0 P1 : Chk) (hp0 : Agrees E G p0 P0)
    (hp1 : Agrees E G p1 P1) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkCore» E.defs (G.map (·.1)) (leaf 23) [s, t, c0, c1]
      [(s, ps), (t, pt), (c0, p0), (c1, p1)] Γ (H.map encEqn) =
      enc ((checkCore 23 [(s, Ps), (t, Pt), (c0, P0), (c1, P1)] E G Γ H).map encEqn) := by
  rule_dispatch
  cases Γ with
  | nil => rfl
  | cons L Γ' =>
    simp only [Const.lcase, listParts_mirror, typeIn_typeOf]
    split_ifs with hL
    · cases typeOf G (L :: Γ') s with
      | none => rfl
      | some B =>
        simp only [Option.bind_some, bindO_some, mapT_eqLower, mapT_eqWk, eqn_eq, wkAt_eq,
          ← List.map_cons]
        rw [hp0, hp1]
        simp only [isTy_label, hasType_label, weakens_label, equal_enc, subst_eq, var_eq, and_assoc,
          mk1_eq, node2_mk]
        rule_close
    · rfl

/-- The mirror's application to two arguments. -/
theorem app2_eq (f a b : Tree) : «Equations.app2» f a b = apps f [a, b] := rfl

/-- The mirror's application to three arguments. -/
theorem app3_eq (f a b c : Tree) : «Equations.app3» f a b c = apps f [a, b, c] := rfl

/-- The mirror's application. -/
theorem app_eq (f a : Tree) : «Reader.app» f a = mk 10 [f, a] := rfl

/-- The mirror's test of a term's type as the type of trees. -/
theorem hasType_tT (G : List Glob) (Γ : Ctx) (t : Tree) :
    («Equations.hasType» (G.map (·.1)) Γ t (leaf 0)).label ≠ 0 ↔ typeOf G Γ t = some tT :=
  hasType_label G Γ t tT

/-- The mirror's function type from trees. -/
theorem tyArrow_tT (B : Tree) : «Check.tyArrow» (leaf 0) B = tArrow tT B :=
  tyArrow_eq tT B

/-- The mirror's type of lists of trees. -/
theorem tyList_tT : «Check.tyList» (leaf 0) = tList tT := tyList_eq tT

/-- The mirror's list of values of a function at the elements of a list of trees. -/
theorem mapBy_tT (B body xs : Tree) :
    «Equations.mapBy» (leaf 0) B body xs = mapBy tT B body xs :=
  mapBy_eq tT B body xs

/-- A context whose innermost type is the type of trees. -/
theorem cons_tT (Γ : Ctx) : (leaf 0 :: Γ : Ctx) = tT :: Γ := congrArg (· :: Γ) rfl

/-- The mirror's rule of case analysis at the empty list. -/
theorem more_lcaseNil (E : Env) (G : List Glob) (A B n c : Tree)
    (pA pB pn pc : List Tree → List Tree → Tree) (PA PB Pn Pc : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 24) [A, B, n, c]
      [(A, pA), (B, pB), (n, pn), (c, pc)] Γ (H.map encEqn) =
      enc ((checkMore 24 [(A, PA), (B, PB), (n, Pn), (c, Pc)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, tyArrow_eq, tyList_eq]
  rule_close

/-- The mirror's rule of case analysis at a list of a head and a tail. -/
theorem more_lcaseCons (E : Env) (G : List Glob) (A B x xs n c : Tree)
    (pA pB px pxs pn pc : List Tree → List Tree → Tree) (PA PB Px Pxs Pn Pc : Chk) (Γ : Ctx)
    (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 25)
      [A, B, x, xs, n, c] [(A, pA), (B, pB), (x, px), (xs, pxs), (n, pn), (c, pc)] Γ
      (H.map encEqn) =
      enc ((checkMore 25 [(A, PA), (B, PB), (x, Px), (xs, Pxs), (n, Pn), (c, Pc)] E G Γ
        H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, tyArrow_eq, tyList_eq]
  rule_close

/-- The mirror's rule of iteration at the label zero. -/
theorem more_iterZero (E : Env) (G : List Glob) (A s z : Tree)
    (pA ps pz : List Tree → List Tree → Tree) (PA Ps Pz : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 26) [A, s, z]
      [(A, pA), (s, ps), (z, pz)] Γ (H.map encEqn) =
      enc ((checkMore 26 [(A, PA), (s, Ps), (z, Pz)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [isTy_label, hasType_label, tyArrow_eq]
  rule_close

/-- The mirror's rule of iteration at the successor of a label. -/
theorem more_iterSucc (E : Env) (G : List Glob) (A s z n : Tree)
    (pA ps pz pn : List Tree → List Tree → Tree) (PA Ps Pz Pn : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 27) [A, s, z, n]
      [(A, pA), (s, ps), (z, pz), (n, pn)] Γ (H.map encEqn) =
      enc ((checkMore 27 [(A, PA), (s, Ps), (z, Pz), (n, Pn)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_tT]
  simp only [isTy_label, hasType_label, tyArrow_eq]
  rule_close

/-- The mirror's rule of the fold of trees at a node. -/
theorem more_foldNode (E : Env) (G : List Glob) (A f x xs : Tree)
    (pA pf px pxs : List Tree → List Tree → Tree) (PA Pf Px Pxs : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 28) [A, f, x, xs]
      [(A, pA), (f, pf), (x, px), (xs, pxs)] Γ (H.map encEqn) =
      enc ((checkMore 28 [(A, PA), (f, Pf), (x, Px), (xs, Pxs)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_tT, tyArrow_tT, tyList_tT]
  simp only [isTy_label, hasType_label, tyArrow_eq, tyList_eq, mapBy_eq, wk_eq]
  rule_close

/-- The mirror's rule of the fold of trees whose step sees the node itself, at a node. -/
theorem more_paraNode (E : Env) (G : List Glob) (A f x xs : Tree)
    (pA pf px pxs : List Tree → List Tree → Tree) (PA Pf Px Pxs : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 37) [A, f, x, xs]
      [(A, pA), (f, pf), (x, px), (xs, pxs)] Γ (H.map encEqn) =
      enc ((checkMore 37 [(A, PA), (f, Pf), (x, Px), (xs, Pxs)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_tT, tyArrow_tT, tyList_tT]
  simp only [isTy_label, hasType_label, tyArrow_eq, tyList_eq, mapBy_eq, wk_eq]
  rule_close

/-- The mirror's rule of induction on a tree. -/
theorem more_indTree (E : Env) (G : List Glob) (s t c1 : Tree)
    (ps pt p1 : List Tree → List Tree → Tree) (Ps Pt P1 : Chk) (hp1 : Agrees E G p1 P1)
    (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 29) [s, t, c1]
      [(s, ps), (t, pt), (c1, p1)] Γ (H.map encEqn) =
      enc ((checkMore 29 [(s, Ps), (t, Pt), (c1, P1)] E G Γ H).map encEqn) := by
  rule_dispatch
  cases Γ with
  | nil => rfl
  | cons L Γ' =>
    simp only [Const.lcase, typeIn_typeOf]
    cases typeOf G (L :: Γ') s with
    | none => rfl
    | some B =>
      simp only [tyList_tT, mapBy_tT, cons_tT, equal_tT]
      simp only [Option.bind_some, bindO_some, mapT_eqLower, mapT_eqWk, eqn_eq, wkAt_eq,
        tyList_eq, subst_eq, var_eq, ← List.map_cons]
      rw [hp1]
      simp only [equal_enc]
      simp only [isTy_label, hasType_label, weakens_label, and_assoc, mk1_eq, app2_eq]
      rule_close

/-- The mirror's rule of induction on the label of a tree. -/
theorem more_indLabel (E : Env) (G : List Glob) (s t c0 c1 : Tree)
    (ps pt p0 p1 : List Tree → List Tree → Tree) (Ps Pt P0 P1 : Chk) (hp0 : Agrees E G p0 P0)
    (hp1 : Agrees E G p1 P1) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 30)
      [s, t, c0, c1] [(s, ps), (t, pt), (c0, p0), (c1, p1)] Γ (H.map encEqn) =
      enc ((checkMore 30 [(s, Ps), (t, Pt), (c0, P0), (c1, P1)] E G Γ H).map encEqn) := by
  rule_dispatch
  cases Γ with
  | nil => rfl
  | cons L Γ' =>
    simp only [Const.lcase, typeIn_typeOf]
    cases typeOf G (L :: Γ') s with
    | none => rfl
    | some B =>
      simp only [Option.bind_some, bindO_some, mapT_eqLower, eqn_eq, wkAt_eq, subst_eq, var_eq,
        ← List.map_cons]
      rw [hp0, hp1]
      simp only [equal_enc, equal_tT]
      simp only [hasType_label, weakens_label, and_assoc, mk1_eq, app2_eq, app_eq]
      rule_close

/-- The mirror's rule of unfolding a reference to a definition. -/
theorem more_unfold (E : Env) (G : List Glob) (j : Tree) (pj : List Tree → List Tree → Tree)
    (Pj : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 31) [j]
      [(j, pj)] Γ (H.map encEqn) =
      enc ((checkMore 31 [(j, Pj)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [Const.label, nth_eq]
  cases E.defs[j.label]? with
  | none => rfl
  | some d =>
    simp only [bindO_some, mk1_eq, typeIn_typeOf, wk_eq, Option.bind_some, Label.ref]
    cases typeOf G Γ (mk 23 [j]) <;> rfl

/-- The mirror's rule of the conditional at a quoted tree. -/
theorem more_condQuote (E : Env) (G : List Glob) (c a b : Tree)
    (pc pa pb : List Tree → List Tree → Tree) (Pc Pa Pb : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 32) [c, a, b]
      [(c, pc), (a, pa), (b, pb)] Γ (H.map encEqn) =
      enc ((checkMore 32 [(c, Pc), (a, Pa), (b, Pb)] E G Γ H).map encEqn) := by
  rule_dispatch
  rw [typeIn_typeOf]
  cases typeOf G Γ a with
  | none => rfl
  | some A =>
    simp only [Option.bind_some, bindO_some, hasType_label]
    rule_close

/-- The mirror's rule of an instance of an axiom. -/
theorem more_ax (E : Env) (G : List Glob) (j : Tree) (us : List Tree)
    (pj : List Tree → List Tree → Tree) (ps : List (Tree × (List Tree → List Tree → Tree)))
    (Pj : Chk) (qs : List (Tree × Chk)) (hqs : qs.map Prod.fst = us) (Γ : Ctx)
    (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 33) (j :: us)
      ((j, pj) :: ps) Γ (H.map encEqn) =
      enc ((checkMore 33 ((j, Pj) :: qs) E G Γ H).map encEqn) := by
  rule_dispatch
  subst hqs
  simp only [«Prelude.tail», Const.lcase, axioms_eq, Const.label, nth_eq,
    List.getElem?_map]
  cases axioms[j.label]? with
  | none => rfl
  | some th => simp only [Option.map_some, bindO_some, Option.bind_some, cite_eq]

/-- The mirror's rule of iteration reading the label of the tree it iterates over. -/
theorem more_iterLabel (E : Env) (G : List Glob) (A s z t : Tree)
    (pA ps pz pt : List Tree → List Tree → Tree) (PA Ps Pz Pt : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 34) [A, s, z, t]
      [(A, pA), (s, ps), (z, pz), (t, pt)] Γ (H.map encEqn) =
      enc ((checkMore 34 [(A, PA), (s, Ps), (z, Pz), (t, Pt)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_tT]
  simp only [isTy_label, hasType_label, tyArrow_eq]
  rule_close

/-- The mirror's rule of the conditional as an iteration. -/
theorem more_condIter (E : Env) (G : List Glob) (A c a b : Tree)
    (pA pc pa pb : List Tree → List Tree → Tree) (PA Pc Pa Pb : Chk) (Γ : Ctx) (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 35) [A, c, a, b]
      [(A, pA), (c, pc), (a, pa), (b, pb)] Γ (H.map encEqn) =
      enc ((checkMore 35 [(A, PA), (c, Pc), (a, Pa), (b, Pb)] E G Γ H).map encEqn) := by
  rule_dispatch
  simp only [hasType_tT]
  simp only [isTy_label, hasType_label, wk_eq]
  rule_close

/-- The mirror's rule of an instance of a theorem. -/
theorem more_thm (E : Env) (G : List Glob) (j : Tree) (us : List Tree)
    (pj : List Tree → List Tree → Tree) (ps : List (Tree × (List Tree → List Tree → Tree)))
    (Pj : Chk) (qs : List (Tree × Chk)) (hqs : qs.map Prod.fst = us) (Γ : Ctx)
    (H : List Eqn) :
    «Equations.checkMore» E.defs (E.thms.map encThm) (G.map (·.1)) (leaf 36) (j :: us)
      ((j, pj) :: ps) Γ (H.map encEqn) =
      enc ((checkMore 36 ((j, Pj) :: qs) E G Γ H).map encEqn) := by
  rule_dispatch
  subst hqs
  simp only [«Prelude.tail», Const.lcase, Const.label, nth_eq, List.getElem?_map]
  cases E.thms[j.label]? with
  | none => rfl
  | some th => simp only [Option.map_some, bindO_some, Option.bind_some, cite_eq]

end GebTests.Prototypes.GoedelT.MirrorRules

end
