/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Typechecker
public import Geb.Prototypes.Computability.Oitavem.BoundedQuantification
public import Geb.Prototypes.Computability.Oitavem.Length
public import Geb.Prototypes.Computability.PresheafScan

set_option doc.verso true in
/-!
# Decision problems represented by Oitavem expressions

Unary denotations of Oitavem expressions form a submonoid of bitstring
endomorphisms. This instantiates the decision-problem category directly from
syntax, without assuming an equivalence with a machine complexity class.
Normalizing an expression's result supplies a two-valued object of the category.

A binary expression can check a position, represented by a suffix, against the
unchanged input. Bounded universal quantification turns it into a decision
problem accepting exactly when every position passes. Membership in the
submonoid is witnessed by the constructed expression.

## Main definitions

* {lit}`Expr.unary` interprets a unary expression as an endomorphism.
* {lit}`definableSubmonoid` contains exactly those endomorphisms.
* {lit}`Expr.admissible` supplies an admissible map together with its syntax witness.
* {lit}`Expr.decisionProblem` turns a word-valued test into a decision problem.
* {lit}`Expr.scan` and {lit}`Expr.scanProblem` check every input position.

## Main statements

* {lit}`Expr.decisionProblem_pass_iff` identifies the accepted fiber.
* {lit}`Expr.scanProblem_pass_iff` identifies the universally checked fiber.
* {lit}`Expr.presheafScan_pass_iff` turns a correct local position test into a
  presheaf recognizer in the decision-problem category.
* {lit}`no_universal_decider` rules out a universal membership test for
  arbitrary encoded checkers within the same algebra.
* {lit}`no_squareFold` shows that admissible constructor operations need not have
  an admissible fold on explicit word-shaped trees.

## Tags

decision problem, submonoid, logspace, bounded quantification, typechecker
-/

set_option doc.verso true

@[expose] public section

universe u v uA uB

namespace Geb.Oitavem

open CategoryTheory GebProto.EndomorphismCategory

/-- Interpret a unary expression with its sole input in normal position. -/
def Expr.unary (e : Expr 1 0) : Function.End (List Bool) := fun w ↦ e.eval ![w] Fin.elim0

/-- Unary substitution is composition of word functions. -/
theorem Expr.unary_comp (e d : Expr 1 0) :
    (Expr.comp (safe := false) e ![d]).unary = e.unary ∘ d.unary := by
  funext w
  change e.eval (fun i ↦ (![d] i).eval ![w] Fin.elim0) Fin.elim0 =
    e.eval ![d.eval ![w] Fin.elim0] Fin.elim0
  congr 1
  funext i
  exact Fin.cases rfl (fun j ↦ j.elim0) i

/-- Unary expression denotations contain the identity and are closed under composition. -/
def definableSubmonoid : Submonoid (Function.End (List Bool)) where
  carrier := {f | ∃ e : Expr 1 0, e.unary = f}
  one_mem' := ⟨Expr.initial (.proj 1 0), rfl⟩
  mul_mem' := by
    rintro f g ⟨e, rfl⟩ ⟨d, rfl⟩
    exact ⟨Expr.comp (safe := false) e ![d], Expr.unary_comp e d⟩

/-- An expression supplies its admissibility witness directly. -/
def Expr.admissible (e : Expr 1 0) : definableSubmonoid := ⟨e.unary, e, rfl⟩

/-- Every Boolean verdict is one of the two distinct truth values. -/
theorem truth_twoValued (p : List Bool → Bool) :
    TwoValued [true] [] (fun x ↦ truth (p x)) :=
  ⟨by decide, fun x ↦ by cases p x <;> simp [truth]⟩

/-- Normalize an expression's nonempty output to acceptance. -/
def Expr.decisionProblem (e : Expr 1 0) : DecisionProblem definableSubmonoid [true] [] where
  checker := e.nonempty.admissible
  twoValued := by
    change TwoValued [true] [] (fun w ↦ e.nonempty.eval ![w] Fin.elim0)
    simp only [Expr.eval_nonempty]
    exact truth_twoValued _

/-- The decision problem accepts exactly the nonempty outputs of its expression. -/
theorem Expr.decisionProblem_pass_iff (e : Expr 1 0) (w : List Bool) :
    e.decisionProblem.checker.val w = [true] ↔ e.unary w ≠ [] := by
  change e.nonempty.eval ![w] Fin.elim0 = [true] ↔ _
  rw [Expr.eval_nonempty]
  cases h : e.unary w with
  | nil => simp [Expr.unary] at h; simp [h, truth]
  | cons b v => simp [Expr.unary] at h; simp [h, truth]

/-- Check every suffix against the unchanged original input. -/
def Expr.scan (p : Expr 2 0) : Expr 1 0 :=
  Expr.comp (safe := false) p.allSuffixes fun _ ↦ Expr.initial (.proj 1 0)

/-- The scan is the conjunction of the position checks. -/
theorem Expr.eval_scan (p : Expr 2 0) (w : List Bool) :
    p.scan.unary w = truth (w.tails.all fun v ↦ !(p.eval ![v, w] Fin.elim0).isEmpty) := by
  change p.allSuffixes.eval (fun _ ↦ w) Fin.elim0 = _
  have h : (fun _ : Fin 2 ↦ w) = Fin.cons w ![w] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i
  rw [h]
  exact Expr.eval_allSuffixes p w ![w]

/-- The decision problem requiring every input position to pass the given test. -/
def Expr.scanProblem (p : Expr 2 0) : DecisionProblem definableSubmonoid [true] [] :=
  p.scan.decisionProblem

/-- Universal position checking is internal to the Oitavem decision-problem category. -/
theorem Expr.scanProblem_pass_iff (p : Expr 2 0) (w : List Bool) :
    p.scanProblem.checker.val w = [true] ↔
      ∀ v ∈ w.tails, p.eval ![v, w] Fin.elim0 ≠ [] := by
  rw [Expr.scanProblem, Expr.decisionProblem_pass_iff, Expr.eval_scan]
  rw [truth_ne_nil, List.all_eq_true]
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff]

/-- A local Oitavem position test supplies a presheaf decision problem. The
node-position reader must cover precisely the input tree's nodes; non-node
positions pass. Constructing this local expression from coded signature
operations is a separate obligation from this scan-composition theorem. -/
theorem Expr.presheafScan_pass_iff {I : Type u} [CategoryTheory.Category.{v} I]
    (F : PresheafPFunctor.{u, u, uA, uB, v, v} I I)
    (decI : DecidableEq I) (feI : FinEnum I)
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) (feB : ∀ a, FinEnum (F.toPFunctor.B a))
    (decEqW : DecidableEq (WType F.toPFunctor.B)) (p : Expr 2 0) (w : List Bool)
    (z : F.toSlicePFunctor.W) (nodeAt : List Bool → Option (WType F.toPFunctor.B))
    (sound : ∀ v ∈ w.tails, ∀ t, nodeAt v = some t →
      t ∈ Geb.PresheafRecognition.occurrences feB z.1)
    (complete : ∀ t ∈ Geb.PresheafRecognition.occurrences feB z.1,
      ∃ v ∈ w.tails, nodeAt v = some t)
    (hlocal : ∀ v ∈ w.tails, (!(p.eval ![v, w] Fin.elim0).isEmpty) =
      (nodeAt v).all (Geb.PresheafRecognition.localNaturality F decI feI feHom feB decEqW)) :
    p.scanProblem.checker.val w = [true] ↔ F.IsHereditarilyNatural z := by
  have hc := Geb.PresheafRecognition.positions_eq_native F decI feI feHom feB decEqW
    w z.1 nodeAt sound complete (fun v ↦ !(p.eval ![v, w] Fin.elim0).isEmpty) hlocal
  have heval : p.scan.unary w =
      truth (F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1) :=
    (Expr.eval_scan p w).trans (congrArg truth hc)
  rw [Expr.scanProblem, Expr.decisionProblem_pass_iff, heval, truth_ne_nil]
  exact F.isHereditarilyNaturalBoolCore_eq_true_iff decI feI feHom feB decEqW z

/-- There is no class-internal membership test for all encoded Oitavem checkers,
even when only their acceptance verdicts, rather than full outputs, are required. -/
theorem no_universal_decider (encode : List Bool → List Bool → List Bool)
    (hdiag : (fun w ↦ encode w w) ∈ definableSubmonoid) (eval : Expr 1 0)
    (complete : ∀ e : Expr 1 0, ∃ c, ∀ w,
      eval.unary (encode w c) ≠ [] ↔ e.unary w ≠ []) : False := by
  obtain ⟨d, hd⟩ := hdiag
  let e := (Expr.comp (safe := false) eval ![d]).negation
  obtain ⟨c, hc⟩ := complete e
  have he : e.unary c = truth (eval.unary (encode c c)).isEmpty := by
    change (Expr.comp (safe := false) eval ![d]).negation.eval ![c] Fin.elim0 = _
    rw [Expr.eval_negation]
    change truth ((Expr.comp (safe := false) eval ![d]).unary c).isEmpty = _
    rw [Expr.unary_comp]
    change truth (eval.unary (d.unary c)).isEmpty = _
    rw [congrFun hd c]
  have h := hc c
  rw [he, truth_ne_nil] at h
  cases hw : eval.unary (encode c c) with
  | nil =>
    rw [hw] at h
    exact h.mpr rfl rfl
  | cons b v =>
    rw [hw] at h
    exact Bool.noConfusion (h.mp (List.cons_ne_nil b v))

/-- Fold a word-shaped unary tree, squaring the output at each constructor.
The base is a constant expression and the step is the expression {lit}`squareWord`. -/
def squareFold : List Bool → List Bool :=
  List.rec [true, true] fun _ _ r ↦ squareWord.unary r

/-- Repeated squaring makes the output doubly exponential in the tree's depth. -/
theorem length_squareFold (w : List Bool) : (squareFold w).length = 2 ^ (2 ^ w.length) := by
  refine List.rec (motive := fun w ↦ (squareFold w).length = 2 ^ (2 ^ w.length)) rfl ?_ w
  intro b v ih
  change (squareWord.eval ![squareFold v] Fin.elim0).length = _
  rw [length_squareWord, ih]
  simp only [List.length_cons, pow_succ, ← pow_add, Nat.mul_two]

/-- The growth of this fold exceeds every polynomial bound. -/
theorem exists_poly_lt_doubleExp (c d : ℕ) : ∃ n, c * (n + 1) ^ d < 2 ^ (2 ^ n) := by
  let k := c + d + 2
  let n := 2 * k
  have hexp : c + n * d < 2 ^ n := by
    calc
      c + n * d < 2 * k * (d + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        dsimp [n, k]
        omega
      _ ≤ 2 * k * k := Nat.mul_le_mul_left (2 * k) (by dsimp [k]; omega)
      _ = 2 * k ^ 2 := by rw [Nat.pow_two, Nat.mul_assoc]
      _ < 2 ^ n := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  refine ⟨n, Nat.lt_of_le_of_lt ?_ (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) hexp)⟩
  calc
    c * (n + 1) ^ d ≤ 2 ^ c * (2 ^ n) ^ d :=
      Nat.mul_le_mul (Nat.le_of_lt Nat.lt_two_pow_self)
        (Nat.pow_le_pow_left Nat.lt_two_pow_self d)
    _ = 2 ^ (c + n * d) := by rw [← Nat.pow_mul, Nat.pow_add]

/-- Even with Oitavem-definable base and step, the fold on explicit unary trees
need not be Oitavem-definable. This obstructs an unrestricted W-eliminator. -/
theorem no_squareFold (e : Expr 1 0) : ¬ (∀ w, e.unary w = squareFold w) := by
  intro he
  obtain ⟨c, d, hbound⟩ := e.length_le_poly
  obtain ⟨n, hn⟩ := exists_poly_lt_doubleExp c d
  let w := List.replicate n false
  have hw : w.length = n := List.length_replicate
  have h := hbound ![w] Fin.elim0 n (fun i ↦ by simpa only [Matrix.vec_single_eq_const] using hw.le)
  change (e.unary w).length ≤ _ at h
  rw [he w, length_squareFold, hw] at h
  exact Nat.not_lt_of_ge h hn

end Geb.Oitavem
