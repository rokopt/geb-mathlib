/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Basic
public import Geb.Prototypes.MType.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Guarded blocks and their M-type solutions

A block is guarded when no body is a bare reference to an export of the block: each body is
an operation applied to terms over the imports and exports, or an import
{cite}`MiliusMoss2009`. Stated as a type, the body at an export is an element of
{lit}`P.Obj (P.FreeM (Γ ⊕ E)) ⊕ Γ` rather than of {lit}`P.FreeM (Γ ⊕ E)`, so guardedness is
checked by type checking. The bodies are terms of any depth, and the references into the
block's own exports may form cycles.

With imports interpreted in the M-type {name}`Geb.MType.M`, constructed from W-types, a
guarded block has exactly one solution there. The solution is the corecursion whose states
are finished values of the M-type, for the imports, and pending terms: a term emits its root
operation, and a reference to an export emits the root of that export's body. Both halves are
bisimulations. Existence relates the corecursion from each state to that state's value;
uniqueness relates the values of a term under any two solutions, since a reference to an
export evaluates through its guarded body to a root operation over the values of subterms.
{name}`Geb.MType.M.bisim` is proved by recursion on depth, the reading of guarded recursion
as well-founded recursion in presheaves on the ordinal {lit}`ω`
{cite}`BirkedalMogelbergSchwinghammerStovring2012`.

## Main definitions

* {lit}`GuardedBlock` is a block whose bodies are guarded by their type.
* {lit}`GuardedBlock.toBlock` gives the equations of a guarded block.
* {lit}`GuardedBlock.solution` is its solution in the M-type.

## Main statements

* {lit}`GuardedBlock.isSolution_solution` states that the solution satisfies the equations.
* {lit}`GuardedBlock.eq_of_isSolution` states that any two solutions are equal.
* {lit}`GuardedBlock.existsUnique_isSolution` gives each guarded block exactly one solution
  in the M-type.

## References

* {cite}`MiliusMoss2009`, Sections 3 and 6, for guarded equation morphisms and their unique
  solutions in completely iterative algebras, the M-type among them.
* {cite}`BirkedalMogelbergSchwinghammerStovring2012` for guarded recursion as recursion on
  depth.

## Tags

guarded recursion, equation morphism, M-type, corecursion, bisimulation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition

open PFunctor

variable {P : PFunctor.{0, 0}} {Γ E : Type}

/-- A guarded block: the body at each export is an operation applied to terms over the imports
and exports, or an import. -/
abbrev GuardedBlock (P : PFunctor.{0, 0}) (Γ E : Type) := E → P.Obj (P.FreeM (Γ ⊕ E)) ⊕ Γ

namespace GuardedBlock

/-- A guarded body as a term: the operation applied to its terms, or the import. -/
def body : P.Obj (P.FreeM (Γ ⊕ E)) ⊕ Γ → P.FreeM (Γ ⊕ E) :=
  Sum.elim (fun x ↦ .liftBind x.1 x.2) fun x ↦ .pure (.inl x)

/-- The equations of a guarded block, forgetting the guard. -/
def toBlock (d : GuardedBlock P Γ E) : Block P Γ E := fun i ↦ body (d i)

/-- One layer of a pending term: an operation emits itself over its subterms, an import
emits the root of its value, and a reference to an export emits the root of that export's
body. -/
def stepTerm (env : Γ → MType.M P) (d : GuardedBlock P Γ E) :
    P.FreeM (Γ ⊕ E) → P.Obj (MType.M P ⊕ P.FreeM (Γ ⊕ E))
  | .liftBind a ts => ⟨a, fun b ↦ .inr (ts b)⟩
  | .pure (.inl x) => P.map .inl (env x).dest
  | .pure (.inr i) => Sum.elim (P.map .inr) (fun x ↦ P.map .inl (env x).dest) (d i)

/-- One layer of the solution: a finished value emits its root, a pending term one layer. -/
def step (env : Γ → MType.M P) (d : GuardedBlock P Γ E) :
    MType.M P ⊕ P.FreeM (Γ ⊕ E) → P.Obj (MType.M P ⊕ P.FreeM (Γ ⊕ E)) :=
  Sum.elim (fun m ↦ P.map .inl m.dest) (stepTerm env d)

/-- The solution of a guarded block in the M-type: the corecursion from the reference to
each export. -/
def solution (env : Γ → MType.M P) (d : GuardedBlock P Γ E) (i : E) : MType.M P :=
  MType.M.corec (step env d) (.inr (.pure (.inr i)))

/-- The corecursion from every state is the state's value: a finished value is itself, and a
pending term is its evaluation with the exports interpreted by the solution. -/
theorem corec_step (env : Γ → MType.M P) (d : GuardedBlock P Γ E)
    (s : MType.M P ⊕ P.FreeM (Γ ⊕ E)) :
    MType.M.corec (step env d) s =
      Sum.elim id (eval MType.M.mk (Sum.elim env (solution env d))) s := by
  set F := Sum.elim id (eval MType.M.mk (Sum.elim env (solution env d)))
  refine MType.M.bisim (fun x y ↦ x = y ∨ ∃ s, x = MType.M.corec (step env d) s ∧ y = F s)
    ?_ _ _ (.inr ⟨s, rfl, rfl⟩)
  -- A state whose layer is that of a finished value `m`, and whose value is `m`: the roots
  -- agree, and the children are related as finished values to the corecursions from them.
  have fin (s : MType.M P ⊕ P.FreeM (Γ ⊕ E)) (m : MType.M P)
      (hs : step env d s = P.map .inl m.dest) (hy : F s = m) :
      ∃ a f g, (MType.M.corec (step env d) s).dest = ⟨a, f⟩ ∧ (F s).dest = ⟨a, g⟩ ∧
        ∀ b, (f b = g b ∨ ∃ s, f b = MType.M.corec (step env d) s ∧ g b = F s) :=
    ⟨m.dest.1, fun b ↦ MType.M.corec (step env d) (.inl (m.dest.2 b)), m.dest.2,
      by rw [MType.M.dest_corec, hs]; rfl, by rw [hy]; rfl,
      fun b ↦ .inr ⟨.inl (m.dest.2 b), rfl, rfl⟩⟩
  rintro x y (rfl | ⟨s, rfl, rfl⟩)
  · exact ⟨x.dest.1, x.dest.2, x.dest.2, rfl, rfl, fun _ ↦ .inl rfl⟩
  rcases s with m | (x | ⟨a, ts⟩)
  · exact fin (.inl m) m rfl rfl
  · rcases x with x | i
    · exact fin (.inr (.pure (.inl x))) (env x) rfl rfl
    · have hy : F (.inr (.pure (.inr i))) =
          MType.M.corec (step env d) (.inr (.pure (.inr i))) := rfl
      rw [hy]
      exact ⟨_, _, _, MType.M.dest_corec _ _, MType.M.dest_corec _ _, fun _ ↦ .inl rfl⟩
  · have hy : F (.inr (.liftBind a ts)) = MType.M.mk ⟨a, fun b ↦ F (.inr (ts b))⟩ := rfl
    rw [hy]
    exact ⟨a, _, _, MType.M.dest_corec _ _, MType.M.dest_mk _,
      fun b ↦ .inr ⟨.inr (ts b), rfl, rfl⟩⟩

/-- A guarded body evaluates to its root layer over the values of its subterms. -/
theorem eval_body (env : Γ → MType.M P) (d : GuardedBlock P Γ E)
    (g : P.Obj (P.FreeM (Γ ⊕ E)) ⊕ Γ) :
    eval MType.M.mk (Sum.elim env (solution env d)) (body g) =
      MType.M.mk (P.map (Sum.elim id (eval MType.M.mk (Sum.elim env (solution env d))))
        (Sum.elim (P.map .inr) (fun x ↦ P.map .inl (env x).dest) g)) := by
  rcases g with g | x
  · rfl
  · exact (MType.M.mk_dest (env x)).symm

/-- The solution satisfies the equations of the block. -/
theorem isSolution_solution (env : Γ → MType.M P) (d : GuardedBlock P Γ E) :
    IsSolution MType.M.mk env d.toBlock (solution env d) := fun i ↦
  (eval_body env d (d i)).trans ((MType.M.corec_eq _ _).trans
    (congrArg (fun f ↦ MType.M.mk (P.map f (step env d (.inr (.pure (.inr i))))))
      (funext (corec_step env d)))).symm

/-- Any two solutions of a guarded block are equal. -/
theorem eq_of_isSolution (env : Γ → MType.M P) (d : GuardedBlock P Γ E) {v w : E → MType.M P}
    (hv : IsSolution MType.M.mk env d.toBlock v) (hw : IsSolution MType.M.mk env d.toBlock w) :
    v = w := by
  set Fv := eval MType.M.mk (Sum.elim env v)
  set Fw := eval MType.M.mk (Sum.elim env w)
  suffices key : ∀ t, Fv t = Fw t from funext fun i ↦ key (.pure (.inr i))
  intro t
  refine MType.M.bisim (fun x y ↦ x = y ∨ ∃ t, x = Fv t ∧ y = Fw t) ?_ _ _
    (.inr ⟨t, rfl, rfl⟩)
  -- An operation over terms has that root under both solutions, with children related as
  -- the values of its subterms.
  have op (a : P.A) (ts : P.B a → P.FreeM (Γ ⊕ E)) : ∃ a' f g,
      (Fv (.liftBind a ts)).dest = ⟨a', f⟩ ∧ (Fw (.liftBind a ts)).dest = ⟨a', g⟩ ∧
        ∀ b, (f b = g b ∨ ∃ t, f b = Fv t ∧ g b = Fw t) :=
    ⟨a, _, _, MType.M.dest_mk _, MType.M.dest_mk _, fun b ↦ .inr ⟨ts b, rfl, rfl⟩⟩
  -- An import has the same value under both solutions.
  have imp (x : Γ) : ∃ a' f g,
      (Fv (.pure (.inl x))).dest = ⟨a', f⟩ ∧ (Fw (.pure (.inl x))).dest = ⟨a', g⟩ ∧
        ∀ b, (f b = g b ∨ ∃ t, f b = Fv t ∧ g b = Fw t) :=
    ⟨(env x).dest.1, (env x).dest.2, (env x).dest.2, rfl, rfl, fun _ ↦ .inl rfl⟩
  rintro x y (rfl | ⟨t, rfl, rfl⟩)
  · exact ⟨x.dest.1, x.dest.2, x.dest.2, rfl, rfl, fun _ ↦ .inl rfl⟩
  rcases t with (x | j) | ⟨a, ts⟩
  · exact imp x
  · -- A reference to an export evaluates through the export's guarded body.
    have hv' : Fv (.pure (.inr j)) = Fv (body (d j)) := (hv j).symm
    have hw' : Fw (.pure (.inr j)) = Fw (body (d j)) := (hw j).symm
    rw [hv', hw']
    rcases d j with ⟨a, ts⟩ | x
    · exact op a ts
    · exact imp x
  · exact op a ts

/-- A guarded block has exactly one solution in the M-type. -/
theorem existsUnique_isSolution (env : Γ → MType.M P) (d : GuardedBlock P Γ E) :
    ∃! v, IsSolution MType.M.mk env d.toBlock v :=
  ⟨solution env d, isSolution_solution env d, fun _ hw ↦
    eq_of_isSolution env d hw (isSolution_solution env d)⟩

end GuardedBlock

end Geb.Definition

end
