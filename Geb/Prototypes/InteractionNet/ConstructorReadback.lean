/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermCellOrder
public import Geb.Prototypes.InteractionNet.TermGraphReadback
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Constructor read-back agrees with term syntax

Reading a term's graph follows its ordered constructor children. The visited cells are
exactly the term's parent-first cell order. A bound exceeding the number of syntax cells
therefore suffices to recover the same constructor tree as a structural fold of the term.

## Main definitions

* {lit}`Term.constructorReadback` — read a constructor tree directly from term syntax.

## Main statements

* {lit}`Term.fragment_readTree` — bounded graph traversal agrees with the syntax constructor fold.

## Tags

interaction net, constructor, graph, read-back, term, compiler
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν : Type} {arity : α → ℕ}

private theorem sequence_pairs {X Y Z : Type} (f : X → Option Y) (g : X → Z) (xs : List X) :
    ((xs.map fun x ↦ (f x).map (fun y ↦ (y, g x))).mapM id) =
      ((xs.map f).mapM id).map (fun ys ↦ ys.zip (xs.map g)) := by
  refine List.rec rfl (fun x xs ih ↦ ?_) xs
  simp only [List.map_cons, List.mapM_cons, ih]
  cases f x <;> cases (xs.map f).mapM id <;> rfl

private theorem sequence_length {X : Type} (xs : List (Option X)) (ys : List X)
    (h : xs.mapM id = some ys) : ys.length = xs.length := by
  revert ys
  refine List.rec (fun ys h ↦ by cases h; rfl) (fun x xs ih ys h ↦ ?_) xs
  cases x with
  | none => simp [List.mapM_cons] at h
  | some x =>
    cases hs : xs.mapM id with
    | none => simp [List.mapM_cons, hs] at h
    | some zs =>
      have hy : x :: zs = ys := by simpa [List.mapM_cons, hs] using h
      subst ys
      exact congrArg Nat.succ (ih zs hs)

/-- Known child visit lists are concatenated when their constructor observations succeed. -/
theorem PortNet.readNode_visits {C : Type} (tag : α → Option ℕ) (a : α) (c : C)
    (children : Fin (arity a) → Option (RoseTree ℕ)) (visits : Fin (arity a) → List C) :
    readNode tag a c (fun i ↦ (children i).map (fun t ↦ (t, visits i))) =
      (do
        let l ← tag a
        let ts ← (List.ofFn children).mapM id
        pure (RoseTree.node l ts)).map
          (fun t ↦ (t, c :: (List.ofFn visits).flatten)) := by
  unfold readNode
  simp only [List.ofFn_eq_map]
  rw [sequence_pairs]
  cases tag a with
  | none => rfl
  | some l =>
    cases hs : ((List.finRange (arity a)).map children).mapM id with
    | none => rfl
    | some ts =>
      have hl := sequence_length _ ts hs
      have hf : ts.length ≤ ((List.finRange (arity a)).map visits).length := by
        simpa only [List.length_map] using Nat.le_of_eq hl
      have hg : ((List.finRange (arity a)).map visits).length ≤ ts.length := by
        simpa only [List.length_map] using Nat.le_of_eq hl.symm
      simp only [bind, Option.bind_some, Option.map_some, pure, List.map_fst_zip hf]
      rw [List.flatMap, List.map_snd_zip hg]

namespace Term

private theorem nat_le_sum_of_mem (xs : List ℕ) (x : ℕ) (h : x ∈ xs) : x ≤ xs.sum := by
  revert x
  refine List.rec (fun _ h ↦ (List.not_mem_nil h).elim) (fun y ys ih x h ↦ ?_) xs
  simp only [List.sum_cons]
  rcases List.mem_cons.mp h with rfl | h
  · omega
  · have hi := ih x h
    omega

/-- Read a constructor tree from syntax, rejecting variables and unrecognized agent symbols. -/
def constructorReadback (tag : α → Option ℕ) : Term arity ν → Option (RoseTree ℕ) :=
  PFunctor.FreeM.rec (fun _ ↦ none) (fun a _ children ↦ do
    let l ← tag a
    let ts ← (List.ofFn children).mapM id
    pure (RoseTree.node l ts))

/-- A depth bound exceeding the cell count reads syntax and records every cell exactly once. -/
theorem fragment_readTree (tag : α → Option ℕ) (t : Term arity ν) (fuel : ℕ)
    (bound : t.cellOrder.length < fuel) :
    t.fragment.net.readTree tag fuel (.inl (.inl ())) =
      (t.constructorReadback tag).map (fun r ↦ (r, t.cellOrder)) := by
  revert fuel
  refine PFunctor.FreeM.rec (fun x fuel bound ↦ ?_) (fun a ts ih fuel bound ↦ ?_) t
  · cases fuel with
    | zero => exact (Nat.not_lt_zero _ bound).elim
    | succ fuel => rfl
  · cases fuel with
    | zero => exact (Nat.not_lt_zero _ bound).elim
    | succ fuel =>
      have hc (i : Fin (arity a)) : (cellOrder (ts i)).length < fuel := by
        have hi : (cellOrder (ts i)).length ≤
            ((List.finRange (arity a)).map fun j ↦ (cellOrder (ts j)).length).sum :=
          nat_le_sum_of_mem _ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
        change (Sum.inl () :: (List.finRange (arity a)).flatMap
          (fun i ↦ (cellOrder (ts i)).map
            (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (fragment (ts i)).Cell)))).length < fuel + 1 at bound
        simp only [List.length_cons, List.length_flatMap, List.length_map] at bound
        change ((List.finRange (arity a)).map
          (fun j ↦ (cellOrder (ts j)).length)).sum + 1 < fuel + 1 at bound
        omega
      change (TermFragment.agent a (fun i ↦ fragment (ts i))).net.readTree tag (fuel + 1)
        (.inl (.inl ())) = _
      rw [TermFragment.agent_readTree_root]
      have hr (i : Fin (arity a)) := ih i fuel (hc i)
      simp only [hr, Option.map_map, Function.comp_def]
      let visits (i : Fin (arity a)) : List (Unit ⊕ (Σ i, (fragment (ts i)).Cell)) :=
        (cellOrder (ts i)).map (fun c ↦ Sum.inr ⟨i, c⟩)
      have hv : (List.ofFn visits).flatten = (List.finRange (arity a)).flatMap visits := by
        rw [List.ofFn_eq_map]
        rfl
      have hn := PortNet.readNode_visits tag a (Sum.inl ())
        (fun i ↦ constructorReadback tag (ts i)) visits
      rw [hv] at hn
      exact hn

end Term

end Geb.InteractionNet

end
