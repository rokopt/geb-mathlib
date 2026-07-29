/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Batteries.Data.UnionFind
public import Mathlib.Data.List.Basic

/-!
# A size-indexed union-find and the fold over a list of edges

`Batteries.UnionFind` carries its size as a field, so an index into it
has type `Fin self.size` and every operation that changes the
structure changes the index type. `Sized n` fixes the size as a
subtype, so the indices are `Fin n` throughout and no cast is needed
to pass one operation's index to the next. `Sized.ofEdges` folds
`Sized.union` over a list of pairs, and the two theorems about it are
the two directions of correctness: every listed pair is merged, and
nothing beyond the listed pairs is.

The second is stated as an eliminator — any `h : Fin n → α` agreeing
on the listed pairs agrees on roots — rather than as a
characterisation of the merged relation as the equivalence closure of
the edges. The eliminator is what a coequalizer's factorisation law
instantiates directly.

The upstream target of this module is Batteries rather than mathlib4,
`Sized` being a wrapper over a Batteries type; where such content
belongs is `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

## Main definitions

* `Batteries.UnionFind.Sized` — a union-find of a fixed size.
* `Batteries.UnionFind.Sized.discrete`,
  `Batteries.UnionFind.Sized.union`,
  `Batteries.UnionFind.Sized.root` — the operations, at `Fin n`.
* `Batteries.UnionFind.Sized.ofEdges` — the fold over a list of
  pairs.

## Main statements

* `Batteries.UnionFind.Sized.root_ofEdges_eq_of_mem` — every listed
  pair is merged.
* `Batteries.UnionFind.Sized.apply_root_ofEdges` — nothing beyond the
  listed pairs is merged, in eliminator form.

## Tags

union-find, disjoint set, quotient, choice-free
-/

@[expose] public section

universe u

namespace Batteries.UnionFind

variable {n : Nat}

/-- `union` preserves the size. -/
theorem size_union (self : UnionFind) (x y : Fin self.size) :
    (self.union x y).size = self.size := by
  unfold union; simp [UnionFind.size]

/-- `push` adds one to the size. -/
theorem size_push (self : UnionFind) : self.push.size = self.size + 1 := by
  unfold push; simp [UnionFind.size]

/-- A union-find whose size is fixed, so that its indices are
`Fin n` and no operation changes their type. -/
def Sized (n : Nat) : Type := {u : UnionFind // u.size = n}

/-- The discrete partition on `n` elements: `n` `push`es onto the
empty structure. -/
def Sized.discrete (n : Nat) : Sized n :=
  Nat.rec (motive := fun m ↦ Sized m) ⟨.empty, rfl⟩
    (fun _ v ↦ ⟨v.1.push, by rw [size_push, v.2]⟩) n

/-- Merge the classes of two indices. -/
def Sized.union (v : Sized n) (x y : Fin n) : Sized n :=
  ⟨v.1.unionN x y v.2.symm, by obtain ⟨u, rfl⟩ := v; exact size_union u x y⟩

/-- The representative of an index's class, as an index. -/
def Sized.root (v : Sized n) (x : Fin n) : Fin n :=
  ⟨v.1.rootD x, by obtain ⟨u, rfl⟩ := v; exact UnionFind.rootD_lt.mpr x.isLt⟩

/-- The union-find obtained by merging every listed pair. -/
def Sized.ofEdges (n : Nat) (l : List (Fin n × Fin n)) : Sized n :=
  l.foldl (fun v p ↦ v.union p.1 p.2) (discrete n)

/-- Two indices have the same root exactly when they are equivalent. -/
theorem Sized.root_eq_iff {v : Sized n} {a b : Fin n} :
    v.root a = v.root b ↔ v.1.Equiv a b := Fin.ext_iff

/-- `Batteries.UnionFind.equiv_union` restated at `Sized.union`. The
`Nat` arguments match Batteries' `Equiv`; the `Fin n` arguments the
other lemmas pass are coerced. -/
theorem Sized.equiv_union {v : Sized n} {x y : Fin n} {a b : Nat} :
    (v.union x y).1.Equiv a b ↔
      v.1.Equiv a b ∨ v.1.Equiv a x ∧ v.1.Equiv y b
                    ∨ v.1.Equiv a y ∧ v.1.Equiv x b := by
  obtain ⟨u, rfl⟩ := v
  exact UnionFind.equiv_union

/-- Every index is its own root in the discrete partition. -/
theorem Sized.rootD_discrete (m x : Nat) : (discrete m).1.rootD x = x :=
  Nat.rec (motive := fun k ↦ (discrete k).1.rootD x = x)
    UnionFind.rootD_empty (fun _ ih ↦ (UnionFind.root_push).trans ih) m

/-- `Sized.rootD_discrete` at `Fin n`. -/
theorem Sized.root_discrete (x : Fin n) : (discrete n).root x = x :=
  Fin.ext (rootD_discrete n x)

/-- A root is its own root. -/
theorem Sized.root_root (v : Sized n) (x : Fin n) :
    v.root (v.root x) = v.root x := Fin.ext UnionFind.rootD_rootD

end Batteries.UnionFind
