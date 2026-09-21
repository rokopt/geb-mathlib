/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Sig
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Bundles: a root over an expression

The admissible trees of the bundle signature at the root index are the
expressions of Logs with one normal and no safe argument, each under a root
node. Embedding wraps every shape of a tree of Logs; the root's child is such
a tree, and the equivalence {lit}`bundleEquiv` identifies bundles with
expressions. The spelling of a bundle is a fixed prefix, the root's spine
and label, followed by the spelling of the embedded expression.

# Main definitions

* {lit}`embed`, {lit}`unembed` — a tree of Logs as a tree of the bundle
  signature, and back.
* {lit}`Bundle`, {lit}`wrap`, {lit}`unwrap`, {lit}`bundleEquiv` — the
  admissible trees at the root index, and their equivalence with
  expressions.
* {lit}`rootPrefix` — the prefix every bundle's spelling carries.

# Main statements

* {lit}`wValid_embed`, {lit}`wIndexRoot_embed` — embedding preserves
  admissibility and the index.
* {lit}`unembed_embed`, {lit}`embed_unembed` — the two directions invert on
  trees of Logs and on admissible trees with a wrapped root.
* {lit}`spell_wrap` — the spelling of a wrapped expression.

# Tags

bitstream, M-type, slice polynomial functor, W-type, logspace
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Shape Direction Expr)
open Geb.SizeBounded.Logspace.WTree (CodedSig)
open Geb.BitTree (Tree leaf fork)

public section

/-- A tree of Logs as a tree of the bundle signature, every shape wrapped. -/
@[expose] def embed : Geb.Oitavem.sig.toPFunctor.W → sig.toPFunctor.W :=
  WType.elim sig.toPFunctor.W fun x ↦ WType.mk (some x.1) x.2

/-- Embedding at a node. -/
theorem embed_mk (a : Shape) (f : Direction a → Geb.Oitavem.sig.toPFunctor.W) :
    embed (WType.mk a f) = WType.mk (some a) fun d ↦ embed (f d) := rfl

/-- A tree of Logs standing in for the root when unwrapping. -/
@[expose] def junk : Geb.Oitavem.sig.toPFunctor.W := WType.mk (.initial (.zero 0)) Fin.elim0

/-- A tree of the bundle signature as a tree of Logs: a wrapped shape
unwrapped, the root replaced by a stand-in. -/
@[expose] def unembed : sig.toPFunctor.W → Geb.Oitavem.sig.toPFunctor.W :=
  WType.elim Geb.Oitavem.sig.toPFunctor.W fun x ↦ match x with
    | ⟨none, _⟩ => junk
    | ⟨some a, c⟩ => WType.mk a c

/-- Unembedding inverts embedding. -/
theorem unembed_embed : ∀ w, unembed (embed w) = w
  | WType.mk a f => congrArg (WType.mk a) (funext fun d ↦ unembed_embed (f d))

/-- The index of an embedded tree is the index of the tree, wrapped. -/
theorem wIndexRoot_embed : ∀ w, sig.wIndexRoot (embed w) = some (Geb.Oitavem.sig.wIndexRoot w)
  | WType.mk _ _ => rfl

/-- Embedding preserves admissibility. -/
theorem wValid_embed : ∀ w, sig.WValid (embed w) ↔ Geb.Oitavem.sig.WValid w
  | WType.mk a f => by
    have h1 := SlicePFunctor.wValid_mk sig (some a) fun d ↦ embed (f d)
    have h2 := SlicePFunctor.wValid_mk Geb.Oitavem.sig a f
    refine h1.trans (Iff.trans ?_ h2.symm)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun d ↦ (wValid_embed (f d)).mp (h1 d), funext fun d ↦ ?_⟩
      exact Option.some.inj ((wIndexRoot_embed (f d)).symm.trans (congrFun h2 d))
    · rintro ⟨h1, h2⟩
      refine ⟨fun d ↦ (wValid_embed (f d)).mpr (h1 d), funext fun d ↦ ?_⟩
      exact (wIndexRoot_embed (f d)).trans (congrArg some (congrFun h2 d))

/-- A tree whose index is wrapped has a wrapped root. -/
theorem head_isSome_of_wIndexRoot (t : sig.toPFunctor.W) (i : ℕ × ℕ)
    (h : sig.wIndexRoot t = some i) : (PFunctor.W.head t).isSome = true := by
  cases t with
  | mk a c =>
    cases a with
    | none => cases h
    | some a => rfl

/-- Embedding inverts unembedding on admissible trees with a wrapped root. -/
theorem embed_unembed : ∀ t : sig.toPFunctor.W, sig.WValid t →
    (PFunctor.W.head t).isSome = true → embed (unembed t) = t
  | WType.mk none _, _, hs => by cases hs
  | WType.mk (some a) c, hv, _ => by
    obtain ⟨hall, hover⟩ := (SlicePFunctor.wValid_mk sig (some a) c).mp hv
    refine congrArg (WType.mk (some a)) (funext fun d ↦ embed_unembed (c d) (hall d) ?_)
    exact head_isSome_of_wIndexRoot (c d) _ (congrFun hover d)

/-- The admissible trees at the root index. -/
abbrev Bundle := {t : sig.W // sig.wIndex t = none}

/-- The root's child. -/
@[expose] def child : sig.toPFunctor.W → sig.toPFunctor.W
  | WType.mk none c => c ()
  | WType.mk (some _) _ => WType.mk none fun _ ↦ embed junk

/-- A bundle is a root over its child. -/
theorem bundle_eq (b : Bundle) : b.1.1 = WType.mk none fun _ ↦ child b.1.1 := by
  obtain ⟨⟨t, hv⟩, hi⟩ := b
  cases t with
  | mk a c =>
    cases a with
    | none => exact congrArg (WType.mk none) (funext fun u ↦ by cases u; rfl)
    | some a => cases hi

/-- The child of a bundle is admissible with the index of an expression of
one normal and no safe argument. -/
theorem child_valid (b : Bundle) :
    sig.WValid (child b.1.1) ∧ sig.wIndexRoot (child b.1.1) = some (1, 0) := by
  have hv := b.1.2
  rw [bundle_eq b] at hv
  have hv' := (SlicePFunctor.wValid_mk sig none fun _ ↦ child b.1.1).mp hv
  exact ⟨hv'.1 (), congrFun hv'.2 ()⟩

/-- An expression under a root. -/
@[expose] def wrap (e : Expr 1 0) : Bundle :=
  ⟨⟨WType.mk none fun _ ↦ embed e.1.1, (SlicePFunctor.wValid_mk _ _ _).mpr
    ⟨fun _ ↦ (wValid_embed _).mpr e.1.2, funext fun _ ↦ by
      rw [Function.comp_apply, wIndexRoot_embed]
      exact congrArg some e.2⟩⟩, rfl⟩

/-- The expression under a bundle's root. -/
@[expose] def unwrap (b : Bundle) : Expr 1 0 :=
  ⟨⟨unembed (child b.1.1), by
    obtain ⟨hv, hi⟩ := child_valid b
    rw [← wValid_embed, embed_unembed _ hv (head_isSome_of_wIndexRoot _ _ hi)]
    exact hv⟩, by
    obtain ⟨hv, hi⟩ := child_valid b
    apply Option.some.inj
    change some (Geb.Oitavem.sig.wIndexRoot (unembed (child b.1.1))) = _
    rw [← wIndexRoot_embed, embed_unembed _ hv (head_isSome_of_wIndexRoot _ _ hi)]
    exact hi⟩

/-- Bundles are expressions of one normal and no safe argument. -/
@[expose] def bundleEquiv : Bundle ≃ Expr 1 0 where
  toFun := unwrap
  invFun := wrap
  left_inv b := by
    obtain ⟨hv, hi⟩ := child_valid b
    refine Subtype.ext (Subtype.ext ?_)
    change WType.mk none (fun _ ↦ embed (unembed (child b.1.1))) = b.1.1
    rw [embed_unembed _ hv (head_isSome_of_wIndexRoot _ _ hi)]
    exact (bundle_eq b).symm
  right_inv e := Subtype.ext (Subtype.ext (unembed_embed e.1.1))

/-- The prefix of every bundle's spelling: the root's one fork, and the
root's label as a leaf. -/
@[expose] def rootPrefix : List Bool :=
  true :: false :: (Geb.BitTree.Elias.encodeNat (code none).length ++ code none)

/-- The spelling of a wrapped expression: the prefix, then the spelling of
the embedded expression. -/
theorem spell_wrap (e : Expr 1 0) :
    coded.spell (wrap e).1.1 = rootPrefix ++ coded.spell (embed e.1.1) := by
  change Geb.BitTree.Elias.encode (Geb.SizeBounded.Logspace.WTree.spine (leaf (code none))
    (List.ofFn fun i : Fin 1 ↦ coded.toTree (embed e.1.1))) = _
  rw [List.ofFn_succ, List.ofFn_zero]
  rfl

end

end Geb.BitStream.Oitavem
