/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ArrayWiring
public import Geb.Prototypes.InteractionNet.WiringEmbedding
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compacting the live endpoints of a partner array

After a graph contraction, discarded endpoints are isolated from all live endpoints.
A finite injection lists the live endpoints in their new order. Searching that list
decodes each live endpoint's partner, yielding a compact partner array. The closed-image
invariant makes every search succeed. Compaction is executable and preserves every live
wire; the search-based implementation is intended for the verified prototype.

## Main definitions

* {lit}`ArrayWiring.Closed` — partners of live endpoints are live.
* {lit}`ArrayWiring.pullback` — compact a closed set of live endpoints into a new array.

## Main statements

* {lit}`ArrayWiring.pullback_respects` — compaction preserves partners under the live injection.
* {lit}`ArrayWiring.pullback_eq` — compaction reads back any matching represented by that injection.

## Tags

interaction net, runtime, compaction, array, read-back, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.ArrayWiring

variable {size live : ℕ}

/-- The listed live endpoints are closed under the array's partner operation. -/
def Closed (w : ArrayWiring size) (e : Fin live ↪ Fin size) : Prop :=
  ∀ p, ∃ q, w.links[e p] = e q

/-- Every represented matching has a closed image in its ambient array. -/
theorem closed_of_respects {w : ArrayWiring size} {e : Fin live ↪ Fin size}
    {v : Wiring (Fin live)} (h : Wiring.Respects e v w.read) : w.Closed e :=
  fun p ↦ ⟨v.partner p, h p⟩

/-- Locate a live endpoint's partner in the new compact enumeration. -/
def partner? (w : ArrayWiring size) (e : Fin live ↪ Fin size) (p : Fin live) : Option (Fin live) :=
  (List.finRange live).find? (fun q ↦ decide (w.links[e p] = e q))

/-- A closed live image makes partner decoding succeed. -/
theorem partner?_isSome (w : ArrayWiring size) (e : Fin live ↪ Fin size)
    (h : w.Closed e) (p : Fin live) : (w.partner? e p).isSome := by
  obtain ⟨q, hq⟩ := h p
  exact List.find?_isSome.mpr ⟨q, List.mem_finRange q, by simpa only [decide_eq_true_eq] using hq⟩

/-- Decode the partner of a live endpoint, using the closed-image proof only for totality. -/
def partner (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) (p : Fin live) :
    Fin live := (w.partner? e p).get (w.partner?_isSome e h p)

/-- The decoded endpoint is exactly the array's original partner. -/
theorem partner_spec (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e)
    (p : Fin live) : e (w.partner e h p) = w.links[e p] := by
  have hf := List.find?_some (Option.eq_some_of_isSome (w.partner?_isSome e h p))
  exact (of_decide_eq_true hf).symm

/-- Materialize the live matching at compact indices, preserving the matching invariant. -/
def pullback (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    ArrayWiring live :=
  encode
    { partner := w.partner e h
      involutive p := by
        apply e.injective
        exact (w.partner_spec e h (w.partner e h p)).trans
          ((congrArg w.read.partner (w.partner_spec e h p)).trans (w.involutive (e p)))
      fixedPointFree p hp := by
        have he := w.partner_spec e h p
        rw [hp] at he
        exact w.fixedPointFree (e p) he.symm }

/-- Compaction preserves every live wire through its original endpoint injection. -/
theorem pullback_respects (w : ArrayWiring size) (e : Fin live ↪ Fin size) (h : w.Closed e) :
    Wiring.Respects e (w.pullback e h).read w.read := by
  intro p
  simp only [pullback, read_encode]
  exact (w.partner_spec e h p).symm

/-- A compacted array reads back the matching represented by its live endpoint injection. -/
theorem pullback_eq {w : ArrayWiring size} {e : Fin live ↪ Fin size} {v : Wiring (Fin live)}
    (h : Wiring.Respects e v w.read) : (w.pullback e (closed_of_respects h)).read = v := by
  apply Wiring.ext
  funext p
  apply e.injective
  exact ((w.pullback_respects e (closed_of_respects h)) p).symm.trans (h p)

end Geb.InteractionNet.ArrayWiring

end
