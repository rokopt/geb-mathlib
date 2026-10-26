/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.WiringIndex
public import Geb.Prototypes.InteractionNet.NamedWiring
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Renaming invariance of graph assembly

Named-wire construction depends on which endpoints have equal names, rather than on their
enumeration order. Boundary attachment likewise commutes with bijections of internal cells
and attachment positions. These facts support changes of syntax order and occurrence
indices in the compiler's graph interpretation while fixing the observable boundary.

## Main statements

* {lit}`Wiring.ofNames_respects` — an injection preserving equal names preserves named wires.
* {lit}`PortNet.coupleIso` — cell and attachment renaming preserve graph assembly.

## Tags

interaction net, graph, compiler, renaming, gluing, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

namespace Wiring

variable {P Q ν μ : Type} [DecidableEq P] [DecidableEq Q]
variable [BEq ν] [LawfulBEq ν] [BEq μ] [LawfulBEq μ]

/-- Preserving distinct endpoint occurrences and their name classes preserves every named wire. -/
theorem ofNames_respects (ps : List P) (pu : ps.Nodup) (pc : ∀ p, p ∈ ps)
    (pn : P → ν) (pt : ∀ p, (ps.map pn).count (pn p) = 2)
    (qs : List Q) (qu : qs.Nodup) (qc : ∀ q, q ∈ qs)
    (qn : Q → μ) (qt : ∀ q, (qs.map qn).count (qn q) = 2)
    (e : P ↪ Q) (names : ∀ p p', pn p = pn p' → qn (e p) = qn (e p')) :
    Respects e (ofNames ps pu pc pn pt) (ofNames qs qu qc qn qt) := by
  intro p
  apply ofNames_partner_eq
  · exact fun h ↦ (ofNames ps pu pc pn pt).fixedPointFree p (e.injective h)
  · exact names _ _ (ofNames_partner_name ps pu pc pn pt p)

end Wiring

namespace PortNet

variable {α C D B B' Γ : Type} {arity : α → ℕ} {label : C → α} {label' : D → α}
variable [FinEnum C] [FinEnum D] [FinEnum Γ] [FinEnum B] [FinEnum B']

/-- Renaming attachment positions and cells commutes with assembly, fixing the external boundary. -/
def coupleIso (n : PortNet arity label B) (m : PortNet arity label' B')
    (w : Wiring (Γ ⊕ B)) (w' : Wiring (Γ ⊕ B')) (b : B ≃ B') (e : C ≃ D)
    (labels : ∀ c, label' (e c) = label c)
    (wires : n.wiring.map (endpointEquiv arity b e labels) = m.wiring)
    (loops : n.loops = m.loops)
    (boundary : w.map (Equiv.sumCongr (Equiv.refl Γ) b) = w') :
    (n.couple w).Iso (m.couple w') := by
  let ambient := Equiv.sumCongr (Equiv.sumCongr (Equiv.refl Γ) b)
    (endpointEquiv arity b e labels)
  have hn : Wiring.Respects (endpointEquiv arity b e labels).toEmbedding n.wiring m.wiring := by
    rw [← wires]
    exact Wiring.respects_map _ _
  have hb : Wiring.Respects (Equiv.sumCongr (Equiv.refl Γ) b).toEmbedding w w' := by
    rw [← boundary]
    exact Wiring.respects_map _ _
  have hs : Wiring.Respects ambient.toEmbedding (w.sum n.wiring) (w'.sum m.wiring) := hb.sum hn
  have hp : (couplePorts arity label Γ B).trans ambient.toEmbedding =
      (b.prodCongr (Equiv.refl Bool)).toEmbedding.trans (couplePorts arity label' Γ B') := by
    ext p
    rcases p with ⟨p, bit⟩
    cases bit <;> rfl
  have hg := hs.glue (couplePorts arity label Γ B) (FinEnum.toList B)
    (w.sum n.wiring, n.loops) (w'.sum m.wiring, m.loops) loops
  rw [hp, Wiring.glue_enum_equiv] at hg
  have hleft := n.couple_spec w
  have hright := m.couple_spec w'
  refine ⟨e, labels, ?_, hleft.2.trans (hg.2.trans hright.2.symm)⟩
  apply (hleft.1.trans hg.1).map_eq hright.1
    (endpointEquiv arity (Equiv.refl Γ) e labels)
  intro p
  cases p <;> rfl

end PortNet

end Geb.InteractionNet

end
