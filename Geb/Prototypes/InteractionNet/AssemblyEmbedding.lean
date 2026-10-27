/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.TermGraphAttachment
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Graph assembly inside a common endpoint space

Boundary coupling and term attachment can be performed inside a larger matching. Their
endpoint embeddings identify every retained wire, and their loop equations keep any closed
components already present outside the operation. These specifications allow successive
assembly operations to be compared in one common allocation of endpoints.

## Main statements

* {lit}`PortNet.couple_in` — boundary coupling preserves an ambient matching embedding.
* {lit}`TermFragment.attach_in` — term attachment preserves an ambient matching embedding.

## Tags

interaction net, graph, assembly, attachment, embedding, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α C B Γ P ν μ : Type} {arity : α → ℕ} {label : C → α} [DecidableEq P]

/-- Attach a boundary matching within a larger matching, preserving its external loop offset. -/
theorem PortNet.couple_in [FinEnum C] [FinEnum B] [FinEnum Γ]
    (n : PortNet arity label B) (w : Wiring (Γ ⊕ B))
    (e : CouplingEndpoint arity label Γ B ↪ P) (ambient : Wiring P × ℕ)
    (he : Wiring.Respects e (w.sum n.wiring) ambient.1) (extra : ℕ)
    (hl : n.loops + extra = ambient.2) :
    let g := Wiring.glue ((couplePorts arity label Γ B).trans e) (FinEnum.toList B) ambient
    Wiring.Respects ((coupleEmbedding arity label Γ B).trans e) (n.couple w).wiring g.1 ∧
      (n.couple w).loops + extra = g.2 := by
  have hs := n.couple_spec w
  have hg := he.glue_offset (couplePorts arity label Γ B) (FinEnum.toList B)
    (w.sum n.wiring, n.loops) ambient extra hl
  exact ⟨hs.1.trans hg.1, (congrArg (· + extra) hs.2).trans hg.2⟩

/-- Attach replacements within a larger matching, preserving its external closed components. -/
theorem TermFragment.attach_in (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ)
    (e : AttachmentEndpoint f g ↪ P) (ambient : Wiring P × ℕ)
    (he : Wiring.Respects e (attachmentState f g).1 ambient.1) (extra : ℕ)
    (hl : (attachmentState f g).2 + extra = ambient.2) :
    let w := Wiring.glue ((attachmentPorts f g).trans e) f.order ambient
    Wiring.Respects ((attachmentEmbedding f g).trans e) (f.attach g).net.wiring w.1 ∧
      (f.attach g).net.loops + extra = w.2 := by
  let : DecidableEq (AttachmentEndpoint f g) := attachmentDecidableEq f g
  have hs := f.attach_spec g
  have hg := he.glue_offset (attachmentPorts f g) f.order (attachmentState f g) ambient extra hl
  exact ⟨hs.1.trans hg.1, (congrArg (· + extra) hs.2).trans hg.2⟩

end Geb.InteractionNet

end
