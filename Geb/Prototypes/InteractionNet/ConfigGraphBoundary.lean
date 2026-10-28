/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphPermutation
public import Geb.Prototypes.InteractionNet.GraphConfluence
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiled configurations at a fixed boundary size

Textual execution preserves interface length without retaining the same interface terms.
A proof of the common length places every compiled configuration in one graph type.
The transport keeps every numeric boundary position and respects equation permutations
and reversals.

## Main definitions

* {lit}`Config.graphAt` — compile a closed configuration at its specified boundary size.

## Main statements

* {lit}`Config.graphAt_nextName` — allocation counters do not affect graph identity.
* {lit}`Config.graphAt_perm` — equation permutations preserve the represented graph.
* {lit}`Config.graphAt_swap` — reversing an equation preserves the represented graph.

## Tags

interaction net, compiler, configuration, graph, boundary, execution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

variable {α : Type} {arity : α → ℕ} {boundary : ℕ}

/-- Compile a configuration, retaining numeric boundary positions at the specified common size. -/
def graphAt (c : Config arity) (closed : c.Closed) (h : c.interface.length = boundary) :
    Graph arity boundary :=
  let n := c.toFiniteNet closed
  Graph.ofNet ⟨n.1, n.2.1, n.2.2.reboundary (finCongr h)⟩

/-- The identity size transport leaves the compiled graph unchanged. -/
theorem graphAt_refl (c : Config arity) (closed : c.Closed) :
    c.graphAt closed rfl = Graph.ofNet (c.toFiniteNet closed) := by
  change Graph.ofNet ⟨_, _, (c.toFiniteNet closed).2.2.reboundary (Equiv.refl _)⟩ = _
  rw [PortNet.reboundary_refl]

/-- The fresh-name counter does not contribute a graph endpoint or a wire. -/
theorem graphAt_nextName (c : Config arity) (next : ℕ) (closed : c.Closed)
    (h : c.interface.length = boundary) :
    ({ c with nextName := next } : Config arity).graphAt closed h = c.graphAt closed h := by
  let d : Config arity := { c with nextName := next }
  have ht (i : d.GraphRoot) : c.graphTerm i = d.graphTerm i := by
    rcases i with i | (i | i) <;> rfl
  have hw : d.graphRootWiring.map (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)) =
      c.graphRootWiring := by
    ext p
    rcases p with i | (i | (i | i)) <;> rfl
  have hi := d.reorderGraphIso c closed closed (Equiv.refl _) (Equiv.refl _) ht hw
  rw [PortNet.reboundary_refl] at hi
  exact Quotient.sound ⟨hi.reboundary (finCongr h)⟩

/-- A graph at a fixed size is independent of the order of textual equations. -/
theorem graphAt_perm (c : Config arity) (es : List (Equation arity ℕ))
    (hp : es.Perm c.equations) (closed : c.Closed) (h : c.interface.length = boundary) :
    c.graphAt closed h =
      ({ c with equations := es } : Config arity).graphAt (c.closed_perm es hp closed) h := by
  obtain ⟨i⟩ := c.toFiniteNet_perm es hp closed
  exact Quotient.sound ⟨i.reboundary (finCongr h)⟩

/-- Reversing a textual equation preserves its compiled graph at the fixed external size. -/
theorem graphAt_swap (c : Config arity) (e : Equation arity ℕ)
    (closed : ({ c with equations := e :: c.equations } : Config arity).Closed)
    (h : c.interface.length = boundary) :
    ({ c with equations := e :: c.equations } : Config arity).graphAt closed h =
      ({ c with equations := (e.2, e.1) :: c.equations } : Config arity).graphAt
        (c.closed_swap e closed) h :=
  Quotient.sound ⟨(c.swapGraphIso e closed).reboundary (finCongr h)⟩

end Geb.InteractionNet.Config

end
