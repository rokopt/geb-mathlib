/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Vertex -- shake: keep

public meta import Geb.Prototypes.Definition.Vertex -- shake: keep

set_option doc.verso true in
/-!
# Examples of vertices and environments

The signature has cells, with two children, and atoms labelled by bitstrings, with none. An
environment pairs a parameter with a context of two layers, as a Nock subject pairs a sample
with its context. Vertices select the parameter, the context, a layer, or a node inside a
layer; a body written against the context is transported to the whole environment and
resolves to the same term.

## Main definitions

* {lit}`noun` has cells and bitstring atoms.
* {lit}`subject` pairs a parameter with two layers.
* {lit}`swapBody` refers to the lower layer and to the parameter by their vertices.
* {lit}`contextBody` refers to the upper layer by its vertex in the context.

## Main statements

* {lit}`ofDirection_sample` identifies the parameter's direction with its vertex.

## Tags

vertex, environment, subject, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.VertexTests

open PFunctor

/-- Cells, with two children, and atoms labelled by bitstrings, with none. -/
abbrev noun : PFunctor.{0, 0} := ⟨Option (List Bool), fun o ↦ Fin (o.elim 2 fun _ ↦ 0)⟩

/-- A cell. -/
def cell {X : Type} (x y : noun.FreeM X) : noun.FreeM X :=
  .liftBind none fun i ↦ Fin.cases x (fun _ ↦ y) i

/-- An atom. -/
def atom {X : Type} (bs : List Bool) : noun.FreeM X := .liftBind (some bs) Fin.elim0

/-- The upper layer. -/
def upper : noun.FreeM Unit := cell (atom [false]) (atom [true, true])

/-- The lower layer. -/
def lower : noun.FreeM Unit := atom [true]

/-- A parameter paired with a context of two layers. -/
def subject : noun.FreeM Unit := cell (.pure ()) (cell upper lower)

/-- The parameter. -/
def sampleV : Vertex subject := some ⟨(0 : Fin 2), ()⟩

/-- The context. -/
def contextV : Vertex subject := some ⟨(1 : Fin 2), none⟩

/-- The lower layer. -/
def lowerV : Vertex subject := some ⟨(1 : Fin 2), some ⟨(1 : Fin 2), none⟩⟩

/-- The parameter's direction of the free polynomial. -/
def sampleD : Direction subject := ⟨(0 : Fin 2), ()⟩

/-- The parameter's direction is its vertex. -/
theorem ofDirection_sample : Vertex.ofDirection sampleD = sampleV := rfl

/-- The lower layer paired with the parameter, by vertices of the subject. -/
def swapBody : noun.FreeM (Vertex subject) := cell (.pure lowerV) (.pure sampleV)

/-- The upper layer, as the first vertex below the context's root. -/
def upperInContext : Vertex (subterm subject contextV) := some ⟨(0 : Fin 2), none⟩

/-- A body written against the context: the upper layer paired with a new atom. -/
def contextBody : noun.FreeM (Vertex (subterm subject contextV)) :=
  cell (.pure upperInContext) (atom [false, true])

/-- The atoms of a noun in order, with each parameter contributing a marker. -/
def atoms (x : noun.Obj (List (List Bool))) : List (List Bool) :=
  match x with
  | ⟨none, f⟩ => f (0 : Fin 2) ++ f (1 : Fin 2)
  | ⟨some bs, _⟩ => [bs]

/-- The marker of a parameter. -/
def marker : Unit → List (List Bool) := fun _ ↦ [[]]

-- The vertices select the layer and the parameter.
#guard eval atoms marker (subterm subject lowerV) = [[true]]
#guard eval atoms marker (subterm subject contextV) = [[false], [true, true], [true]]
#guard eval atoms marker (subterm subject (Vertex.root subject)) =
  [[], [false], [true, true], [true]]
-- Resolution substitutes the subterm at each vertex.
#guard eval atoms marker (link (fun _ : Unit ↦ swapBody) (subterm subject) ()) = [[true], []]
-- Transport to the subject resolves as the original resolves against the context.
#guard eval atoms marker
    (link (fun _ : Unit ↦ contextBody.map contextV.append) (subterm subject) ()) =
  [[false], [true, true], [false, true]]
#guard eval atoms marker
    (link (fun _ : Unit ↦ contextBody) (subterm (subterm subject contextV)) ()) =
  [[false], [true, true], [false, true]]

end Geb.Definition.VertexTests

end
