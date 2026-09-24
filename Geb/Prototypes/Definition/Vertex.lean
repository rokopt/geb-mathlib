/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Cslib.Foundations.Data.PFunctor.Free
public import Geb.Prototypes.Definition.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Vertices of terms

A vertex of a term of the free monad is a rooted path: at a variable, the root; at an
operation, either the root or a direction of the operation followed by a vertex of that child.
A vertex selects a subterm, and a vertex of that subterm translates into a vertex of the whole
term. Subterms, the root and translation satisfy the five laws of a directed container
{cite}`AhmanChapmanUustalu2014`: terms and their vertices form the cofree recursive directed
container on the signature with the variables adjoined as nullary operations. Read as a tree
of that signature, a term is a shape of the cofree comonoid on it, and its vertices are the
directions there {cite}`NiuSpivak2023`; the free monad supplies the finite bodies and the
cofree comonoid the structures they are resolved against {cite}`LibkindSpivak2025`.

Where a direction of the free polynomial ({name}`Geb.Definition.Direction`) addresses a
variable leaf alone, a vertex addresses every node, operations and nullary operations
included. Each direction is a vertex, and the subterm it selects is its variable.

A term used as an environment is addressed by its vertices. A family of bodies whose variables
are vertices of an environment is resolved by linking it against the subterm map of the
environment; the result is a family over the environment's own variables. A family written
against the subterm at a vertex is transported to the whole environment by translating its
vertices, and the transported family resolves as the original resolves against the subterm.
Composed with {name}`Geb.Definition.eval_bind`, the value of a body at an environment is its
value with each vertex interpreted by the value of the subterm there.

## Main definitions

* {lit}`Vertex` gives the vertices of a term.
* {lit}`Vertex.root` is the root vertex.
* {lit}`subterm` selects the subterm at a vertex.
* {lit}`Vertex.append` translates a vertex of a subterm into a vertex of the whole term.
* {lit}`Vertex.ofDirection` is the vertex at a direction of the free polynomial.

## Main statements

* {lit}`subterm_root`, {lit}`subterm_append`, {lit}`Vertex.append_root`,
  {lit}`Vertex.root_append` and {lit}`Vertex.append_assoc` are the directed-container laws.
* {lit}`subterm_ofDirection` states that a direction selects its variable.
* {lit}`link_map_append` states that transport along a vertex preserves resolution.

## Implementation notes

{lit}`subterm` returns a term selected by a vertex whose type depends on the term, which the
fold of {name}`PFunctor.FreeM.liftM` into {name}`Cont` cannot express. The module therefore
imports the executable code for Cslib's {name}`PFunctor.FreeM.rec` that
{lit}`Geb.Cslib.Foundations.Data.PFunctor.Free` supplies, and every declaration here recurses
through that recursor.

## References

* {cite}`AhmanChapmanUustalu2014`, Section 3.1, for directed containers, and Section 4.4,
  for the cofree recursive directed container.
* {cite}`NiuSpivak2023`, Section 8.1, Proposition 8.18, for the cofree comonoid on a
  polynomial, whose directions at a tree are its rooted paths.
* {cite}`LibkindSpivak2025` for the free monad as a module over the cofree comonoid, the
  division of roles between bodies and what they run on.

## Tags

vertex, subterm, directed container, free monad, environment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition

open PFunctor

universe uA u

variable {P : PFunctor.{uA, u}} {Γ E : Type u}

/-- The vertices of a term: at a variable, the root; at an operation, the root or a direction
of the operation followed by a vertex of that child. -/
def Vertex (t : P.FreeM Γ) : Type u :=
  FreeM.rec (fun _ ↦ PUnit) (fun a _ vs ↦ Option ((b : P.B a) × vs b)) t

/-- The root vertex. -/
def Vertex.root : (t : P.FreeM Γ) → Vertex t
  | .pure _ => ⟨⟩
  | .liftBind _ _ => none

/-- The subterm at a vertex. -/
def subterm (t : P.FreeM Γ) : Vertex t → P.FreeM Γ :=
  FreeM.rec (motive := fun t ↦ Vertex t → P.FreeM Γ) (fun x _ ↦ .pure x)
    (fun a ts sub v ↦ Option.elim v (.liftBind a ts) fun p ↦ sub p.1 p.2) t

/-- Translate a vertex of the subterm at a vertex into a vertex of the whole term. -/
def Vertex.append {t : P.FreeM Γ} : (v : Vertex t) → Vertex (subterm t v) → Vertex t :=
  FreeM.rec (motive := fun t ↦ (v : Vertex t) → Vertex (subterm t v) → Vertex t)
    (fun _ _ _ ↦ ⟨⟩)
    (fun a ts app v ↦ match (motive := (v : Option ((b : P.B a) × Vertex (ts b))) →
        Vertex (subterm (.liftBind a ts) v) → Vertex (.liftBind a ts)) v with
      | none => fun w ↦ w
      | some p => fun w ↦ some ⟨p.1, app p.1 p.2 w⟩) t

/-- The subterm at the root is the whole term. -/
@[simp] theorem subterm_root (t : P.FreeM Γ) : subterm t (Vertex.root t) = t := by
  cases t <;> rfl

/-- The subterm at a translated vertex is the subterm of the subterm. -/
theorem subterm_append (t : P.FreeM Γ) (v : Vertex t) (w : Vertex (subterm t v)) :
    subterm t (v.append w) = subterm (subterm t v) w := by
  refine FreeM.rec (motive := fun t ↦ ∀ (v : Vertex t) (w : Vertex (subterm t v)),
    subterm t (v.append w) = subterm (subterm t v) w) (fun _ _ _ ↦ rfl) ?_ t v w
  intro a ts ih v w
  match v, w with
  | none, _ => rfl
  | some p, w => exact ih p.1 p.2 w

namespace Vertex

/-- Translating the root of a subterm gives the vertex of that subterm. -/
@[simp] theorem append_root {t : P.FreeM Γ} (v : Vertex t) :
    v.append (root (subterm t v)) = v := by
  refine FreeM.rec (motive := fun t ↦ ∀ v : Vertex t, v.append (root (subterm t v)) = v)
    (fun _ _ ↦ rfl) ?_ t v
  intro a ts ih v
  match v with
  | none => rfl
  | some p =>
    exact congrArg (fun w ↦ some (⟨p.1, w⟩ : (b : P.B a) × Vertex (ts b))) (ih p.1 p.2)

/-- Translating from the subterm at the root changes no vertex. -/
theorem root_append (t : P.FreeM Γ) (w : Vertex (subterm t (root t))) :
    (root t).append w = cast (congrArg Vertex (subterm_root t)) w := by
  cases t <;> rfl

/-- Translation is associative. -/
theorem append_assoc {t : P.FreeM Γ} (u : Vertex t) (v : Vertex (subterm t u))
    (w : Vertex (subterm t (u.append v))) :
    (u.append v).append w =
      u.append (v.append (cast (congrArg Vertex (subterm_append t u v)) w)) := by
  refine FreeM.rec (motive := fun t ↦ ∀ (u : Vertex t) (v : Vertex (subterm t u))
    (w : Vertex (subterm t (u.append v))), (u.append v).append w =
      u.append (v.append (cast (congrArg Vertex (subterm_append t u v)) w)))
    (fun _ _ _ _ ↦ rfl) ?_ t u v w
  intro a ts ih u v w
  match u, v, w with
  | none, _, _ => rfl
  | some p, v, w =>
    exact congrArg (fun x ↦ some (⟨p.1, x⟩ : (b : P.B a) × Vertex (ts b))) (ih p.1 p.2 v w)

/-- The vertex at a direction of the free polynomial: the same path, ending at the variable. -/
def ofDirection {s : P.FreeM PUnit.{u + 1}} : Direction s → Vertex s :=
  FreeM.rec (motive := fun s ↦ Direction s → Vertex s) (fun _ _ ↦ ⟨⟩)
    (fun a ts ofDir p ↦ some (⟨p.1, ofDir p.1 p.2⟩ : (b : P.B a) × Vertex (ts b))) s

end Vertex

/-- The subterm at a direction of the free polynomial is its variable. -/
@[simp] theorem subterm_ofDirection {s : P.FreeM PUnit.{u + 1}} (p : Direction s) :
    subterm s (Vertex.ofDirection p) = .pure ⟨⟩ := by
  refine FreeM.rec (motive := fun s ↦ ∀ p : Direction s,
    subterm s (Vertex.ofDirection p) = .pure ⟨⟩) (fun _ _ ↦ rfl) ?_ s p
  intro a ts ih p
  exact ih p.1 p.2

/-- Transport along a vertex preserves resolution: a family written against the subterm at a
vertex, its vertices translated into the environment, resolves against the environment as the
original family resolves against the subterm. -/
theorem link_map_append (env : P.FreeM Γ) (v : Vertex env)
    (d : E → P.FreeM (Vertex (subterm env v))) :
    link (fun i ↦ (d i).map v.append) (subterm env) = link d (subterm (subterm env v)) := by
  funext i
  simp only [link, ← FreeM.bind_pure_comp, FreeM.bind_assoc, Function.comp_apply,
    FreeM.pure_bind, subterm_append]

end Geb.Definition

end
