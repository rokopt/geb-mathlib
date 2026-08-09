/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The signature of Cobham's class of bitstring functions

The syntactic signature of a Cobham-style function algebra on bitstrings, whose
recursion scheme is bounded recursion on notation [Cobham1965], together with its
interpretation over every `sig`-tree. Terms are built from a constant zero,
projections, two successors, a smash and a concat generator, and are closed under a
composition and a bounded recursion. `sig` fixes the shape of the syntax alone — each
constructor's arity and the arity relation its subterms must satisfy — and `eval`
gives the meaning of any tree respecting that relation. Cobham's class itself is the
subtype `C` of trees whose recursions additionally respect the length bound the
scheme imposes, carrying `eval` down to `C.eval`.

## Main definitions

* `Cobham.Shape` — the seven constructor forms, with their arities as parameters.
* `Cobham.Direction` — the subterm positions of a shape.
* `Cobham.rc` — the arity each subterm position must carry.
* `Cobham.q` — the arity a shape produces.
* `Cobham.sig` — the signature, as a slice polynomial functor over `ℕ`.
* `Cobham.sigFinitary` — every shape has finitely many directions.
* `Cobham.Sem` — the meaning of an arity: a function of an environment of bitstrings.
* `Cobham.transport` — transport of a meaning along an equality of arities.
* `Cobham.evalRec` — the recursion `boundedRec` performs on its recursion variable.
* `Cobham.evalValue` — the meaning of one node from its children's meanings.
* `Cobham.evalStep` — `evalValue` as a slice algebra.
* `Cobham.eval` — the interpretation of a `sig`-tree, by the slice W-type's
  eliminator.
* `Cobham.arity` — the arity of a `sig`-tree.
* `Cobham.RecBoundedValue` — the length bound one node imposes.
* `Cobham.RecBounded` — `RecBoundedValue` at every node, hereditarily.
* `Cobham.C` — Cobham's class: the trees satisfying `RecBounded`.
* `Cobham.C.arity` — the arity of an expression.
* `Cobham.COf` — the expressions of a given arity.
* `Cobham.C.eval` — the meaning of an expression, at its own arity.
* `Cobham.concatRaw` / `Cobham.smashRaw` — the two generators as single nodes.
* `Cobham.concatOf` / `Cobham.smashOf` — those nodes as expressions of arity two.
* `Cobham.smashFreeBool` — whether no `smash` node occurs anywhere in a raw tree.
* `Cobham.SmashFree` — the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, excluding
  the `smash` generator.

## Main statements

* `Cobham.fst_eval` — the index component of a tree's interpretation is its arity.
* `Cobham.recBounded_mk` — `RecBounded` unfolded one level, on a raw node.

## Implementation notes

`concatRaw` and `smashRaw` are named apart from the expressions built on them
because instance search finds `Decidable (sig.WValid w)` when `w` is a constant but
not when it is a literal `WType.mk` application, with or without an ascription, so
`decide` discharges admissibility only of a named tree.

`Direction`, `rc` and `q` are `@[reducible]`. Instance search does not delta-reduce a
semireducible definition, and `sigFinitary` resolves `FinEnum (sig.B a)` against the
literal `Direction a` each branch produces.

`sigFinitary`'s `comp` branch resolves `FinEnum (Unit ⊕ Fin m)` through the
choice-free `FinEnum.unit` and `FinEnum.finSum`, and its other branches resolve
`FinEnum (Fin n)` through the choice-free `FinEnum.finFin`. Those instances are
`scoped` in `namespace FinEnum`; this module's `open scoped FinEnum` is required for
them to win resolution over mathlib's `Classical.choice`-dependent counterparts,
which `lake lint` rejects.

A bitstring is represented as a `List Bool` whose head is the word's last bit, so
`succ b` prepends by consing `b`. `evalValue` is a separate definition from
`evalStep` because the match on `Shape` must generalize the compatibility hypothesis,
which arrives bundled in `SliceDomPFunctor.Obj`. A child's meaning carries the index
it was built at rather than the index `rc` prescribes, equal but not definitionally
so; `transport` carries it across, with the motive of `▸` fixed once instead of at
each use site. `evalValue`'s `boundedRec` clause does not consult its bound child's
meaning: the bound is a side condition on admissibility, imposed by
`RecBoundedValue`, not part of a tree's value.

`eval` is a slice morphism, so the index it returns agrees with `arity` only by
`SlicePFunctor.W.comp_elim`, a `funext` theorem; `C.eval` is therefore
`transport (fst_eval _) (eval _).2` rather than the second projection alone, and the
index equation `RecBoundedValue` consumes is the node's compatibility composed with
`fst_eval`. `recBounded_mk` is stated on the raw `⟨WType.mk a f, _⟩` rather than on
`SlicePFunctor.W.mk`, at which the `WType.rec` of `RecProp` iota-reduces and the
unfolding is definitional; the index equation is a hypothesis, definitional proof
irrelevance making the choice of proof term immaterial. `C.arity` and `C.eval`
qualify `arity` and `eval` because the namespace of the declaration being elaborated
is in scope, which would otherwise make each body self-referential.

## References

* [Cobham1965]
* [HeraudNowak2011]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, W-type, polynomial functor
-/

namespace Cobham

open scoped FinEnum

public section

/-- The seven constructor forms of Cobham's class, each carrying its arities as
parameters: `zero` the constant empty bitstring; `proj n i` the `i`th of `n`
variables; `succ b` the successor appending the bit `b`; `smash` and `concat` the two
bitstring generators; `comp n m` the composition of an `m`-ary expression with `m`
`n`-ary argument expressions; `boundedRec n` the bounded recursion producing arity
`n + 1`. -/
inductive Shape
  | zero
  | proj (n : ℕ) (i : Fin n)
  | succ (b : Bool)
  | smash
  | concat
  | comp (n m : ℕ)
  | boundedRec (n : ℕ)

/-- The subterm positions of a shape. The five base forms — `zero`, `proj`, `succ`,
`smash` and `concat` — have none, `smash` and `concat` being generators rather than
recursive constructions; `comp` has its head and its `m` argument expressions;
`boundedRec` has four, its base, its two step expressions and its bound. -/
@[expose, reducible] def Direction : Shape → Type
  | .zero => Fin 0
  | .proj _ _ => Fin 0
  | .succ _ => Fin 0
  | .smash => Fin 0
  | .concat => Fin 0
  | .comp _ m => Unit ⊕ Fin m
  | .boundedRec _ => Fin 4

/-- The arity each subterm position must carry: the hypotheses of the arity relation
of bounded recursion on notation [Cobham1965]. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ
  | .zero, i => i.elim0
  | .proj _ _, i => i.elim0
  | .succ _, i => i.elim0
  | .smash, i => i.elim0
  | .concat, i => i.elim0
  | .comp _ m, .inl () => m
  | .comp n _, .inr _ => n
  | .boundedRec n, ⟨0, _⟩ => n
  | .boundedRec n, ⟨1, _⟩ => n + 2
  | .boundedRec n, ⟨2, _⟩ => n + 2
  | .boundedRec n, _ => n + 1

/-- The arity a shape produces: the conclusions of the arity relation of bounded
recursion on notation [Cobham1965]. -/
@[expose, reducible] def q : Shape → ℕ
  | .zero => 0
  | .proj n _ => n
  | .succ _ => 1
  | .smash => 2
  | .concat => 2
  | .comp n _ => n
  | .boundedRec n => n + 1

/-- The signature of Cobham's class as a slice polynomial functor over `ℕ`, the index
being the arity. -/
@[expose] def sig : SlicePFunctor ℕ ℕ where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

/-- Every shape has finitely many directions, which is what makes admissibility of a
`sig`-tree decidable. The branches ascribe their instances explicitly: instance
search stops at reducible transparency on the projection `sig.B a`, so a bare
`inferInstance` does not find them. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .zero => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .smash => inferInstanceAs (FinEnum (Fin 0))
  | .concat => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ m => inferInstanceAs (FinEnum (Unit ⊕ Fin m))
  | .boundedRec _ => inferInstanceAs (FinEnum (Fin 4))

/-- The meaning of an arity: a function of an environment of bitstrings, one per
argument, returning a bitstring. -/
@[expose] def Sem : ℕ → Type := fun n ↦ (Fin n → List Bool) → List Bool

/-- Transport of a meaning along an equality of arities. Named so that the motive of
`▸` is fixed once rather than inferred at each use in `evalValue`. -/
@[expose] def transport {i j : ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v

/-- The recursion `boundedRec` performs on its recursion variable, by `List.rec`,
matching [HeraudNowak2011]'s `Rec` (`f(y·i, x) = h_i(y, f(y,x), x)`), not
[Strahm2003]'s last-argument form. The base case is the empty bitstring; a step
consumes the low bit `b`, passes the remaining bitstring `v` as the new recursion
variable, and passes the recursive value alongside it. -/
@[expose] def evalRec {n : ℕ} (g : Sem n) (h₀ h₁ : Sem (n + 2)) :
    List Bool → Sem n :=
  List.rec g (fun b v ih x ↦
    (if b then h₁ else h₀) (Fin.cons v (Fin.cons (ih x) x)))

/-- The meaning of one node, from its children's meanings and the proof that each
child's index is the one `rc` prescribes. A separate definition from `evalStep`
because the match on `Shape` must generalize that proof.

The bitstring generators read the ambient environment directly, `Direction` being
`Fin 0` for each: `zero` returns the empty bitstring; `proj n i` returns the `i`th
argument; `succ b` prepends `b` to the argument. `smash` and `concat` are Cobham's
two generators: `smash` marks its result with a leading `true`, so
`|#(a, b)| = |a| · |b| + 1`; `concat` reads its second argument as the earlier part
of the word and its first as the later part, consistent with the list head
representing the word's last bit. `comp` applies its head's meaning to the argument
expressions' meanings, each read at the ambient environment. `boundedRec` performs
`evalRec` on its recursion variable, its base and two step children supplying `g`,
`h₀` and `h₁`. -/
@[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .zero, _, _ => fun _ ↦ []
  | .proj _ i, _, _ => fun x ↦ x i
  | .succ b, _, _ => fun x ↦ b :: x 0
  | .smash, _, _ => fun x ↦ true :: List.replicate ((x 0).length * (x 1).length) false
  | .concat, _, _ => fun x ↦ x 1 ++ x 0
  | .comp _ _, c, h => fun x ↦
      transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x)
  | .boundedRec _, c, h => fun x ↦
      evalRec (transport (h 0) (c 0).2) (transport (h 1) (c 1).2)
        (transport (h 2) (c 2).2) (x 0) (Fin.tail x)

/-- `evalValue` as an algebra for `sig` in the slice over `ℕ`. Returning the shape's
own output index as the first component makes the eliminator's coherence obligation
hold by `rfl`. -/
@[expose] def evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The interpretation of a `sig`-tree: its arity together with its meaning at that
arity, by the slice W-type's eliminator. -/
@[expose] def eval : sig.W → Σ n, Sem n :=
  SlicePFunctor.W.elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl

/-- The arity of a `sig`-tree. -/
@[expose] def arity : sig.W → ℕ := sig.wIndex

/-- The index component of a tree's interpretation is the tree's arity. `eval` is a
morphism in the slice over `ℕ`, so composing it with the index projection gives
`sig.wIndex`; this is that equation read at a single tree, the form `transport`
consumes. -/
theorem fst_eval (z : sig.W) : (eval z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl) z

/-- The recursion bound of one node, from its children and the proof that each
child's evaluated index is the one `rc` prescribes. It is vacuous at every shape but
`boundedRec`, where it is the side condition of bounded recursion on notation
[Cobham1965]: at every environment, the recursion's value is no longer than the
meaning of the bound child. `evalValue`'s `boundedRec` clause supplies the bounded
quantity, read at the same environment. -/
@[expose] def RecBoundedValue : (a : Shape) → (c : Direction a → sig.W) →
    (∀ b, (eval (c b)).1 = rc a b) → Prop
  | .zero, _, _ => True
  | .proj _ _, _, _ => True
  | .succ _, _, _ => True
  | .smash, _, _ => True
  | .concat, _, _ => True
  | .comp _ _, _, _ => True
  | .boundedRec n, c, h => ∀ x : Fin (n + 1) → List Bool,
      (evalRec (transport (h 0) (eval (c 0)).2) (transport (h 1) (eval (c 1)).2)
          (transport (h 2) (eval (c 2)).2) (x 0) (Fin.tail x)).length ≤
        (transport (h 3) (eval (c 3)).2 x).length

/-- The admissibility of a `sig`-tree: every node satisfies `RecBoundedValue`,
hereditarily. The fold over the tree is carried by the slice W-type's `Prop`-valued
paramorphism `SlicePFunctor.W.RecProp`; the index equation `RecBoundedValue` requires
is the node's compatibility (`SliceDomPFunctor.compatible_iff`) composed with
`fst_eval`, since compatibility constrains a child's `wIndex` rather than the index
its interpretation carries. -/
@[expose] def RecBounded : sig.W → Prop :=
  SlicePFunctor.W.RecProp (fun x ih ↦
    RecBoundedValue x.1.1 x.1.2
        (fun b ↦ (fst_eval (x.1.2 b)).trans
          ((sig.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2 b)) ∧
      ∀ b, ih b)

/-- One-level unfolding of `RecBounded` on a raw node `⟨WType.mk a f, hv⟩`: the
root's `RecBoundedValue` together with admissibility of every child. Stated on the
raw tree rather than on `SlicePFunctor.W.mk`, so that `WType.rec` iota-reduces and
the equation is definitional. -/
theorem recBounded_mk (a : Shape) (f : Direction a → sig.toPFunctor.W)
    (hv : sig.WValid (WType.mk a f))
    (h : ∀ b, (eval ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩).1 = rc a b) :
    RecBounded ⟨WType.mk a f, hv⟩ =
      (RecBoundedValue a (fun b ↦ ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩) h ∧
        ∀ b, RecBounded ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩) :=
  rfl

/-- Cobham's class as a type of expressions: the `sig`-trees whose recursions
respect the length bound. -/
@[expose] def C : Type := { e : sig.W // RecBounded e }

/-- The arity of an expression, that of the underlying tree. -/
@[expose] def C.arity (e : C) : ℕ := Cobham.arity e.1

/-- The expressions of a given arity. -/
@[expose] def COf (n : ℕ) : Type := { e : C // e.arity = n }

/-- The meaning of an expression, at its own arity. The underlying tree's
interpretation carries the index `eval` computed, equal to the arity by `fst_eval`
but not definitionally so, hence the `transport`. -/
@[expose] def C.eval (e : C) : Sem e.arity :=
  transport (fst_eval e.1) (Cobham.eval e.1).2

/-- The `concat` generator as a single node, its `Direction` being empty. -/
@[expose] def concatRaw : sig.toPFunctor.W := WType.mk .concat Fin.elim0

/-- The `concat` generator as an expression of arity two, its `RecBoundedValue`
vacuous and its hereditary conjunct empty. -/
@[expose] def concatOf : COf 2 :=
  ⟨⟨⟨concatRaw, by decide⟩, ⟨trivial, fun b ↦ b.elim0⟩⟩, rfl⟩

/-- The `smash` generator as a single node, its `Direction` being empty. -/
@[expose] def smashRaw : sig.toPFunctor.W := WType.mk .smash Fin.elim0

/-- The `smash` generator as an expression of arity two, as `concatOf`. -/
@[expose] def smashOf : COf 2 :=
  ⟨⟨⟨smashRaw, by decide⟩, ⟨trivial, fun b ↦ b.elim0⟩⟩, rfl⟩

/-- Whether no `smash` node occurs anywhere in a raw tree. -/
@[expose] def smashFreeBool : sig.toPFunctor.W → Bool :=
  WType.elim Bool fun x ↦
    match x with
    | ⟨.smash, _⟩ => false
    | ⟨_, c⟩ => decide (∀ b, c b = true)

/-- An expression of the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, which
[Strahm2003] Theorem 1(2) contains in the functions computable
simultaneously in polynomial time and linear space. Hereditary: a
top-node test would not exclude `#` from subterms. -/
@[expose] def SmashFree (e : C) : Prop := smashFreeBool e.1.1 = true

/-- `SmashFree` is decidable, its `Bool` equation unfolded explicitly since a bare
`inferInstance` does not see through the definition. -/
instance (e : C) : Decidable (SmashFree e) :=
  inferInstanceAs (Decidable (smashFreeBool e.1.1 = true))

end

end Cobham
