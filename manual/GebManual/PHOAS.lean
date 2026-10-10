/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.PHOAS.Category
import Geb.Prototypes.PHOAS.Cofree
import Geb.Prototypes.PHOAS.Paranatural
import GebTests.Prototypes.PHOAS

/-! # PHOAS and the universal properties of binding syntax

The polynomial profunctor, its pointwise free monad and end, and the
initial algebra on context-indexed families. The chapter distinguishes
these universal properties and relates them to operations on syntax
with variable binding.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Geb.PHOAS Geb.PHOAS.PProfunctor

#doc (Manual) "PHOAS and the universal properties of binding syntax" =>

The free-monad/end construction implements an initial algebra for a
binding signature on families of types indexed by contexts. Its closed
terms are the empty-context component of that initial algebra. For the
polynomial profunctors considered here, this is proved by
{name}`scopedIsInitial` and {name}`endIsoInitial`:

```
F(X, Y) = Free(P(X, -))(Y)
E       = ∫ X. F(X, X)
E       ≅ (μ L)(∅)
```

Here `L` is an endofunctor on context-indexed families, specified below
independently of `F` and `E`. Thus initiality specifies the syntax and
the free-monad/end construction supplies an implementation. The
specification includes open terms: the closed type by itself does not
retain the contexts needed to describe the bodies of binders.

The starting point is Edward Kmett's
[PHOAS For Free](https://comonad.com/reader/2013/phoas/)
{citep Kmett2013}[]. The
[School of Haskell version](https://www.schoolofhaskell.com/user/edwardk/phoas)
includes the sections on taking an end and on the Church representation
of the free monad. This development uses polynomial trees for the free
monad and proves the compatibility condition defining the end
explicitly. The formal modules and executable examples appear at the
end of this chapter; declaration references link to their code.

# Which property characterizes which object

The constructions have different carriers and different morphisms.
Keeping them separate specifies what a uniqueness theorem permits.

:::table +header
*
  * Construction
  * Universal property
  * Computational meaning
*
  * `F(X, Y)`, with `X` fixed
  * Free `P(X, -)`-algebra on `Y`; initial algebra for `Z ↦ Y + P(X, Z)`
  * Trees with leaves in `Y`, and substitution for those leaves
*
  * `E = ∫ X. F(X, X)`
  * Universal compatible family of diagonal components
  * Closed syntax uniform in the representation of variables
*
  * `T(Γ) = Scoped Γ`, as a functor of `Γ`
  * Initial `L`-algebra in the category of context functors
  * Open syntax, structural recursion under binders, and unique folds
*
  * `E ≅ T(∅)`
  * Empty-context component of any initial `L`-algebra
  * Closed terms characterized through the specification of open terms
:::

The last row is the characterization furnished by
{name}`endIsoInitial`. It does not assert that taking the
empty-context component preserves initial objects in some category of
closed algebras. The initial object in the third row is an entire
functor equipped with constructors.

# Polynomial directions describe binding arities

A {name}`PProfunctor` consists of operation positions `A` and a
polynomial functor of directions at each position. Write that inner
polynomial as

```
Dₐ(X) = Σ b : Bₐ, (Cₐᵦ → X)
P(X, Y) = Σ a : A, (Dₐ(X) → Y).
```

In the code, `A` is `P.A`, `Bₐ` is `(P.B a).A`, and `Cₐᵦ` is
`(P.B a).B b`. The outer position selects a constructor; `b` selects
one of its recursive arguments; and `Cₐᵦ` describes the variables
bound in that argument. An element of `Dₐ(X)` chooses an argument and
assigns an `X`-value to every variable it binds.

The interpretation {name}`PProfunctor.Obj` is contravariant in `X`
because the directions occur as a function domain. For `f : X' → X`
and `g : Y → Y'`, {name}`dimap` maps `(a, k)` to
`(a, g ∘ k ∘ Dₐ(f))`. The categorical packaging is
{name}`profunctor`.

For Kmett's untyped lambda syntax, {name}`Kmett.signature` has two
positions. Application has two arguments, each binding no variables;
abstraction has one argument, binding one variable. Consequently,
{name}`Kmett.objEquiv` gives

```
P(X, Y) ≅ (Y × Y) + (X → Y).
```

The `X` in an abstraction is a variable supplied to its body; `Y`
stands for a recursive result. Separating these parameters makes
`P(X, -)` an ordinary polynomial functor. Variables as syntax nodes
will come from the free monad's leaves.

# The pointwise free monad

Fix `X`. The definition {name}`Free` reuses CSLib's polynomial free
monad, with unfolding {name}`Free.unfold`:

```
F(X, Y) ≅ Y + P(X, F(X, Y)).
```

For every type `Z`, a map `v : Y → Z` interpreting leaves and an
algebra `α : P(X, Z) → Z` determine a map
`fold(v, α) : F(X, Y) → Z`. It sends a leaf to its interpretation
and an operation to `α` applied to its interpreted children.
{name}`Free.fold` constructs the map;
{name}`Free.fold_pure` and {name}`Free.fold_liftBind` state its
constructor equations; {name}`Free.fold_unique` proves that these
equations determine it uniquely. This is the free-algebra universal
property, with both `X` and the map on generators `Y` specified.

Monad bind substitutes trees for leaves while keeping `X` fixed.
Input renaming {name}`Free.comap` changes `X` contravariantly.
It commutes with output renaming ({name}`Free.comap_map`) and with
bind ({name}`Free.comap_bind`), so the pointwise free monads assemble
into {name}`freeProfunctor`.

For lambda syntax, a binder has type
`X → F(X, Y)`, and a variable constructor has type `Y → F(X, Y)`.
Using a bound variable as a leaf brings the two parameters together.
{name}`Kmett.identity` and {name}`Kmett.exampleTerm` package the
resulting families for `λx. x` and `λx. λy. x y` as closed ends.

There is also a fibrewise reading of the pointwise universal property.
For fixed `Y`, consider the category of algebras of
`Z ↦ Y + P(X, Z)` at each `X`. A map `f : X' → X` induces a natural
transformation `P(X, -) → P(X', -)`, and hence restriction of
algebras from the `X'` category to the `X` category. Initiality then
gives a comparison from `F(X, Y)` to the restricted algebra
`F(X', Y)`; its underlying map is {name}`Free.comap`. This explains
the coherence of the pointwise construction. A stable fibred
initial-object assertion would additionally require restriction to
preserve initial objects. Neither that assertion nor a bundled
fibration is part of the formal development.

# The end imposes uniformity

The type {name}`End` consists of families `eₓ : F(X, X)` satisfying
the wedge equation, for every function `f : X → Y`:

```
map f (eₓ) = comap f (eᵧ)       in F(X, Y).
```

Thus the positive and negative ways of changing the variable type
agree. This is the explicit condition used here for PHOAS uniformity.
Lean's type quantifier alone is not taken to imply it, and no
parametricity axiom is assumed. The statement concerns this proved
dinaturality condition, without claiming an equivalence with a
separate relational-parametricity semantics of a programming language.

The end universal property concerns maps into this family. If a type
`S` has maps `sₓ : S → F(X, X)` satisfying the wedge equation
pointwise, there is exactly one map `S → E` whose components are the
`sₓ`. {name}`endEquiv` identifies the explicit family with mathlib's
end, and {name}`endIsLimit` supplies its limiting-wedge property.
This property is available for an end independently of a syntax
interpretation. It does not itself supply structural recursion.

For a chosen `α : P(X, X) → X`, {name}`End.iter` evaluates a closed
term by instantiating its variable type at `X` and applying the
pointwise fold with leaf map `id`. This is the operation corresponding
to Kmett's `iter0`. Its existence does not say that `E` is initial in
a category whose objects are the maps `P(X, X) → X`.

# Contexts recover the open subterms

A context `Γ` is a type of available variables. A scoped term supplies
a component

```
tₓ : (Γ → X) → F(X, X)
```

for every `X`, with compatibility

```
map f (tₓ env) = comap f (tᵧ (f ∘ env)).
```

This is {name}`Scoped`. The environment `env : Γ → X` assigns
representatives to the available variables. A variable term is
{name}`Scoped.var`: it selects one variable from that environment.
{name}`Scoped.emptyEquivEnd` identifies `T(∅)` with `E`, since an
empty context has exactly one environment into every type.

An operation's argument indexed by `b` may use both the surrounding
variables `Γ` and its newly bound variables `Cₐᵦ`. Its context is
therefore `Γ + Cₐᵦ`. The constructor {name}`Scoped.node` combines
the surrounding environment with the assignment supplied to that
argument. The name “scoped” refers to this explicit account of the
variables available in each subterm.

The equivalence {name}`Scoped.unfold` proves the one-layer equation

```
T(Γ) ≅ Γ + Σ a : A, Π b : Bₐ, T(Γ + Cₐᵦ).
```

Uniformity is used to recover these constructors. The component at
`X = Γ` with the identity environment determines whether the term is
a variable or an operation. In the variable case, compatibility forces
all components to select that same context variable. In the operation
case, polynomial directions split each child into an argument index
and an assignment of bound variables, producing the extended-context
family. These are the claims implemented by
{name}`Scoped.eq_var_of_eval`, {name}`Scoped.child`, and the two
inverse laws of {name}`Scoped.unfold`.

For closed lambda terms, {name}`Kmett.closedUnfold` specializes the
equation to

```
E ≅ (E × E) + T(1).
```

An abstraction body is open in one variable. Replacing `T(1)` by an
unrestricted function space `E → E` changes the equation and the
object being specified.

# Initiality of the context family

Separate the node operator from its variable summand. For a family
`M`, context extension and the two operators are

```
δC(M)(Γ) = M(Γ + C)
H(M)(Γ)  = Σ a : A, Π b : Bₐ, δCₐᵦ(M)(Γ)
V(Γ)     = Γ
L(M)     = V + H(M).
```

These are {name}`ContextExtension`, {name}`BindingNode`, and
{name}`BindingLayer`. Here `V` is the identity functor on contexts,
regarded as a fixed variable family, rather than the identity
endofunctor on families. Their definitions mention neither ends
nor free monads. The functor {name}`contextExtensionFunctor` realizes
`δC` by precomposition. A context map `f : Γ → Δ` acts on variables by `f`
and on argument `b` through `M(f + id)` at the extended context.
A natural transformation `M → N` acts separately on every recursive
argument. These actions define {name}`bindingFunctor` on the
category of covariant functors from types to types.

An `L`-algebra has a context functor `M`, variable maps
`vΓ : Γ → M(Γ)`, and operation maps
`nΓ,a : (Π b, M(Γ + Cₐᵦ)) → M(Γ)`, natural in `Γ`.
A morphism of such algebras is a natural transformation preserving
both kinds of constructor. {name}`scopedAlgebra` is the algebra
carried by `T`. The theorem {name}`scopedIsInitial` states that for
every `L`-algebra there exists exactly one such morphism from `T`.

The proof needs more than the one-layer isomorphism. A fixed-point
equation alone does not distinguish inductive from coinductive syntax.
Here {name}`Scoped.erase` interprets every variable in the singleton
type. The result is an ordinary well-founded free-monad tree, and each
scoped child erases to one of its subtrees. Recursion on that tree
gives {name}`Scoped.recOn`, including recursive hypotheses at all the
extended contexts. It supplies {name}`Scoped.fold`; constructor
preservation determines the fold uniquely by
{name}`Scoped.fold_unique`. Naturality follows from
{name}`Scoped.fold_rename`, and the categorical wrapper packages
these facts as initiality.

The fold theorem is also useful before supplying functor structure:
{name}`Scoped.fold_unique` applies to arbitrary target families with
the indicated variable and operation maps. The categorical theorem
adds the renaming actions and naturality appropriate to models of
binding syntax.

This places the construction in the context-indexed approach to
binding of Fiore, Plotkin and Turi {citep FiorePlotkinTuri1999}[].
Their Theorem 2.1 characterizes syntax for a binding signature as the
free signature algebra on the presheaf of variables, equivalently as
an initial algebra after adjoining that variable summand. Their
presentation uses finite contexts and finite binding arities. Here
contexts are all types in a universe, arities may be infinite, and the
proved result identifies the explicit free-monad/end family with an
initial binding algebra. Its tree representation is described below;
interoperability with a separate named-syntax implementation or the
Haskell `bound` library is not part of the formalization.

The exact universe condition matters. Contexts and binder arities
`Cₐᵦ` belong to `Type u`, the universe quantified over in the scoped
family. Operation positions and argument indices may have independent
universes `uA` and `uB`. The categorical initiality theorem uses
functors

```
Type u ⥤ Type (max uA uB (u + 1)),
```

whose value universe accommodates the end over `Type u`.
{name}`liftedFreeProfunctor` makes the corresponding lift for
mathlib's end. The theorem imposes no finiteness condition on the
signature; well-founded trees with infinite branching are included.

# Coherent families and their tree representation

The compatibility equation has a representation theorem in addition
to its initiality interpretation. For a single signature layer,
{name}`ScopedObj.equiv` states

```
ScopedObj Γ ≃ H(V)(Γ) = Σ a : A, Π b : Bₐ, (Γ + Cₐᵦ).
```

A family chooses an operation and, at each argument, either a
surrounding variable or a newly bound variable. The family then
substitutes its supplied environments into those choices.
The compatibility condition is paranaturality from the covariant
representable `Hom(Γ, -)` to `P`. With a covariant source, the
dinatural and strong-dinatural conditions coincide
{citep Neumann2023}[], Definition 3 and Note 6. This restricted
representation does not use a general diYoneda theorem.

For full expressions the target is already `F(X, X)`, and
{name}`Scoped.equivTerm` proves

```
Scoped Γ ≃ Term P Γ.
```

The right side contains no compatibility predicate. Its operation
shape is an ordinary polynomial free-monad tree. A leaf label selects
a variable from the context obtained by adjoining the binders along
its path. {name}`Term.node` accepts whole terms at the extended
contexts; {name}`Term.var` supplies leaves. The conversion
{name}`Term.toScoped` constructs the coherent family, and the
equivalence proves that every coherent family arises this way.
{name}`Kmett.exampleTree_toScoped` identifies the tree construction
of `λx. λy. x y` with its explicit PHOAS family.

Thus a lambda body can be supplied as a term in `Γ + 1`. The client
need not supply a metalanguage function on expressions or a proof of
its uniformity. This is an intrinsic scope representation: the type
records which variables may occur. Explicit injections still record
how variables sit in successively extended contexts; the representation
theorem does not itself supply surface notation that hides them.

The initiality statement reads `T ≅ μ M. (V + H(M))`, or equivalently
that `T` is the free `H`-algebra on `V`. A free-monad construction on
the category of context families would express it as `H*(V)`.
This is distinct from the pointwise monad `F(X, -)`. A monad of
substitution on the family `T` is another structure again, discussed
below. These constructions have different objects as their arguments.

# Operations on binding syntax

For lambda syntax the binding operator, up to the empty-context
coproduct identifications, is

```
L(M)(Γ) ≅ Γ + (M(Γ) × M(Γ)) + M(Γ + 1).
```

The recursive argument of abstraction is already a result in the
extended context. A fold can therefore inspect or interpret the body
without choosing a concrete representation for its bound variable.
This provides structural recursion for analyses and translations over
PHOAS terms.

The constructor equations {name}`Scoped.fold_var` and
{name}`Scoped.fold_node` are the computation rules. The uniqueness
theorem says that two families of functions satisfying those same
equations agree. {name}`Scoped.fold_fusion` derives the usual fusion
law: composing a fold with a constructor-preserving map is the fold
into the target algebra. These are laws of the specified algebra,
independent of its free-monad/end implementation.

Renaming is {name}`Scoped.rename`. Under a binder it acts by
`f + id`, changing the surrounding variables and retaining the newly
bound variables ({name}`Scoped.rename_node`). Context functions
include injections for weakening, permutations for exchange, and
noninjective maps identifying variables. Identity and composition are
proved by {name}`Scoped.rename_id` and {name}`Scoped.rename_comp`.
If a target interpretation respects these actions,
{name}`Scoped.fold_rename` proves that folding commutes with renaming.

The executable examples make the context distinction observable.
{name}`GebTests.PHOAS.scopedCount` counts operation nodes by the
scoped fold: `λx. x` has one and `λx. λy. x y` has three.
{name}`GebTests.PHOAS.freeVars` instead takes values in `List Γ`.
It concatenates the lists at application and discards the newly bound
variable at abstraction. The closed example has no free variables.
Its outer abstraction body has one free variable; renaming that
variable to `7` yields the list containing `7`, while the inner bound
variable is still discarded.

The pointwise free monad already has substitution for its positive
leaves. A substitution operation on the scoped family must additionally
account for context extension, retaining new bound variables while
weakening substituted terms. A scoped substitution operation and its
laws have not been added here. The fold and induction principles
provide tools for that development; the existing monad instance alone
is not a formalization of those scoped laws. The syntax also has no
quotient imposing beta or eta equations.

# Strong HOAS, weak HOAS, and admissible functions

Kmett's strong/weak distinction concerns a binder's input type:
strong HOAS accepts an expression, whereas weak HOAS accepts a
variable that must be injected into the expression type. Moving that
input to a separate parameter removes the recursive datatype from
negative position {citep Kmett2013}[]. It changes the substitution
interface, not the intended collection of object-language terms.

An unrestricted function `T(Γ) → T(Γ)` can inspect the syntax of its
argument. That is useful for a metaprogram but need not describe an
object-language binder. For Kmett's untyped syntax, take the distinct closed terms
`I = λx. x` and `K = λx. λy. x`, regarded in any context, and define

```
g(t) = I    if t has an application at its root
g(t) = K    otherwise.
```

This total operation preserves well-scopedness and commutes with
renaming: renaming leaves the root constructor unchanged. Nevertheless,
`g(var x) = K` and `g(app p q) = I`. A putative binder body recovered
by supplying `var x` would be `K`; substituting `app p q` into that
body would still give `K`. Applying the original host function instead
gives `I`. The operation is therefore not an admissible binder if
host application is meant to implement syntactic substitution.
No divergence or unsafe host-language feature is needed for this
counterexample.

The relevant meaning of correctness is adequacy as binding syntax,
including the behavior of substitution. Merely returning well-scoped
terms, or commuting with renamings, is weaker. Correct analyses,
translations, and evaluation procedures need not themselves be binder
bodies. Equations on object terms also matter: this development
represents raw syntax with intrinsic scope, without a beta/eta quotient.

Restrictions on the host function space are established practice.
Washburn and Weirich exclude inspection of embedded arguments through
an interface using abstract types and polymorphism
{citep WashburnWeirich2003}[], Section 2.1. Their Section 3 distinguishes
iteration laws from adequacy. Chlipala's PHOAS separates variable types
from syntax and uses an explicit relational well-formedness condition
in its metatheory {citep Chlipala2008}[], Sections 2.1 and 3.1.
The meaning of an admissible host function depends on that language
and its restrictions; it is not determined by the arrow type alone.

The equivalence with {name}`PProfunctor.Term` establishes adequacy for
the particular coherent weak families defined here. It does not classify
inhabitants of an unrestricted strong-HOAS recursive type, nor prove
that paranaturality always coincides with relational parametricity.
For the fixed binding signature, it leaves no missing tree syntax for
an adequate strong representation to add. Strong HOAS can still offer
a different interface and substitution implementation, and host
functions can express more general metaprograms. Neither observation
requires additional admissible object-language terms. The equivalence
constrains extensional values, not the source code of their generators:
a computation may produce a coherent family without being written
as a sequence of constructor calls.

## The substitution law that characterizes open terms

There is a precise mathematical version of the claim that an
admissible function is substitution into a fixed expression. The
following argument assumes a monad `T` on sets; its application to
scoped syntax requires the scoped substitution operation and monad
laws that are not yet formalized here.

Write `η` for variables and `σ* : T(X) → T(Y)` for substitution
along `σ : X → T(Y)`. For a set `A` of formal parameters, consider
a family

```
ΦX : (A → T(X)) → T(X).
```

Require compatibility with all substitutions, including substitutions
by composite terms:

```
ΦY(σ* ∘ ρ) = σ*(ΦX(ρ)).
```

Then the family is determined by the single open term
`t = ΦA(ηA) : T(A)`. Indeed, choose the substitution `ρ : A → T(X)`
in that equation. The unit law gives

```
ΦX(ρ) = ΦX(ρ* ∘ ηA) = ρ*(ΦA(ηA)) = ρ*(t).
```

Conversely, any `t : T(A)` defines such a family by substitution;
associativity gives the compatibility equation. Evaluation at `ηA`
recovers `t`, so these constructions are inverse. With `A = 1`,
these are exactly the families `T(X) → T(X)` satisfying this law.
The parameter may occur repeatedly or not at all in `t`.

This is ordinary Yoneda in the Kleisli category: its morphisms
`A → X` are functions `A → T(X)`, and `T(X)` is represented by the
singleton object. Apply the covariant Yoneda lemma to those two
representables; see {citep Riehl2016}[], Theorem 2.2.4 and
Definition 5.2.10. The argument specializes these standard results;
it requires no polynomial hypothesis or diYoneda principle.

This substitution law is a condition on term-valued operations.
The definition of {name}`Scoped` instead imposes compatibility on
families of variable environments into the mixed-variance `F`.
The two conditions have different types. The tree equivalence provides
the syntax on which to formulate the former; it does not silently
identify the two conditions. In particular, the root-inspecting `g`
above satisfies renaming naturality but fails substitution naturality.

# Abstraction as reclassification of free variables

Abstraction needs only renaming and a constructor. Choose a
classification `s : Γ → Δ + C`, where `Δ`
contains the variables to remain free and `C` labels those to bind.
For `t : T(Γ)`, renaming produces

```
rename s t : T(Δ + C).
```

This is a body that a constructor binding `C` can accept directly.
For a single lambda, `C = 1`. With decidable equality on variable
names, one possible classification is

```
sₓ(y) = inr ()    if y = x
sₓ(y) = inl y     otherwise

abstractₓ(t) = lam(rename sₓ t).
```

Here the remaining context is still the original variable type; an
explicit classification into a smaller `Δ` can instead remove the
selected variable from the context type. No equality decision is
needed when the classification is supplied directly. Existing binders
remain protected: {name}`Scoped.rename_node` lifts the map by the
identity on their newly bound variables. In this repository the free
case is on the left of `Γ + C` and the newly bound case on the right.
Reversing that coproduct is only a convention.

This operation is usually called abstraction. Bird and Paterson give
the same construction, using their context-extension map followed by
`Lam` {citep BirdPaterson1999}[], Section 4. It is distinct from monadic
`bind`, which substitutes expressions for free variables. Instantiating
a body `b : T(Γ + C)` with `k : C → T(Γ)` would use

```
instantiate(k, b) = b >>= [ηΓ, k].
```

Under an inner binder of arity `D`, a substitution `σ : Γ → T(Δ)`
must be lifted by

```
σ⁺(inl x) = rename inl (σ x)
σ⁺(inr d) = var (inr d).
```

These equations describe the intended scoped substitution API; they
are not additional implemented operations or proved monad laws.
They explain why merely applying the monad instance of `F(X, -)`
does not finish the construction. They also separate constructing a
body directly in an extended context from capturing a selected name
in an already constructed open term.

# Relation to bound and earlier representations

Kmett's slides {citep Kmett2012Bound}[] compare representations by
the operations they make available. The following table applies that
comparison to the syntax considered here.

:::table +header
*
  * Representation
  * Binder body
  * Main obligation
*
  * Named syntax
  * A term plus a chosen name
  * Manage freshness, capture avoidance, and alpha-equivalence
*
  * Globally fresh names
  * A term using a unique identifier
  * Maintain the freshness invariant and identifier supply
*
  * Numeric de Bruijn syntax
  * A term using relative binder depths
  * Maintain scope bounds and shift indices during substitution
*
  * Strong HOAS
  * A restricted host function on expressions
  * Justify admissibility and provide eliminators under binders
*
  * Parametric weak HOAS
  * A host function on abstract variables
  * Establish uniformity and support operations on open bodies
*
  * Context-extension syntax
  * A term in `T(Γ + C)`
  * Lift renaming and substitution through context extensions
:::

Kmett's stated preference for `bound` concerns working inside binder
bodies, using `Foldable` and `Traversable` for free variables, and
reducing opportunities for implementation mistakes
{citep Kmett2013}[]. His `Bound` article develops a reusable scope
transformer, simultaneous substitution, and the `Bound` class for
substitution through structures such as patterns
{citep Kmett2015Bound}[]. These are library and algorithmic concerns,
in addition to the question of which expressions can be represented.

The documented logical scope view is `f (Var b a)`, where `Var b a`
has a bound case `B b` and a free case `F a`. Taking `f = T`, `b = C`,
and `a = Γ` gives the same context extension as `T(Γ + C)`, after
swapping the coproduct. The optimized `Scope` representation stores
`f (Var b (f a))`: its free case can contain a whole subterm.
This enables constant-time lifting and lets instantiation retain such
a subterm without traversing it. The documentation's `fromScope`
distributes those placements to leaves; `toScope` goes the other way,
with `fromScope ∘ toScope = id`. They are not inverse on raw storage:
the opposite composite normalizes placements. The library's equality
comparison accounts for that distinction {citep KmettBoundScope2023}[].

Accordingly, {name}`Scoped.equivTerm` connects a coherent PHOAS
presentation to the ordinary scope-tree side of this design space.
It does not implement `bound`'s storage optimization or prove a cost
comparison. The free-variable fold and structural recursion supplied
here address some of the same usability concerns. A general
`Foldable`-style enumeration or decidable equality does not follow for
arbitrary signatures: argument sets may be infinite and labels need
not have decidable equality. Even for a finite signature, frontend
notation and efficient substitution remain separate implementation
questions.

There is therefore precedent for the representation, the abstraction
operation, and the strategy of restricting higher-order functions.
Bird and Paterson's nested datatype uses `Term (Incr Γ)` under a
lambda, where `Incr Γ` adjoins one variable, and develops its maps,
folds, and monad {citep BirdPaterson1999}[]. Fiore, Plotkin and Turi
give the corresponding algebraic account through context extension
{citep FiorePlotkinTuri1999}[]. Chlipala also discusses approaches
with a first-order implementation and a higher-order interface
{citep Chlipala2008}[], Section 5.

The specific result recorded here is the constructive equivalence
between explicitly coherent polynomial PHOAS families and binding
trees, together with initiality for the specified context operator.
It makes the scoping proof unnecessary for clients using the tree
constructors. This is not a priority claim for context-extension
syntax, nor a theorem that every useful function on terms is a
substitution into one fixed term. The latter characterization requires
the substitution law stated above.

# Diagonal fixed points and profunctor algebras

For Kmett's signature, {name}`Kmett.no_fixed_point` proves that no
type `X` satisfies `P(X, X) ≅ X`. In particular,
{name}`Kmett.end_not_fixed_point` rules out that equation for the
closed end. This does not conflict with `L(T) ≅ T`: the latter is an
equation in a category of context functors, with abstraction using
context extension.

For the indexing category with one object and only its identity,
[algebras for a profunctor](https://ncatlab.org/nlab/show/algebra+for+a+profunctor)
{citep NLabProfunctorAlgebra}[] give another candidate category.
Applied to `P`, its objects are pairs `(X, p)` with `p : P(X, X)`.
These are {name}`Diagonal`; a morphism `f : X → Y` satisfies
`P(id, f)(p) = P(f, id)(q)`. Such a morphism preserves the operation
position. Distinct positions therefore rule out initial and terminal
objects, as proved by {name}`not_isInitial` and
{name}`not_isTerminal`.

To make structure maps the objects instead, use the derived
profunctor

```
Aₚ(X, Y) = P(Y, X) → Y.
```

This is {name}`AlgebraObj`, packaged as {name}`algebraProfunctor`.
Its diagonal objects have the desired form `(X, α : P(X, X) → X)`.
The homomorphism condition for `f : X → Y` is

```
f ∘ α ∘ P(f, id) = β ∘ P(id, f)     on P(Y, X).
```

It is {name}`Algebra.Hom`. Even in this category Kmett's signature
has no initial object: {name}`Kmett.no_initial_algebra`, packaged
as {name}`kmett_not_isInitial`, proves the obstruction. Therefore
the interpreter {name}`End.iter` does not witness initiality here.
The binding-algebra category instead keeps an entire context family
and requires its maps to preserve variables, binding operations, and
renaming.

# The coinductive question and the scope of the result

The pointwise cofree candidate has carrier {name}`Cofree`, built
from the repository's M-types, with equation

```
C(X, Y) ≅ Y × P(X, C(X, Y)).
```

Every node carries a positive label; {name}`counit` reads the root
label. Thus a diagonal family `∀ X, C(X, X)` would supply an element
of the empty type at its empty-type component.
{name}`cofree_family_empty` proves that even such a family without
compatibility is impossible. An end of this diagonal family cannot
provide inhabited coinductive binding syntax.

The derived coalgebra profunctor {name}`coalgebraProfunctor` has
values `X → P(X, Y)` and diagonal objects `X → P(X, X)`.
{name}`kmett_not_isTerminal` rules out a terminal object for Kmett's
signature in that category as well. Neither obstruction settles
terminal coalgebras for the context endofunctor `L`. A terminal
`L`-coalgebra, a comparison with an end or coend construction, and a
dependent version over slices remain outside the formal development.

The proved specification is initiality for the binding operator `L`
associated to the supplied polynomial directions. This operator is
defined independently of the chosen syntax representation, so
{name}`endIsoInitial` applies to any other implementation of its
initial algebra in the stated category. Extending this characterization
to other profunctors requires specifying their binding operator and
proving the corresponding initiality; the polynomial case does not
assert such a result for arbitrary mixed-variance functors.

# Formal development

These sections render the implementation and tests from their Lean
sources: the profunctors, context operators, representation and
initiality theorems, followed by the examples and obstructions.

{includeLiterate "." Geb.Prototypes.PHOAS.Basic "Free monads and ends" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Binding "Context extension" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Scoped "Contexts and scoped unfolding" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Initial "Recursion and unique folds" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Paranatural "Paranatural families" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Term "Trees for coherent families" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Category "Categorical universal properties" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Kmett "Kmett's lambda syntax" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Algebra "Derived algebra profunctors" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Dual "The terminal-coalgebra obstruction" (level := 2)}

{includeLiterate "." Geb.Prototypes.PHOAS.Cofree "The pointwise cofree candidate" (level := 2)}

{includeLiterate "." GebTests.Prototypes.PHOAS "Executable binding examples" (level := 2)}
