# Definitions in Geb

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Mathematical construction](#mathematical-construction)
- [Definitions with imports and exports](#definitions-with-imports-and-exports)
- [Structural addresses](#structural-addresses)
- [Recursive definitions](#recursive-definitions)
- [Which equations are definitions](#which-equations-are-definitions)
- [Equations in slice, presheaf and depth-indexed settings](#equations-in-slice-presheaf-and-depth-indexed-settings)
- [Definitions as presentations](#definitions-as-presentations)
- [Content identity](#content-identity)
- [Unison and Nock](#unison-and-nock)
- [Relation to the existing representations](#relation-to-the-existing-representations)
- [Prototype boundary](#prototype-boundary)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

A candidate definition is a finitely presented derived operation of a
polynomial signature. Its body belongs to the signature's free monad;
its parameters are structural directions, the directions of the free
monad. The environments against which bodies are resolved are addressed
by vertices, the directions of the cofree comonoid. Recursive
definitions form a finite recursive program scheme. A block of equations
is a definition, relative to a class of models, when it has exactly one
solution in every model of the class: well-founded blocks in every
algebra, guarded blocks in every completely iterative algebra. A
definition's content identity is the identity of its presentation,
including its dependencies and semantic profile. Its denotation is a
separate construction in a specified model. Raw syntax remains the rose
tree of bitstrings. Each profile interprets the trees that decode to its
terms, interfaces, and definition blocks.

This proposal instantiates established constructions, rather than
postulating a categorical object universally called a definition. The
Lean prototype is [Definition.lean](../Geb/Prototypes/Definition.lean)
and the modules it indexes, with
[executable examples](../GebTests/Prototypes/Definition.lean).

## Mathematical construction

Let the ambient category initially be `Set`, and let

```text
P(X) = Σ a : A, X^(B a)
T_P(X) = μ Y. (X + P(Y)).
```

Here `P` is the signature of available constructors or operations;
`T_P` is its free monad. For an effective language, each `B a` comes
with a finite enumeration, and operation labels have a specified,
decodable bitstring representation. Finitary alone does not imply
that the shape type `A` has such a representation.

For a second polynomial `Q` describing operations to be defined, a
nonrecursive definition family is a natural transformation

```text
δ : Q ⇒ T_P.
```

In `Set`, the Yoneda correspondence gives the equivalent data

```text
δ_a ∈ T_P(B_Q a),                         a ∈ A_Q.
δ_X(a, arguments) = T_P(arguments)(δ_a).
```

Thus an operation is defined by a term with its argument directions as
variables. No textual name is required. The universal property of the
free monad extends `δ` to a monad morphism `T_Q ⇒ T_P`, which expands
uses of the defined operations. `Derived`, `expandOps`, and
`expandOps_bind` implement this family and its substitution law.

The polynomial representation of the free monad is

```text
T_P(X) ≅ Σ s : Shape(T_P), X^(Dir(s))
Shape(T_P) = T_P(1)
Dir(variable) = 1
Dir(operation(a, children)) = Σ b : B a, Dir(children(b)).
```

An operation body is consequently a tree shape together with a map
from its variable occurrences to its argument directions. This map may
duplicate or discard arguments. It need not be a bijection, so demanding
a cartesian natural transformation for every definition would exclude
ordinary duplication and weakening. The monad's unit and multiplication
are cartesian; arbitrary derived operations need not be.

[Gambino–Kock, Theorem 4.5](https://arxiv.org/pdf/0906.4931)
establishes the free-polynomial construction, including its slice
version. `Direction` implements the displayed dependent path equations;
`freePolynomial` packages their shapes and directions. The prototype
does not yet formalize the natural isomorphism with Cslib's `FreeM`.

## Definitions with imports and exports

For imports `Γ` and exports `E`, a nonrecursive block is

```text
d : E → T_P(Γ).
```

This is a Kleisli arrow `E → Γ`. The direction records which term
defines each export; it is opposite to the direction of an environment
transformer. Given `σ : Γ → T_P(Δ)`, linking is

```text
link(d, σ)(e) = μ_Δ(T_P(σ)(d(e))).
```

The monad laws provide identity and associative linking. For an algebra
`a : P(V) → V`, write `a* : T_P(V) → V` for its extension. An environment
`ρ : Γ → V` interprets the block by

```text
⟦d⟧_ρ = a* ∘ T_P(ρ) ∘ d : E → V.
```

The prototype proves compatibility between this interpretation and
linking. It does not prescribe evaluation order or effects: those require
a selected operational or denotational model. A morphism of the intended
Geb category can be a value in that model, represented by a finite term
of its inductively presented morphism signature.

## Structural addresses

Choose a separate polynomial `L` describing export grouping. An export
layout is `s : T_L(1)`, and its interface is

```text
E = Dir(s).
```

A direction of `T_L` at `s` records a direction of `L` at a node and a
direction in that child. For a binary layout with two levels, an example
is `(right, (left, leaf))`. This type makes an invalid route unavailable.
Local references use this dependent direction directly. An external
reference consists of a block identifier and a direction in that block's
validated layout. A resolver must check that the supplied layout matches
the retrieved block before accepting the direction.

Free-monad directions select variable leaves, not all syntactic nodes.
A closed term has no such directions, and a nullary operation is not a
variable leaf. The export layout therefore marks exports as variable
leaves deliberately.

Every node of a term is addressed by a vertex: at a variable, the root;
at an operation, the root or a direction of the operation followed by a
vertex of that child.

```text
Vtx(variable) = 1
Vtx(operation(a, children)) = 1 + Σ b : B a, Vtx(children(b)).
```

A vertex `v` of `t` selects the subterm `t ↓ v`, and a vertex `w` of that
subterm translates into the vertex `v ⊕ w` of `t`. With the root `o`,
these operations satisfy the five laws of a directed container:
`t ↓ o = t`, `t ↓ (v ⊕ w) = (t ↓ v) ↓ w`, `v ⊕ o = v`, `o ⊕ w = w` and
`(u ⊕ v) ⊕ w = u ⊕ (v ⊕ w)`
([Ahman–Chapman–Uustalu](https://arxiv.org/abs/1408.5809), Section 3.1).
Terms and their vertices are the cofree recursive directed container on
the signature with the variables adjoined as nullary operations (Section
4.4 there). Read as a tree of that signature, a term is a shape of the
cofree comonoid on it, and its vertices are the directions there
([Niu–Spivak](https://arxiv.org/abs/2312.00990), Proposition 8.18).
`Vertex`, `subterm`, `Vertex.root` and `Vertex.append` implement the
operations; `subterm_root`, `subterm_append`, `Vertex.append_root`,
`Vertex.root_append` and `Vertex.append_assoc` are the laws. Each
free-monad direction is a vertex whose subterm is its variable
(`Vertex.ofDirection`, `subterm_ofDirection`).

The two kinds of address serve the two structures. A direction of the
free monad is where a body receives an argument, and substitution fills
it; a vertex is where a structure is observed, and selection reads it.
Neither subsumes the other. [Libkind and
Spivak](https://arxiv.org/abs/2404.16321) show that the free monad is a
module over the cofree comonad: the free monad supplies terminating
patterns and the cofree comonad the behaviours they run on.

A term used as an environment, as a Nock subject is, is addressed by its
vertices. A body written against an environment `t` with variables `Γ`
is a term `b : T_P(Vtx(t))`. Its resolution substitutes the subterm at
each vertex:

```text
resolve(b) = μ_Γ(T_P(t ↓ −)(b)) : T_P(Γ).
```

This is `link` against the subterm map, a Kleisli composite, so the
monad laws apply to it; by `eval_bind`, the value of the resolved body is
the value of `b` with each vertex interpreted by the value of its
subterm. A body written against the subterm `t ↓ v` is transported to
`t` by renaming along `v ⊕ −`, and the transported body resolves against
`t` as the original resolves against `t ↓ v` (`link_map_append`, a
consequence of the second directed-container law). This is the structure
of Hoon's layering, in which code compiled against a core's context is
used from any subject containing that core, with addresses whose type
excludes the routes at which Nock's slot operation fails.

The layout is part of the interface, not a single mandatory global
library tree. A block can import selected exports from other blocks.
Putting every library into one enclosing identity would make unrelated
layout changes affect references unnecessarily. Paths may have a compact
wire encoding, but their definition and lookup laws remain structural.
An environment is likewise local to the bodies resolved against it.
Resolution replaces every vertex by the subterm there, so a resolved body
mentions no vertex of its environment; when the environment's subterms
carry content identities, a vertex whose subterm has no variables can be
replaced by that identity instead, which converts an environment-relative
reference into an immutable one.

## Recursive definitions

A recursive block of values has the finite equation-morphism form

```text
e : E → T_P(Γ + E).
```

Relative to fixed signatures `P`, `L` and imports `Γ`, a presented
definition is a block with a selected export:

```text
Def_(P,L)(Γ) = Σ s : T_L(1),
                (Dir(s) → T_P(Γ + Dir(s))) × Dir(s).
```

For finitary, effectively coded signatures and coded imports, this is
finite syntax. `Presented` is this dependent sum in Lean, and
`unfoldEntry` unfolds the selected definition. The layout determines the
type of the local references and the selection, so both remain tied to
the block they address.

Equivalently, `e` is a coalgebra for `X ↦ T_P(Γ + X)`, supplied with
a point `1 → E` and a polynomial direction presentation of `E`. Under the
finiteness assumptions this is a finite pointed coalgebra. A stored
import interface lists the finitely many declared imports; the generic
Lean construction also permits an ambient type of import references.

Its local references do not contain its own eventual hash. The finite
bodies contain references to directions in `E`. In an algebra `a`, a
solution relative to imports `ρ` is a function `v : E → V` satisfying

```text
v = a* ∘ T_P([ρ, v]) ∘ e.
```

This is `Block` and `IsSolution`. Finite simultaneous unfolding is
`unfold`; the prototype proves that a solution satisfies every unfolding.
This proves neither that a solution exists nor that it is unique.
For instance, `x = x` permits every value in every algebra, whereas
`x = successor(x)` has no natural-number solution.

To define operations that take arguments, use the more general finite
recursive program scheme

```text
δ : Q ⇒ T_(P+Q).
```

Each body may invoke a locally defined operation on new arguments. This
distinction matters: finitely many nullary equations describe only
regular unfoldings, while recursive function definitions can generate
nonregular trees. Application or a suitable binding signature can also
represent function-valued definitions; a first-order value block alone
does not supply those constructs.

[Milius–Moss](https://arxiv.org/pdf/0904.2385), Sections 3 and 6,
provides the equation-morphism and recursive-program-scheme framework.
Their general scheme uses the completely iterative monad of possibly
infinite trees. The proposal here restricts the right-hand sides to the
finite free monad, then includes them in that larger monad when its
solution theory applies. Guardedness and the model's solution structure
must be checked; being written as a finite tree is not sufficient.

For the flat guarded case `c : E → P(E)`, the prototype proves directly
that `PFunctor.M.corec c` solves the corresponding closed block in `M P`,
and that this solution is unique. The executable example presents an
infinite alternating bitstream by a two-state coalgebra. No unrestricted
fixed-point operator is introduced.

## Which equations are definitions

A family of equations defines its unknowns, relative to a class of
models, when it has exactly one solution in every model of the class.
This is the model-theoretic notion of a definitional extension, stated
for the equations of a block:

| Block | Solutions | Status |
| --- | --- | --- |
| Well-founded: each body refers only to exports below its own | exactly one in every algebra | a definition |
| Guarded: each body is an operation or an import | exactly one in every completely iterative algebra, the M-type among them | a corecursive definition |
| Unguarded | possibly none (`x = successor(x)`) or many (`x = x`) | a constraint on models |

Derived operations belong to the first row. Each defining equation
states the value of its operation, so every algebra of `P` expands in
exactly one way to an algebra of `Q` satisfying them (`derivedAlg`), and
evaluating a term of defined operations agrees with evaluating its
expansion (`eval_expandOps`).

A well-founded block is a typing of the bodies rather than a condition
checked after the fact: for a relation `r` on `E`, the body at `i` ranges
over `T_P(Γ + {j // r j i})`. When `r` is well founded, the block has
exactly one solution in every algebra and environment
(`WFBlock.existsUnique_isSolution`), constructed and characterized by
well-founded recursion on the exports. Layered libraries, in which each
block imports only the exports of earlier blocks, are the special case in
which the relation is the order of the layers.

For guarded blocks, [Milius–Moss](https://arxiv.org/pdf/0904.2385)
prove unique solutions in completely iterative algebras. In the prototype
a guarded block is a typing of its bodies: the body at an export is an
element of `P(T_P(Γ + E)) + Γ`, an operation applied to terms of any
depth or an import (`GuardedBlock`). With imports interpreted in the
M-type constructed from W-types (`Geb/Prototypes/MType/`), such a block
has exactly one solution there (`GuardedBlock.existsUnique_isSolution`):
existence by corecursion on states that are finished values or pending
terms, uniqueness by a bisimulation relating the values of each term
under two solutions. `coalgebra_solution_unique` is the flat case, in
mathlib's M-type: a flat guarded block is a finite coalgebra, and its
unique solution is the corecursive map that finality supplies. A guarded
block is therefore the finite syntax of a corecursive definition. Its
references into its own exports are directions, not digests of the
definition being written, so the acyclicity of content identity between
blocks is unaffected.
Unguarded blocks are equations that constrain their models; they are
axioms rather than definitions.

## Equations in slice, presheaf and depth-indexed settings

Slice and presheaf W-types also add equations to W-types, but of a
different kind. Their equations, that a child's index matches the index
its direction requires and that restrictions are natural, are
well-formedness conditions on trees: they select syntax. The equations
of a block constrain interpretations: they select denotations.
Generalizing the free monad to slice and presheaf free monads extends
what a body can be, to sorted bodies and to context-indexed bodies with
renaming, and equation morphisms are defined in those settings as well;
their equations remain semantic, and the slice or presheaf free monad
does not absorb them.

What a slice typing does absorb is the discipline that places a block in
a row of the table. Well-foundedness is the index constraint of
`WFBlock`. Guardedness is the typing of each body as an element of
`P(T_P(Γ + E)) + Γ` rather than of `T_P(Γ + E)`, which is the
guardedness condition of Milius–Moss for systems of equations: no
right-hand side is a bare variable of the system; `GuardedBlock` is that
typing. A slice layer can therefore make the question whether a block is
a definition, and for which models, a question of type checking.

The equations themselves integrate with the M-type side through depth.
In presheaves on `ω`, the topos of trees
([Birkedal–Møgelberg–Schwinghammer–Støvring](https://arxiv.org/abs/1208.3596)),
a guarded recursive definition has a unique solution because its value
at depth `n + 1` is determined by its value at depth `n`: guarded
recursion becomes well-founded recursion on depth. The proof of
`coalgebra_solution_unique` has this form, by recursion on the depth of
the M-type's approximations, and the
[bitstream construction](../Geb/Prototypes/BitStream/WConstruction.lean)
builds an M-type from a presheaf W-family of finite observations over the
walking arrow together with equations of agreement between adjacent
depths. A guarded block's equations, restricted to depth `n`, are those
agreement equations. Slice and presheaf M-types built in that way would
carry the solutions of guarded blocks as depth-indexed families of
well-founded definitions. The finite observations are the vertices: the
solution of a guarded block is a shape of the cofree comonoid, observed
at its finite rooted paths.

## Definitions as presentations

An equational presentation over a signature `P` is a polynomial `E` of
equations, whose directions at an equation are its variables, with two
derived operations `lhs, rhs : E ⇒ T_P`: the two sides of every equation,
terms of any depth. The sides induce a parallel pair of monad morphisms
`T_E ⇉ T_P`, and finitary monads are presented as coequalizers of such
pairs of free monads ([KellyPower1993], the signatures there being
families of objects indexed by the finitely presentable ones). The
prototype computes the presented object pointwise
([Definition/Presentation/](../Geb/Prototypes/Definition/Presentation.lean)).
A witness over variables `Γ` is a term of `T_{P+E}(Γ)`: its operations of
`P` are congruences, its operations of `E` instances of equations whose
arguments are witnesses, and its variables reflexivities. Its two
endpoints are its images under the monad morphisms `T_{P+E} ⇒ T_P` of the
handlers that fix `P` and send each equation to one of its sides, so the
endpoint maps commute with substitution, and the classes of terms are the
coequalizer of the two endpoint maps, whose quotient takes the equivalence
closure. An algebra satisfies the equations exactly when it gives the two
endpoints of every witness equal values, and for a finitary presentation
the classes over `Γ` are the free algebra satisfying the equations on `Γ`.

The quotient presheaf polynomial functors of
[QuotientPRA/](../Geb/Prototypes/QuotientPRA.lean) build terms and
witnesses as one presheaf W-type, whose restriction rebuilds only the root
of a tree, so each side of their equations is one operation applied to
variables. Such a system is the presentation of its sides as terms of depth
one, and the two constructions give isomorphic initial algebras. The sides
of associativity have depth two, and one side of a unit law is a bare
variable: binary trees modulo those equations present the free monoid, whose
classes are the lists.

A family of derived operations `δ : Q ⇒ T_P` is the presentation over
`P + Q` of the equations `q(x⃗) = δ_q(x⃗)`. The monad morphism of the handler
that fixes `P` and sends each `q` to `δ_q`, the unfolding, coequalizes the
two endpoint maps, and the inclusion of `T_P` is a section of it. A
presentation over signatures `Σ ⊆ Σ'` is definitional when the composite
`T_Σ → T_Σ' → classes` is a bijection. Surjectivity is eliminability, every
new term equal to an old one; injectivity is non-creativity, no new
identification of old terms. These are the two criteria for a definition
that Suppes attributes to Leśniewski ([Suppes1957], pp. 153–154), and the
presentation of derived operations meets both: every term has the class of
its unfolding, a single witness replacing each new operation by the instance
of its equation, and the value of classes in `T_P`, each new operation read
as its body, sends the class of a term to its unfolding. Its models are the
algebras of `P`, each expanded by `derivedAlg`.

| Presentation | New symbols eliminable | Old terms kept distinct |
| --- | --- | --- |
| Derived operations, as `quad(x) = double(double(x))` | yes | yes |
| Commutativity of a binary operation | no new symbol | no |
| `c = succ(c)` over zero and successor | no | yes |

Over a slice polynomial endofunctor, a presentation assigns each equation an
output sort and its variables input sorts, and its sides are well-sorted
terms of the free monad of the underlying polynomial functor
([Definition/Presentation/Slice/](../Geb/Prototypes/Definition/Presentation/Slice.lean)).
Its witnesses are the well-sorted witnesses of the underlying presentation,
and its classes of each sort are the coequalizer of their endpoints at that
sort. The equivalence relation must be generated by well-sorted witnesses
alone, since a chain of the underlying presentation's witnesses can pass
through terms that are not well sorted. Evaluation does not restrict from
the underlying polynomial functor: an algebra over the sorts applies an
operation only to arguments of its input sorts, so well-sorted terms are
evaluated by the free monad's dependent recursor, whose motive carries their
well-sortedness.

Commutativity presents a new theory of the old symbols. The equation
`c = succ(c)` presents a theory with a new element: the class of `c` is the
class of no term of zero and successor, and it has no solution in the natural
numbers. As a guarded block it has exactly one solution in the M-type
(§ Which equations are definitions), so it is a definition relative to that
class of models and not relative to all algebras; the classes of terms, a
quotient of a free algebra, do not contain that solution.

## Content identity

The proposed hash input is a canonical rose tree representing

```text
(schema version, semantic profile reference,
 import interface, export layout, definition bodies).
```

The semantic profile fixes the signature, interpretation of primitive
codes, binding conventions, serialization, and the relevant typing or
execution discipline. Types or certificates that affect meaning belong
in the identity-bearing data; an optional separately checked certificate
can instead attest to an already identified definition. Comments and
display names remain annotations, as in the existing
[concrete-syntax proposal](concrete-syntaxes.md).

Imports contain immutable dependency references. A mutually recursive
component is stored as one block, with internal references by direction.
An exported definition is identified by `(block identifier, direction)`.
This avoids attempting to solve cryptographic fixed-point equations.
The component dependency graph is acyclic after strongly connected
components have been grouped. Component discovery and serialization are
separate from evaluating their equations.

The initial convention should preserve the chosen export layout and
body order. Renaming textual aliases then leaves identity unchanged;
reordering the structural interface may change it. Invariance under
permuting recursive definitions would require a further canonicalization
that transports every internal reference. Sorting hashes alone is not
a specification of how symmetric or tied members are handled. The
prototype makes no permutation-invariance claim.

A digest is a practical locator, not a mathematically injective function
on all definitions. Exact identity is equality of canonical payloads.
A finite digest cannot injectively encode an unbounded family of finite
trees. A store must adopt a collision policy, validate retrieved payloads,
and reject conflicting content at an occupied identifier. Equal hashes
alone are not a theorem of equal syntax or equal meaning.

Likewise, syntactic identity is distinct from equality of denotations.
Inlining, changing recursion equations, or changing sharing can preserve
behavior while changing content identity. With reflection, those
structural differences may themselves be observable. No quotient by
general semantic equivalence is proposed.

## Unison and Nock

Unison identifies definitions by hashes of internal syntax, replaces
dependency names by hash references, and excludes local names from the
hash. Its documented recursive references identify a cycle and a member
within it. This supplies a precedent for immutable block identity plus
local structural references. Geb can retain its proposed versioned
multihash envelope and use polynomial directions for those members.
Sources: [Unison's hashing overview](https://www.unison-lang.org/docs/tour/_big-technical-idea/)
and [hash reference documentation](https://www.unison-lang.org/docs/language-reference/hashes/).

Unison also distinguishes structural types from unique types. Its
[unique-type construction](https://www.unison-lang.org/docs/language-reference/unique-types/)
incorporates a generated identifier into a type's hash input. Therefore
content addressing does not require identifying all structurally
isomorphic types. If Geb needs generative declarations, their identity
tokens must be explicit semantic data; display names still need not
determine identity. This proposal introduces no generative token.

Nock evaluates a formula against a subject, both represented as nouns.
Its slot operation uses positive integer axes: root, left child, and
right child are encoded by 1, 2, and 3. Thus the integers encode binary
paths, rather than supplying an intrinsically different addressing
concept: an axis that selects a node of the subject is a vertex of it,
and the vertex type of a given subject omits the axes at which the slot
operation fails. A Hoon core pairs a battery of code with a payload, and an arm
executes against the core as its subject. Nested library cores and the
numbered standard-library layers are Hoon organization conventions, not
a requirement of the Nock reduction rules. The direction of availability
is determined by the captured subject, not by calling a layer higher or
lower. Sources: [Nock specification](https://docs.urbit.org/nock/specification),
[cores](https://docs.urbit.org/build-on-urbit/hoon-school/f-cores),
[subject organization](https://docs.urbit.org/hoon/why-hoon), and
[standard-library layers](https://docs.urbit.org/hoon/stdlib).

The resulting Geb proposal combines immutable dependency references with
explicit structural environments. Neither language supplies the entire
categorical construction or its correctness proofs for Geb.

## Relation to the existing representations

| Existing construction | Role in the proposal |
| --- | --- |
| Rose trees of bitstrings | Canonical finite representation of interfaces, bodies, and profile references |
| Alternative AST representations | Transport the encoding through a computable isomorphism |
| Canonical and readable S-expressions | Presentations of the same payload through the appropriate codec |
| Finitary W-types and their recognizer | Typed finite bodies over effectively coded signatures |
| Inductively defined morphisms | Signature operations and derived operations, interpreted as morphisms |
| M-types and bitstreams | Possible denotations of finite productive specifications |
| Slice W-types | Sort-correct bodies, imports, and export directions in a slice |
| Presheaf W-types | A base for context-indexed syntax when the required substitution structure is supplied |
| Small inductive-recursive compilation | Reuse the compiled slice signature; no separate definition mechanism |
| Interaction combinators and polynomial evolution | Candidate interpretations or execution profiles for the same finite codes |
| Hash identity | A locator for the canonical presentation and its immutable dependencies |

The new term encoder injects into the existing `RoseTree ℕ`; its natural
labels use the established bitstring sentinel representation. Composing
with `RoseTree.wire` is proved injective. This connects the prototype to
the bitstring wire language and its existing recognizer. It does not
claim that recognizing a valid definition, resolving its imports, or
checking its semantics takes logarithmic space. The earlier S-expression
prototypes use a finite label alphabet; adapting arbitrary definition
payloads to those interfaces still requires the corresponding codec.

In a slice, the free-monad equations are interpreted over a fixed index
object and substitutions preserve those indices. In a presheaf setting,
maps must additionally respect restriction or renaming. Existing
presheaf W-types alone do not establish capture-avoiding substitution
for every binding signature. [Fiore's dependently sorted syntax](https://www.cl.cam.ac.uk/~mpf23/papers/Types/AbsSyn.pdf)
provides the relevant algebraic setting; selecting the category of
contexts and proving the substitution laws remains part of a binding
language's definition.

For interaction nets, a serialized tree may present a graph with sharing,
cycles, and an interface. It need not be that graph's tree unfolding.
[Garner's syntax with sharing](https://arxiv.org/pdf/1009.3682), including
cyclic term graphs in Section 5, is a closer model when those graph
properties must be retained. Compiling a definition into such a runtime
requires a semantics-preservation theorem. For reflective polynomial
evolution, the rule specification and its interpreter must themselves
have effective finite presentations; see
[reflective-polynomial-evolution.md](reflective-polynomial-evolution.md).

Finally, a construction of M-types using W-types does not make every
M-value finitely serializable. In the existing
[bitstream construction](../Geb/Prototypes/BitStream/WConstruction.lean),
the outer W-node has an infinite family of finite observations. Finite
code can represent a definable observation-producing morphism, together
with its correctness or productivity evidence. It cannot represent all
arbitrary functions or all arbitrary bitstreams. Finite-state stream
presentations are narrower still: they produce eventually periodic
infinite streams. General finitely coded generators may have infinite
state spaces and produce nonperiodic streams.

## Prototype boundary

The prototype implements ordinary polynomial signatures in `Type`,
structural direction types, derived-operation expansion, linking,
recursive value blocks with selected exports, finite unfolding,
algebraic interpretation,
flat guarded M-type solutions, and an injective term encoding into
rose trees and then bitstrings
([Definition/Basic.lean](../Geb/Prototypes/Definition/Basic.lean)); the
vertices of terms with their directed-container laws, resolution against
an environment and transport along a vertex
([Definition/Vertex.lean](../Geb/Prototypes/Definition/Vertex.lean));
the soundness of derived-operation expansion and the unique solution
of well-founded blocks
([Definition/Solution.lean](../Geb/Prototypes/Definition/Solution.lean));
guarded blocks with their unique solution in the M-type
([Definition/Guarded.lean](../Geb/Prototypes/Definition/Guarded.lean));
and equational presentations with free-monad sides, their classes of
terms and free models, the agreement with one-step equations, the
presentations of derived operations and the many-sorted presentations
over a slice
([Definition/Presentation.lean](../Geb/Prototypes/Definition/Presentation.lean)).
Its examples exercise structural references, repeated use of an imported
definition, infinite stream production, vertices of a subject with a
parameter and two layers, transport of a body between layers, and the
unique solution of a three-export well-founded block, and bitstreams
defined by guarded blocks, one of depth two referring to its own export
and one with an imported stream, and the presentations of the free monoid,
of commutative binary trees, of a definition of depth two and of a constant
equal to its own successor. All recursion uses
existing recursors, the existing free-monad interpreter, or well-founded
recursion in proofs; `Definition/Vertex.lean` uses the executable code
for the free monad's recursor that
[Free.lean](../Geb/Cslib/Foundations/Data/PFunctor/Free.lean) supplies,
since a subterm selected by a vertex depends on the term.

It does not implement cryptographic hashing, a content store, a block
decoder, permutation canonicalization, a binder language, the presheaf
free-monad interface, solutions of guarded blocks in
completely iterative algebras other than the M-type, a general
recursive-program-scheme solver, the replacement of vertices by content
identities, or a compiler to interaction nets. These require selected
profiles and their proof obligations; adding them to the definition
format itself would prematurely select language semantics.

Run the examples with `lake build GebTests.Prototypes.Definition`.
Bibliographic keys used here are `GambinoKock2013`, `MiliusMoss2009`,
`Fiore2008`, `Garner2012`, `AhmanChapmanUustalu2014`, `NiuSpivak2023`,
`LibkindSpivak2025`, `BirkedalMogelbergSchwinghammerStovring2012`,
`KellyPower1993` and `Suppes1957` in [references.bib](references.bib).
