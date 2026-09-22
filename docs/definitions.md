# Definitions in Geb

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Mathematical construction](#mathematical-construction)
- [Definitions with imports and exports](#definitions-with-imports-and-exports)
- [Structural addresses](#structural-addresses)
- [Recursive definitions](#recursive-definitions)
- [Content identity](#content-identity)
- [Unison and Nock](#unison-and-nock)
- [Relation to the existing representations](#relation-to-the-existing-representations)
- [Prototype boundary](#prototype-boundary)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

A candidate definition is a finitely presented derived operation of a
polynomial signature. Its body belongs to the signature's free monad;
its parameters are structural directions. Recursive definitions form a
finite recursive program scheme. A definition's content identity is the
identity of this presentation, including its dependencies and semantic
profile. Its denotation is a separate construction in a specified model.
Raw syntax remains the rose tree of bitstrings. Each profile interprets
the trees that decode to its terms, interfaces, and definition blocks.

This proposal instantiates established constructions, rather than
postulating a categorical object universally called a definition. The
Lean prototype is [Definition.lean](../Geb/Prototypes/Definition.lean),
with [executable examples](../GebTests/Prototypes/Definition.lean).

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
leaves deliberately. Addressing arbitrary internal syntax occurrences
requires a separate marked-node or context construction; it cannot be
obtained by treating the free monad's directions as all nodes.

The layout is part of the interface, not a single mandatory global
library tree. A block can import selected exports from other blocks.
Putting every library into one enclosing identity would make unrelated
layout changes affect references unnecessarily. Paths may have a compact
wire encoding, but their definition and lookup laws remain structural.

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
concept. A Hoon core pairs a battery of code with a payload, and an arm
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
rose trees and then bitstrings. Its examples exercise structural
references, repeated use of an imported definition, and infinite
stream production. All recursion uses existing recursors or the
existing free-monad interpreter.

It does not implement cryptographic hashing, a content store, a block
decoder, permutation canonicalization, a binder language, the slice or
presheaf free-monad interface, a general recursive-program-scheme solver,
or a compiler to interaction nets. These require selected profiles and
their proof obligations; adding them to the definition format itself
would prematurely select language semantics.

Run the examples with `lake build GebTests.Prototypes.Definition`.
Bibliographic keys used here are `GambinoKock2013`, `MiliusMoss2009`,
`Fiore2008`, and `Garner2012` in [references.bib](references.bib).
