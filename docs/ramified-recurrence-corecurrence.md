# Ramified recurrence and corecurrence

This document proposes an implementation of finite-word and stream function
algebras using the repository's indexed polynomial syntax. Oitavem's `Logs`
supplies a finite fragment; Leivant–Ramyaa supplies ramified corecurrence;
Danner–Royer supplies a framework for treating inductive and coinductive
data together. The proposed constructions and proof obligations below are
distinct from the published characterizations and the existing Lean results.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Objective](#objective)
- [Relationship between the source systems](#relationship-between-the-source-systems)
  - [Oitavem](#oitavem)
  - [Leivant–Ramyaa](#leivantramyaa)
  - [Danner–Royer](#dannerroyer)
- [Data polynomials and program signatures](#data-polynomials-and-program-signatures)
- [Existing implementation and shared syntax](#existing-implementation-and-shared-syntax)
  - [Bitstream carriers](#bitstream-carriers)
  - [Indexed program syntax](#indexed-program-syntax)
- [Finite restrictions, productivity, and silent steps](#finite-restrictions-productivity-and-silent-steps)
  - [An obstruction to productive extension](#an-obstruction-to-productive-extension)
  - [A carrier for delayed computation](#a-carrier-for-delayed-computation)
  - [Finite-stream interface](#finite-stream-interface)
- [Inclusions and compilation](#inclusions-and-compilation)
  - [Data and syntax inclusions](#data-and-syntax-inclusions)
  - [Compiler correctness target](#compiler-correctness-target)
  - [Injection of denotations](#injection-of-denotations)
- [Resource and proof obligations](#resource-and-proof-obligations)
- [Implementation sequence](#implementation-sequence)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Objective

Provide constructors for programs over finite words, finite streams, and
infinite streams, sharing syntax infrastructure and operations where their
typing and interpretation agree. Defining a program should require only
syntactic conditions on sorts, arities, and tiers. Users should not supply
termination, productivity, or resource proofs for individual programs.

The guarantee depends on the fragment:

| Fragment | Intended interpretation | Guarantee from the fragment's metatheory |
| --- | --- | --- |
| Oitavem finite words | Finite words to finite words | Totality and finite-input logspace |
| Oitavem finite streams | The same functions, with incremental input access and output | Finite output on finite input, with a logspace implementation |
| Strict ramified corecurrence | Infinite streams to infinite streams | Productivity and the source system's stream resource bounds |
| Ramified lazy corecurrence | Stream computations permitting silent steps | The specified transducer behavior; termination and data productivity require further guarantees |

Here, absence of user-supplied proofs does not mean absence of proofs in
the implementation. Constructors can discharge syntactic equalities, as
the existing Oitavem constructors do. General interpretation and compiler
theorems supply the semantic guarantees. A finite-stream interface also
needs a representation that establishes finiteness of its inputs; an
arbitrary coinductive sequence does not establish that condition.

## Relationship between the source systems

### Oitavem

[Oitavem2010], Definition 3.1, presents `Logs` using normal composition,
safe recursion on notation, safe concatenation recursion on notation,
and safe log-transition. Theorem 3.4 identifies its denotations with
`FLOGSPACE`, with finite words encoded as in the chapter.

The logspace restriction depends on these particular schemes. In
particular, normal composition and log-transition control access to the
recursive value. Merely having two tiers does not identify a function
algebra with logspace.

### Leivant–Ramyaa

[LeivantRamyaa2015], §4, treats strict corecurrence with arbitrary tiers.
Theorem 2 establishes a jumping finite transducer interpretation with
tier-dependent locality and polynomial continuity properties. Theorem 4
relates jumping finite transducers, two-tier lazy corecurrence, and
strict ramified corecurrence followed by collapse of silent symbols.

Section 5 represents a finite word by appending an infinite repetition
of an end-marker. Its finite interpretation `f_fin` is a partial
function obtained using that representation and collapse. Theorem 5,
together with Proposition 2, gives the finite logspace characterization.
Thus the comparison with Oitavem concerns the resulting total finite
functions. An arbitrary ramified stream program can produce infinite
output even when every input represents a finite word.

### Danner–Royer

[DannerRoyer2012], §§2–3, develops a common formalism for inductive and
coinductive data specified by polynomial functors. Its ramified system
`RS1` provides normal and safe types with restricted folds and unfolds.
The full system concerns polynomial-time computation with a specified
representation and sharing discipline. Section 3 identifies logspace
stream fragments by restricting the available types.

This is a precedent for the proposed organization, rather than a theorem
that combining Oitavem and Leivant–Ramyaa preserves logspace. The
logspace claims require the corresponding restrictions on operations,
types, and evaluation. The preprint sketches some resource arguments
and states others without full proofs; formalizing them remains work.
Its lazy evaluation of codata constructors should also be distinguished
from Leivant–Ramyaa's lazy corecurrence: delaying evaluation of an
observable constructor does not itself add silent computation steps.

## Data polynomials and program signatures

For a finite alphabet `A`, consider the polynomial:

```text
F_A(X) = 1 + A × X
Word A = μ F_A
CoWord A = ν F_A
```

The initial algebra represents finite words. The final coalgebra
represents finite-or-infinite sequences, with an observable empty
constructor. Infinite streams alone use `ν X. A × X`.

For `A = Bool`, the carriers, finite observations, and W-to-M inclusion
are implemented by the [bitstream constructions](#bitstream-carriers)
below. Use those representations for the binary instance.

The polynomial for program syntax has a different role. Its shapes are
program constructors; its directions are their subprogram positions.
Both recurrence programs and corecurrence programs have finite
descriptions, so both can use W-types of indexed program signatures.
Their interpreters assign different semantic operations to the nodes:
recursion on finite data and corecursion into codata.

Taking the M-type of Oitavem's program signature would instead allow
potentially infinite program descriptions. It would not by itself
provide the desired stream interpretation of finite programs.

The choice between terminated sequences and the paper's end-marker
representation must be connected by an explicit representation theorem.
[LeivantRamyaa2015], §5.1, footnote 3, mentions a nullary constructor as
an alternative but observes that it requires restating the schemes.
Changing the data polynomial does not automatically transfer the
published complexity theorem.

## Existing implementation and shared syntax

### Bitstream carriers

[BitStream.lean](../Geb/Prototypes/BitStream.lean) defines
`Geb.BitStream.sig` and the layer equivalence
`sig X ≃ Option (Bool × X)`. Its `wEquiv` identifies `sig.W` with
`List Bool`; `seqEquiv` identifies `sig.M` with `Stream'.Seq Bool`.
The intermediate `Observations` representation packages compatible
finite prefixes. These are equivalences of observable structure:

| Declaration in `Geb.BitStream` | Reusable result |
| --- | --- |
| `take_seqEquiv` | A sequence prefix agrees with the corresponding finite M-type approximation. |
| `seqEquiv_mk`, `seqEquiv_corec` | The equivalence preserves constructors and corecursion. |
| `ofW`, `ofW_injective`, `seqEquiv_ofW` | The W-to-M inclusion is injective and agrees with `Stream'.Seq.ofList`. |
| `corecPrefix_always_some_length` | A transition that always emits a bit fills every observation depth; no finite observation reaches termination. |

[WConstruction.lean](../Geb/Prototypes/BitStream/WConstruction.lean)
states an equivalent carrier `Geb.BitStream.WConstruction.Stream`, the
M-type `Geb.MType.M` of
[MType.lean](../Geb/Prototypes/MType.lean) at the bitstring polynomial,
constructed using ordinary, presheaf, and slice W-types. Its W-type
`Depth` indexes the dependent observation family `Approx`. `Bundle`
packages the observations in a slice W-tree, and `M` requires adjacent
observations to agree. The bundle root has one child per depth; this
is a well-founded tree with infinitely many children, rather than an
infinite branch or a finite program description.

In that namespace, `mEquiv` and `seqEquiv` identify `Stream` with
`Geb.BitStream.sig.M` and `Stream'.Seq Bool`. The operations `mk`,
`dest`, `tail`, and `corec` work directly on the W-representation.
Use `streamLayerEquiv` for the constructor/destructor correspondence,
`observe_corec` and `corec_eq` for the corecursor equations, and
`stream_ext` to prove equality through finite observations.
`mEquiv_corec`, `seqEquiv_corec`, and `seqEquiv_ofW` transfer these
operations and the finite inclusion to the other representations.

The `corec` constructor supplies the compatibility proof internally.
These results provide a data representation and its observation laws;
they do not restrict transitions to a ramified function algebra or
bound their resource use. They also do not decide whether a bitstream
eventually terminates. Generalizing this construction from W-types
to other polynomials remains separate work.

### Indexed program syntax

[Oitavem's syntax](../Geb/Prototypes/Computability/Oitavem/Syntax.lean)
provides `sig`, `Expr`, `wellFormed`, and `Expr.eval`. Its index is the
pair of normal and safe arities. Its semantic family, reused from
[Bellantoni–Cook](../Geb/Mathlib/Computability/BellantoniCook/Basic.lean),
consists of word-valued functions on word inputs.

The stream system needs an index describing input sorts and tiers, and
the output sort and tier. Symbols and streams are distinct sorts;
finite words and coinductive sequences must also be distinguished where
an operation requires finiteness. Oitavem's normal/safe positions and
Leivant–Ramyaa's tier ordering should retain their respective rules.
Their correspondence, if used by a translation, is a theorem to prove.

Over a common index type `J`, the intended syntax can be expressed as:

```text
J    = (input sorts and tiers, output sort and tier)
Expr = μ_J (Σ_common + Σ_finite + Σ_corecurrence)
```

This is a proposed organization, not an implemented Lean declaration.
Reindex the component signatures before forming their coproduct.
Use the existing
[`SlicePFunctor.coprod`](../Geb/Mathlib/Data/PFunctor/Slice/Basic.lean)
and [slice W-type](../Geb/Mathlib/Data/PFunctor/Slice/W.lean)
infrastructure for construction, interpretation, and structural
induction. Retain Oitavem's existing constructors and their behavior
through a semantics-preserving inclusion.

Share projections, branching, and structural operations when their
sorts and tier rules agree. Keep operations requiring a complete word,
such as its length, in the finite fragment. A generic interpreter fold
can be shared without claiming that every operation has both a finite
and an infinite interpretation.

At the semantic level, strict stream corecurrence has the form:

```text
h : S → A
g : S → S
corec(h, g)(s) = h(s) :: corec(h, g)(g(s))
```

Here `S` is the permitted state type, and `h` and `g` are interpreted
subprograms satisfying the source system's typing restrictions. They
are not arbitrary Lean functions admitted as primitive operations.
For simultaneous corecurrence, the finite control index can be included
in the state interpretation. For bits, use
`Geb.BitStream.WConstruction.corec` with the transition
`fun s ↦ some (h s, g s)`. Its defining and comparison equations are
already proved, and `Geb.BitStream.corecPrefix_always_some_length`
supplies the finite-observation criterion for an infinite result.
Mathlib's `PFunctor.M.corec` remains the underlying general corecursor.

A coproduct of signatures permits combinations according to its
indices. Each additional composition or conversion between fragments
therefore needs a rule and a soundness argument. In particular, a
computed value must not acquire permission to drive a recursion or
update corecursive state merely through a conversion of representation.

## Finite restrictions, productivity, and silent steps

### An obstruction to productive extension

Consider the finite-word function returning one bit for the parity of
the input length. It is computable with constant working memory and
therefore belongs to the finite logspace class.

Suppose it had a computable extension to coinductive sequences that
agreed on all finite inputs and could produce its first output
observation on every input. On the infinite zero stream, the computation
of that observation inspects finitely many positions. There are finite
zero words extending those observations with either length parity.
Agreement on finite inputs would require different first output bits,
although the computation has observed the same input information.
Returning an empty output would also disagree with both completions.

Consequently, such an extension cannot be productive on that infinite
input. This is an obstruction from finite observation, independent of
the polynomial representation of programs. It also distinguishes
finiteness of an output from the ability to compute an observable end
of that output.

### A carrier for delayed computation

One possible computational carrier is the M-type of:

```text
D_A(X) = 1 + X + A × X
```

Its alternatives represent stopping, taking a silent step, and emitting
a symbol. Infinite silent computation is a value of this M-type.
Every step observation can be defined while the computation produces
no further data symbols.

The existing bitstream layer `Option (Bool × X)` supplies termination
and emission, but has no silent-step alternative. Its `none` means
termination. Supporting `D_A` therefore requires a distinct polynomial
or a verified encoding; the bitstream corecursor alone does not add
silent computation.

This is a proposed representation of computation, not an identification
with the paper's stream algebra. In particular, an explicit stop and
an infinite silent suffix have different observable behavior. Their
relationship to collapse must be specified before transferring a source
theorem.

There is no generic constructive operation erasing silent steps into
an ordinary terminated sequence while preserving all intended outputs:
finding the next symbol, or establishing that none follows, can fail
to terminate. Define output observations relationally or through an
appropriate partial computation. A theorem establishing termination
or productivity can then justify a stronger interface for a fragment.

### Finite-stream interface

A finite-stream view of an Oitavem function has the same extensional
meaning as its word interpretation. Its implementation may access the
input repeatedly and produce output incrementally. The intended
logspace model must permit the required read-only access; a single
irrevocable pass over the input is an additional restriction.

For bits, use `Geb.BitStream.WConstruction.Stream` with its sequence
equivalence. A finite word `w` is represented by
`Geb.BitStream.WConstruction.ofW (Geb.BitStream.wEquiv.symm w)`.
`seqEquiv_ofW` identifies its sequence view with `Stream'.Seq.ofList w`,
whose finiteness is established by mathlib's
`Stream'.Seq.terminates_ofList`. The bitstream observations and the
Oitavem machine readers both count positions from the Lean list head.
These representation laws do not establish the space usage of an
Oitavem evaluator.

Use a finite input representation, such as words with a stream access
interface, or a representation whose constructors establish finiteness.
Require no separate finiteness proof for each program. A general
compiler theorem must establish finite output for all programs of the
finite fragment on those inputs.

## Inclusions and compilation

### Data and syntax inclusions

For words, the map `Word A → CoWord A` preserves empty and cons and is
injective. For bits, `Geb.BitStream.ofW` and `ofW_injective` implement
and verify this inclusion. `Geb.BitStream.WConstruction.ofW` supplies
the W-representation of the same inclusion, related by `mEquiv_ofW`
and `seqEquiv_ofW`. Independently, inclusion of a program-signature
component gives an inclusion of its finite syntax trees into the
combined syntax, with an interpretation-preservation theorem.

These inclusions do not supply a translation into pure Leivant–Ramyaa
syntax. Such a translation can replace an Oitavem constructor with an
entire target program.

### Compiler correctness target

For an Oitavem program `e`, seek a compiler `C` satisfying:

```text
(⟦C(e)⟧)_fin = ⟦e⟧
```

Equality here is equality of partial finite-word functions, with the
right-hand side regarded as total. It includes definedness of the
left-hand side on every finite input. The subscript `fin` refers to
the chosen padding and output-observation semantics; it is not an
assumed total executable collapse operation.

A candidate route suggested by the characterizations is:

```text
Oitavem expression
  → logspace transducer
  → jumping finite transducer on encoded streams
  → ramified lazy corecurrence program
```

Each arrow requires a constructive translation and a correctness
theorem with matching encodings and machine conventions. The source
theorems establish the extensional relationship; they do not make
these implementation steps automatic. An efficient finite-stream
interpreter can be developed before a translation into pure
corecurrence syntax is available.

### Injection of denotations

The compiler correctness equation reflects distinctions between finite
functions: if two source functions differ on a finite input, their
translations differ under finite observation. It does not establish
that equivalent source programs have identical behavior on infinite
inputs or identical silent-step traces.

To obtain a map on equivalence classes of source denotations, specify
an extension invariant under source equivalence. One possible partial
extension waits for all input ends, computes the finite function, and
remains silent if an input never ends. Modulo an observation relation
that ignores finite silent delays, this supplies an injective extension
of finite functions. Implementing it in the intended resource model
still requires the transducer construction; storing the complete input
is not justified by this description.

No corresponding inclusion of all finite logspace functions into
everywhere-productive stream functions is possible under the finite
observation model, by the parity example above.

## Resource and proof obligations

Finite-word logspace is measured against input length. The strict
stream analysis uses output position and the specified input-access
model. Erasure of silent symbols changes the relation between
computation steps and output positions, so a resource theorem for a
trace does not automatically bound production of its collapsed output.
Neither an unrestricted collapse nor unrestricted composition across
fragments should inherit a logspace claim without a proof.

The [Oitavem development](../Geb/Prototypes/Computability/Oitavem.lean)
already provides the syntax, word interpretation, truncation results,
polynomial output-length bounds, and logarithmic representations of
retained recursion state. In
[Recursion.lean](../Geb/Prototypes/Computability/Oitavem/Recursion.lean),
`Expr.prefixCutoff` and `Expr.recursionCutoff` compute cutoffs from
syntax. `Expr.eval_safeRec_cons_prefixCutoff` connects the cutoff to
`prefixLoop`, and the `prefixCutoff_le_log_of_polyBounded` and
`recursionCutoff_le_log_of_polyBounded` theorems keep it logarithmic
even for normal inputs whose lengths are polynomial in the physical
input length.

The machine construction has reusable components and concrete
soundness theorems:

| Module under `Oitavem/Machine/` | Implemented result and intended reuse |
| --- | --- |
| [Read.lean](../Geb/Prototypes/Computability/Oitavem/Machine/Read.lean) | `inputLength_transformsIn`, `storedLength_transformsIn`, `inputAt_transformsIn`, and `readStored_transformsIn` provide length and digit readers with caller preservation, scratch handling, parked heads, and execution bounds. |
| [While.lean](../Geb/Prototypes/Computability/Oitavem/Machine/While.lean) | `arrives_whileNonblank` supports loop invariants over the whole configuration, including emitted output. |
| [CountOutput.lean](../Geb/Prototypes/Computability/Oitavem/Machine/CountOutput.lean) | `countOutput_runsTo` counts an emitter's output without storing it, using one extra counter tape; `lengthMachine_computable` gives composition with numerical length in Oitavem's encoding. |
| [ReadOutput.lean](../Geb/Prototypes/Computability/Oitavem/Machine/ReadOutput.lean) | `readOutput_runsTo` reads a runtime-selected output digit using a countdown and result tape. It returns `(w[query]?).toList`, distinguishing a false bit from an absent bit, and preserves the caller's output and the emitter's final tapes and heads. |
| [Repeat.lean](../Geb/Prototypes/Computability/Oitavem/Machine/Repeat.lean) | `computableInTimeAndSpace_squareWord` proves quadratic time and logarithmic space for the quadratic-output example. `squareLength_runsTo` and `squareDigit_runsTo` verify its generated-word readers; `computableInTimeAndSpace_length_squareWord` proves cubic time and logarithmic space for numerical length after `squareWord`. |

The output-counting and digit-reading contracts assume a halting
emitter and run it to completion. They provide access to finite
generated words; their present contracts do not give an observation
reader for an emitter that runs forever. Both preserve the simulated
machine's final state of tapes and heads, so scratch cleanup and
return-position obligations must come from the generator's contract.

General reader allocation and substitution, repeated-query setup and
scratch reset, the retained-prefix recursion machine, and the remaining
constructor cases still require machine proofs. The
numerical-length-after-`squareWord` theorem uses the
semantic identity `eval_lengthByRec`; it does not compile the general
safe-recursion scheme. A syntax-wide soundness theorem for all Oitavem
expressions is therefore still required. The
[direct soundness guide](oitavem-logspace-soundness.md) describes these
remaining steps. Build on its machine components for the finite part
of a stream compiler; the bitstream equivalences supply the separate
connection between data representations.

The proposed extension requires the following results:

| Construction | Required result |
| --- | --- |
| Shared indexed syntax | Decidable syntactic admissibility; preservation of each included fragment's typing and interpretation |
| Oitavem incremental implementation | Extend the implemented readers and concrete machines with general substitution and retained-prefix recursion; prove termination, agreement with `Expr.eval`, and logarithmic space for all expressions |
| Strict corecurrence interpretation | Defining observation equations, productivity, and the applicable tier-dependent locality and space bounds |
| Delayed interpretation | Step semantics and an explicit relation to meaningful output, stopping, and source collapse |
| Oitavem-to-stream compiler | Total finite restriction and equality with the source interpretation |
| Composition between fragments | Preservation of typing, definedness guarantees, and the particular resource bound claimed |
| Additional polynomial data types | A representation, access model, and resource theorem appropriate to those types |

The resource constants may depend on a fixed program. These targets
do not assert a universal logspace interpreter when the program is
itself part of the input. A denotational fold into complete lists also
does not establish bounds for an implementation that materializes
intermediate words.

## Implementation sequence

1. Preserve the existing Oitavem syntax and interpretation as the
   finite reference fragment. State its intended finite-stream
   observation relation using the bitstream W-to-M inclusion and
   `seqEquiv_ofW`.
2. Implement the stream fragment with explicit symbol/stream sorts
   and tier rules, first for bits. Interpret strict corecurrence with
   `Geb.BitStream.WConstruction.corec` and use its observation and
   comparison equations. Include the simultaneous form required by
   the source system.
3. Extract shared signature and interpretation constructions from
   those concrete instances. Form the indexed coproduct and prove
   inclusion and interpretation preservation. Initially permit only
   compositions already justified within each source fragment.
4. Complete the Oitavem machine compiler by composing its existing
   readers and implementing the retained-prefix recursion machine
   and remaining constructor cases.
   Develop strict stream resource proofs against an explicit access
   model. These developments can proceed independently; neither is a
   prerequisite for defining the other's syntax.
5. Add delayed computation and its observation relation when connecting
   the finite fragment to the general stream model. Prove finite-input
   termination for the compiled finite fragment, including completion
   of empty outputs. Relate the representation to the paper's padding
   and collapse conventions.
6. Construct the translation into pure ramified corecurrence if that
   presentation is required. Add further compositions or polynomial
   data types only with their typing and resource arguments.

Checks should include identity on infinite streams, an infinite
constant stream, finite length parity, empty finite output, and an
infinite silent computation. Extend the existing
[W-construction checks](../GebTests/Prototypes/BitStream/WConstruction.lean),
which exercise finite and infinite observations and the constructor/tail
operations. The first examples distinguish productive programs and
finite functions; the last distinguishes step productivity from data
productivity and requires the delayed representation. These checks
supplement the general Lean theorems and do not replace them.

## References

Bibliographic records are maintained in [references.bib](references.bib).

- [Oitavem2010] — Definition 3.1 and Theorem 3.4: the finite algebra
  and its logspace characterization.
- [LeivantRamyaa2015] — §§3–4: strict and lazy ramified corecurrence;
  §5: finite-stream representation and the finite logspace result.
- [DannerRoyer2012] — §§2–3: polynomial data/codata, ramified folds
  and unfolds, and restrictions selecting complexity classes.

[Oitavem2010]: https://doi.org/10.1515/9783110324907.355
[LeivantRamyaa2015]: https://doi.org/10.1007/978-3-662-46678-0_27
[DannerRoyer2012]: https://arxiv.org/abs/1201.4567v2
