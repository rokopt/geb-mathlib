# Direct logspace soundness for Oitavem's Logs

This document proposes a direct machine proof for the
[Oitavem prototype][oitavem]. The syntax, truncation results, polynomial
output-length bound, and logarithmic retained recursion state are
formalized. The compiler and its machine soundness theorem remain to be
constructed. Physical-input and stored-word readers, an emitting loop
rule, a generated-output length reader, and a concrete transducer for
`squareWord` are proved
using the existing `SizeBounded` and `SizeBounded/Logspace` libraries.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Objective](#objective)
- [Existing formal results](#existing-formal-results)
- [Reusing the machine libraries](#reusing-the-machine-libraries)
- [Generated-word readers](#generated-word-readers)
- [Constructor proofs](#constructor-proofs)
  - [Initial functions](#initial-functions)
  - [Normal composition](#normal-composition)
  - [Safe recursion](#safe-recursion)
  - [Concatenation recursion](#concatenation-recursion)
  - [Log-transition](#log-transition)
- [Halting, space, and time](#halting-space-and-time)
- [Implementation checkpoints and effort](#implementation-checkpoints-and-effort)
- [References](#references)

<!-- END doctoc -->

## Objective

For each fixed Logs expression, construct a deterministic CSLib
multi-tape transducer that computes its interpretation, halts on every
input, and uses logarithmic work space. Apply the existing
`Geb.Oitavem.Machine.computes_polytime_logspace` theorem to obtain a
polynomial time bound on that same machine.

For `e : Expr 1 0`, the target function is
`fun w ↦ e.eval ![w] Fin.elim0`. With `n = w.length`, the bounds should
have the form `C * (n + 1) ^ d` for time and `C * (n.size + 1)` for
space. The constants and number of work tapes may depend on `e`.
The constructor proofs must handle environments of arbitrary normal
arity and the permitted safe argument. A theorem for encoded tuples
also needs verified readers for that input encoding.

The expression is fixed before execution; this is a compiler soundness
theorem. Its bounds do not assert a uniform logarithmic-space evaluator
when the expression itself is part of the input. All resource proofs
belong to the compiler: constructing a Logs expression continues to
require only the syntactic arity conditions.

[Oitavem2010], Definition 3.1, supplies the algebra. The chapter proves
soundness through the Clote–Takeuti characterization in § 2 and
Theorem 3.4. The proposed machine construction uses the truncation
argument directly, without formalizing that intermediate algebra.
Completeness is outside this construction's scope.

## Existing formal results

- [Syntax][syntax] defines the algebra as a slice polynomial W-type,
  its interpreter, and the recursor-based theorem `Expr.induction`.
  The current syntax suffices for the proposed compiler.
- [Truncation][truncation] constructs `Expr.truncationBound` and proves
  `Expr.truncates_truncationBound`, formalizing the safe-input truncation
  argument of Lemma 3.3.
- [Length][length] defines the executable bound `lengthPoly` and proves
  `Expr.length_le_poly`. Output length is polynomial in the maximum
  normal argument length, independently of safe argument length.
- [Recursion][recursion] proves `Expr.exists_logarithmic_prefix`: each
  expression only needs a logarithmic prefix of its safe input. It also
  defines `prefixLoop` and proves `Expr.exists_logarithmic_loop` and
  `evalRec_cons_prefixLoop`, relating a loop retaining such prefixes to
  full safe recursion. `Expr.prefixCutoff` and `Expr.recursionCutoff`
  compute suitable cutoffs from syntax. Their logarithmic bounds allow
  normal arguments of polynomial length in the original physical input.
- [Space and time][space-time] proves `computes_polytime_logspace` for
  any halting deterministic transducer with a global logarithmic-space
  bound. The proof counts configurations with the write-only output
  omitted.
- [Derived operations][derived] supplies `Expr.boundedRec`, the
  recursive length example `lengthByRec`, and `squareWord`, whose
  output length is exactly the square of its input length.
- [Readers][readers] proves `inputLength_transformsIn`, `storedLength_transformsIn`,
  `inputAt_transformsIn`, and `readStored_transformsIn`. Digit queries
  count from the list head and return the empty word outside the word.
  These contracts include scratch initialization, caller preservation,
  parked heads, and bounds throughout execution.
- [Emitting loops][emitting-loops] proves `arrives_whileNonblank` with
  an invariant over the whole configuration, including growing output.
- [Output counting][output-counting] proves `countOutput_runsTo`:
  an emitter becomes a length reader by adding one binary counter tape.
  The simulated machine's final tapes and heads are preserved exactly;
  the wrapper emits nothing. Counter space depends on output length,
  and finite control remains finite. A bit emitted by the halting
  transition is counted before the wrapper halts. Scratch cleanup and
  parked return heads must still follow from the generator's contract.
  `emitNumber_emits` converts a counter to Oitavem's shortlex encoding;
  `lengthMachine_computable` packages post-composition with numerical
  length as CSLib machine computability with explicit resource bounds.
- [Repeated-input emission][repeat] implements `squareMachine` on one
  work tape. `computableInTimeAndSpace_squareWord` proves CSLib's
  simultaneous bounds `32 * (n + 1)^2` for time and
  `32 * (n.size + 1)` for work space, with identity encodings. This
  computes `squareWord` itself. `squareLength_runsTo` applies the generic
  output counter: two work tapes count the quadratic word in at most
  `224 * (n + 1)^3` steps, with all heads in
  `[-1, 2 * n.size + 1]`.
  `computableInTimeAndSpace_length_squareWord` computes the interpretation
  of `Expr.comp lengthByRec ![squareWord]`, emitting its shortlex result
  in time `256 * (n + 1)^3` and space `6 * (n.size + 1)`.
  Generated digit queries and substitution into
  another expression's normal-input readers remain to be implemented.
- [Machine checks][machine-checks] execute the readers and transducer,
  including leading zeroes, empty words, out-of-range queries, dirty
  scratch tapes, protected registers, and existing output prefixes.

The recursion results bound retained words and indices. They do not
bound the work space used to compute those words or indices. Closing
that distinction requires the machine construction below.

## Reusing the machine libraries

Reuse the finite-control [program type `Prog`][prog], sequencing,
counter operations, [input lookup][read-input], and [loops][while].
The [valuation contract `TransformsIn`][contract] already describes
halting subroutines with parked heads and a bound throughout their
runs. The existing [compiler correctness contract][correct] provides
the register-allocation and preservation pattern needed when a caller
retains data across a subcall. [Output contracts][emit] connect such
runs to emitted words and CSLib's space measure.

The old [representation `Rep`][rep] denotes a short stored word
followed by a suffix of the physical input. Its compiler bounds the
stored part by an expression-dependent constant. This representation
does not cover general Logs outputs: `squareWord` alone can produce a
quadratically long word. Such generated words can occur in normal
argument positions and as recursion inputs.

Extend the compilation method with routines that read generated words.
The initial target is the structured programs produced by this compiler.
A general composition theorem for arbitrary CSLib transducers would
also suffice, but would require separate simulation, tape-reset, and
state-restoration machinery. It is not a prerequisite for this route.

## Generated-word readers

Represent access to a word by verified machine routines for its exact
length and its digit at a requested position. A word may be the
physical input, a stored logarithmic prefix, a segment of another word,
or the output of a child expression. The routines are actual finite
CSLib programs. A Lean function supplying digits without a machine
implementation would not establish soundness.

Each reader contract must establish:

1. Agreement with the represented word, including its length, digit
   order, and the convention for positions outside the word.
2. Halting for every permitted query and environment.
3. A bound throughout the run, measured against the length of the
   original physical input, including scratch tapes and head movement.
4. Preservation of the caller's protected registers, including saved
   recursion prefixes, indices, and the reader's own environment.
5. Parked heads on return and a scratch-register convention that
   supports repeated calls. Initializing reused scratch registers must
   be part of the verified routine.
6. No emission to the final output tape during internal queries.

Code for the readers and their call sites is fixed by the expression.
Runtime data consists of indices, lengths, and stored short words.
The compiler must prove that its number of simultaneously retained
call contexts is bounded by a constant depending on the expression.
Input-length iteration must reuse those contexts.

For physical input length `n`, every generated normal word should have
a bound `p(n)` for a fixed polynomial bound `p`. Thus an index into it
requires `O(log(n + 2))` bits. This needs an environment invariant:
knowing a child routine is logarithmic in its own virtual input length
is insufficient until that length is related to `n`.

The representation preserves leading zeroes. The [word model][word]
stores the paper's words in reverse order, so the beginning of a Lean
list contains the least significant digits. Reader indexing and the
final emitter must consistently use this convention. Prefixes in
`Expr.exists_logarithmic_prefix` refer to this Lean representation.

## Constructor proofs

### Initial functions

Implement each initial function by length and digit routines. String
successor, string predecessor, iterated string predecessor, projections,
and the conditional reduce to length tests and index changes. Zeroes
and last-digit extraction use constant output or a single digit query,
respecting the empty-word case. String
product uses a product of lengths and an index modulo the repeated
word's length, with an explicit empty-word case. These counters are
polynomially bounded in the physical input length.

Numeric successor, predecessor, and subtraction require digitwise
carry or borrow routines for the shortlex encoding. An arbitrary
normal word may have polynomial length; its `rank` can require that
many bits. Its rank must therefore be accessed digitwise rather than
materialized in a work register. Output-length calculation must also
handle carries, saturation at zero, and changes of shortlex length.
The length primitive only encodes a polynomially bounded word length,
so its numerical result can be held in logarithmic space.

### Normal composition

For `g(r₁(x), …, rₘ(x); y)`, instantiate the argument readers of `g`
with the output readers compiled for the `rᵢ`. On a query, recompute
the requested information while preserving the caller's live data.
The [standard logspace composition argument][savage] uses this
recomputation to avoid storing an intermediate output. Here the proof
obligation is to realize that argument with the structured reader
contracts and their actual work tapes.

Polynomial output-length bounds compose. The workspace proof must
count caller storage and the active callee together, rather than only
the maximum size of their return values. The fixed compiled call
structure must justify the constant bound on nested contexts.

### Safe recursion

Use `prefixLoop` as the semantic invariant of an indexed machine loop.
Choose a cutoff sufficient for both step expressions and all prefixes
of the recursion input. If their normal argument lengths are bounded
by `N`, the existing theorem supplies a cutoff of the form
`C * (N.size + 1)`. The environment invariant relates `N` to a
polynomial bound in the physical input length.

Initialize the saved prefix from the base expression. At each
iteration, read the next recursion digit and provide the step routine
with a reader for the corresponding recursion prefix and a reader for
the saved safe value. Compute only the required prefix of the next
value. Retain the old prefix while the step still reads it; two
logarithmic buffers suffice for this part of the state.

The machine iterates over the recursion input using a counter. It must
not retain one call frame per input digit. Calls within an iteration
are to the compiled child expressions and their argument readers.

For empty recursion input, the output is the full base result. For a
nonempty input, `evalRec_cons_prefixLoop` permits the final step to
produce the full result from the retained penultimate prefix. A length
or digit query for that result can rerun the loop and then query that
final step. The logarithmic cutoff limits the saved recursive value;
the result itself may be polynomially long.

`Expr.recursionCutoff h N` is the maximum of the two branch cutoffs,
each computed as the binary size of `lengthPoly` for the branch's
`truncationBound`. `Expr.eval_safeRec_cons_prefixCutoff` verifies the
final step using this cutoff. The cutoff remains logarithmic when
`N` is polynomial in physical input length. Implementing its computation
and the retained-prefix loop on work tapes remains part of compilation.
No boundedness proof is added to the expression syntax.

### Concatenation recursion

The result consists of the base word and one digit per recursion
step. A requested digit identifies either a base-word position or a
step expression applied to the appropriate recursion prefix. Step
expressions receive no previous recursive result. The machine can
therefore answer digit queries independently using length counters and
prefix readers, and emit the complete answer by iterating over output
positions in the representation's order.

### Log-transition

Use the proved closed form from [the semantics][basic]: the child
receives a normal offset whose rank is
`rank z + min(iterationWord.length, rank safe)`.
By `cappedRank_take_size`, the capped safe contribution can be computed
from a logarithmic prefix. That contribution is a small integer because
the iteration word has polynomially bounded length.

The offset `z` can still be a long normal word. Construct a reader for
its shortlex sum with the capped contribution using digitwise
arithmetic, then invoke the child through that reader. Materializing
`rank z` would violate the proposed space bound.

## Halting, space, and time

Prove reader correctness and termination by the existing syntax
recursor, using finite counter loops for recursion on input words.
The combined invariant must include the polynomial bounds on virtual
lengths, register separation, preservation, and scratch initialization.
Length and digit routines must have a terminating call structure;
their mathematical specifications alone do not supply one.

For a fixed expression, bound the length of every work register and
every work-head excursion by `O(n.size + 1)`. The number of tapes and
simultaneously live contexts is fixed by compilation. Convert the run
bounds to CSLib's total `spaceUsed` bound, including initialization,
subcalls, and final emission. Establish the bound for all times, as
required by `computes_polytime_logspace`.

Then prove that the emitter halts with exactly the expression's output
and apply that theorem. This avoids a separate polynomial-time
calculation for every recomputation. Existing subroutine time bounds
remain usable to prove termination; the final polynomial bound follows
from halting and the global space bound on the completed machine.

## Implementation checkpoints and effort

| Checkpoint | Required evidence |
| --- | --- |
| Reader contract and base readers | Verified physical-input and stored-prefix readers, including repeated calls and caller preservation. |
| General reader composition | A verified substitution rule for generated length and digit readers, exercised on polynomially long virtual inputs. |
| Safe recursion over a generated word | A machine for `lengthByRec` composed with `squareWord`, using the saved-prefix loop and querying the generated recursion input. |
| Remaining constructor closure | Machine length and digit routines for every initial function, concatenation recursion, and log-transition. |
| Full soundness | Syntax-wide compiler correctness, exact final output, global logarithmic space, and simultaneous polynomial time for the resulting machine. |

The first checkpoint has verified physical-input and stored-word length
and digit routines. `countOutput` also supplies length readers for generated
words, and `squareLength_runsTo` verifies that construction on quadratic
output. Numerical length composed with `squareWord` has a full machine
bound theorem. That proof uses `eval_lengthByRec` to compute the length
directly; it does not implement the retained-prefix recursion loop.
Generated digit readers and the general allocation and substitution
contracts remain.

The first composition checkpoint should determine whether the proposed
reader contract supports the required register allocation and nested
calls. The safe-recursion checkpoint then tests whether the contract
remains adequate with a live saved prefix. These checkpoints require
machine proofs; executable semantic examples alone do not meet them.

The effort estimate is several extended formalization sessions,
potentially several days, rather than a few-hour completion commitment.
Reader composition and register preservation carry the most design
uncertainty. Shortlex arithmetic and the recursion machine proofs are
substantial additional work. Once their contracts compose, the final
syntax recursor and application of the time theorem should be smaller
parts of the development. These estimates describe the proposed proof
route, not a measured implementation schedule.

Completeness can be considered separately after soundness. The existing
`boundedRec` construction formalizes the constructor used in the
chapter's Lemma 3.2, but it does not yet relate arbitrary logspace
machines to Logs expressions. A future completeness proof would need
that additional characterization or a direct machine encoding.

## References

- [Oitavem2010] — Isabel Oitavem, *Logspace without Bounds*,
  Definitions 2.1 and 3.1, Lemmas 3.2 and 3.3, and Theorem 3.4.
  Bibliographic metadata is in [references.bib](references.bib).
- [John E. Savage, *Complexity Classes III*][savage], CS256 lecture
  slides 5–9: logspace composition by recomputing intermediate output
  and the configuration-counting time argument.
- [Peter Clote, *Computation Models and Function Algebras*][clote],
  Definition 3.21 and Theorem 3.22, manuscript p. 28: the sharply
  bounded recursion scheme and arithmetic FLOGSPACE characterization.
  The theorem cites the Clote–Takeuti work; this passage states the
  characterization without its proof.

[oitavem]: ../Geb/Prototypes/Computability/Oitavem.lean
[syntax]: ../Geb/Prototypes/Computability/Oitavem/Syntax.lean
[truncation]: ../Geb/Prototypes/Computability/Oitavem/Truncation.lean
[length]: ../Geb/Prototypes/Computability/Oitavem/Length.lean
[recursion]: ../Geb/Prototypes/Computability/Oitavem/Recursion.lean
[space-time]: ../Geb/Prototypes/Computability/Oitavem/Machine/SpaceTime.lean
[readers]: ../Geb/Prototypes/Computability/Oitavem/Machine/Read.lean
[emitting-loops]: ../Geb/Prototypes/Computability/Oitavem/Machine/While.lean
[output-counting]: ../Geb/Prototypes/Computability/Oitavem/Machine/CountOutput.lean
[repeat]: ../Geb/Prototypes/Computability/Oitavem/Machine/Repeat.lean
[machine-checks]: ../GebTests/Prototypes/Computability/Oitavem/Machine.lean
[derived]: ../Geb/Prototypes/Computability/Oitavem/Derived.lean
[word]: ../Geb/Prototypes/Computability/Oitavem/Word.lean
[basic]: ../Geb/Prototypes/Computability/Oitavem/Basic.lean
[prog]: ../Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Basic.lean
[read-input]: ../Geb/Prototypes/Computability/SizeBounded/Logspace/Machine/Primitives/ReadInput.lean
[while]: ../Geb/Prototypes/Computability/SizeBounded/Logspace/Machine/While.lean
[contract]: ../Geb/Prototypes/Computability/SizeBounded/Logspace/Machine/Contract.lean
[correct]: ../Geb/Prototypes/Computability/SizeBounded/Logspace/Machine/Compile/Correct.lean
[emit]: ../Geb/Prototypes/Computability/SizeBounded/Machine/Emit.lean
[rep]: ../Geb/Prototypes/Computability/SizeBounded/Logspace/Rep.lean
[Oitavem2010]: https://doi.org/10.1515/9783110324907.355
[savage]: https://cs.brown.edu/courses/csci2560/lectures/lect.03.pdf#page=5
[clote]: https://kleidi.bc.edu/clotelab/pub/cloteHandbookRecTheory.pdf#page=28
