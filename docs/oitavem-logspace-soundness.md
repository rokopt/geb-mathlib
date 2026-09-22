# Direct logspace soundness for Oitavem's Logs

Direct machine soundness for the [Oitavem prototype][oitavem] is proved
by [`Expr.computable_polytime_logspace`][realizer-recursion]. For every
fixed `e : Expr 1 0`, a finite deterministic CSLib transducer computes
`fun w ↦ e.eval ![w] Fin.elim0` in simultaneous polynomial time and
logarithmic work space, with identity input and output encodings.

`Expr.realized` proves the stronger substitution property for every
constructor over polynomially bounded generated arguments and a
protected environment. Safe recursion retains logarithmic prefixes of
intermediate results and emits the complete final step. Concatenation
recursion streams indexed step digits before its base output.
Log-transition uses its verified expression in initial functions and
normal composition. The machine theorem has exactly the existing CSLib
axiom dependencies `propext`, `Classical.choice`, and `Quot.sound`.

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
- [Verified checkpoints and scope](#verified-checkpoints-and-scope)
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
Theorem 3.4. This machine construction uses the truncation
argument directly, without formalizing that intermediate algebra.
Completeness is outside this construction's scope.

## Existing formal results

- [Syntax][syntax] defines the algebra as a slice polynomial W-type,
  its interpreter, and the recursor-based theorem `Expr.induction`.
  Machine realization uses this syntax without additional certificates.
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
- [Space and time][space-time] proves `computes_of_space` for any
  halting deterministic transducer with a global work-space bound: its
  time is exponential in that bound. The proof counts configurations
  with the write-only output omitted. `computes_polytime_logspace` is
  the instance at a logarithmic bound and `computes_expspace` the
  instance at an exponential one.
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
- [Generated digit reading][output-reading] proves `readOutput_runsTo`:
  a fixed emitter gains two tapes, a runtime query countdown and a
  one-bit result. It returns `(w[query]?).toList`, distinguishing a
  false bit from a missing bit, and emits nothing. It preserves the
  emitter's exact final tapes and heads, including when the halting
  transition emits a bit. The result tape must initially be blank;
  the query is consumed to `query - w.length`. The wrapper takes at
  most `t * (2 * B + 8)` steps, with every work head in `[-1, B]`,
  when the emitter has that head bound and `query.size ≤ B`.
  Finite control remains finite. This proof was developed with
  Aristotle and checked under the repository's toolchain.
- [Generated subroutine contracts][generated] defines `EmitsIn`, the
  emitting counterpart of `TransformsIn`, with a bounded final valuation
  and parked return heads. `generatedLength_transformsIn` and
  `generatedAt_transformsIn` turn such an emitter into reusable readers.
  Length queries clear their counter before running. Digit queries copy
  a saved query, clear the result before running, and clear the consumed
  countdown on return, including for out-of-range queries. The extra
  tapes may be dirty on entry. The generator's exact valuation
  transformer determines cleanup and preservation on its old tapes;
  preserving the saved query therefore requires that the generator
  preserve its source tape. The wrapper bounds are
  `4 * B + 9 + T * (2 * B + 5)` and
  `T * (2 * B + 8) + 13 * B + 30` steps, respectively, at the same
  work-head bound `B`. `TransformsIn.seqEmitsIn` composes an internal
  query with a subsequent emitter.
- [Tape allocation][allocation] defines `onTapes` from an explicit
  partition of the caller's tapes into callee and protected tapes.
  `onTapes_runFrom` proves exact simulation at every step, with the
  protected tapes and heads unchanged. `EmitsIn.onTapes` and
  `TransformsIn.onTapes` preserve the original time and head bounds.
  The state type is unchanged, so allocation preserves finite control.
- [Streaming readers][streaming-readers] defines `ReadsAt`, a digit
  contract for queries through the first out-of-range position. Each
  call preserves every register except its result. Physical-input,
  stored-word, and generated-output readers satisfy this contract when
  their scratch registers have the initialized contents they restore.
  `ReadsAt.onTapes` places the reader in a larger caller layout.
  `emitReader_emitsIn` streams the word through successive queries,
  retaining its index and digit, and returns its length in the query
  register. `generatedAt_all_queries` also verifies arbitrary canonical
  queries beyond a generated word's end, returning a missing digit.
  `ReadsAtAll` records this stronger reader contract for padded arithmetic.
  Its precondition and represented word must be independent
  of the query and result registers. For reader time `T`, word-length
  bound `N`, and head bound `B`, it uses at most
  `4 * B + 9 + T + N * (T + 2 * B + 6) + 1` steps at head bound `B`.
- [Contract realization][generated] proves
  `EmitsIn.computes_polytime_logspace`: a finite emitter whose
  precondition holds on blank registers and whose head bound is
  logarithmic yields simultaneous polynomial time and logarithmic
  space on that emitter preceded by one input-head homing step.
  `Emits.spaceUsed_le_all` supplies the space bound at every time,
  including after halting. No polynomial assumption on the emitter's
  termination bound is required.
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
  `squareDigit_runsTo` answers queries through position `n^2`, including
  that first out-of-range position, in time `320 * (n + 1)^3` with
  three tapes and head bound `2 * n.size + 1`.
  `squareInput_emits` also permits dirty generator scratch and proves
  its cleanup and caller preservation. `squareFromHome_emitsIn` adapts
  that generator to the subroutine convention. `squareLength_transformsIn`
  and `squareAt_transformsIn` establish its reusable reader contracts
  with protected caller registers and arbitrary initial scratch contents.
- [Repeated generated emission][repeat] proves `repeatGenerator_emitsIn`:
  a generator that preserves its valuation can be called repeatedly
  using a binary countdown and a fixed set of work tapes. Its word and
  precondition must be independent of the countdown. Applied after
  the generated square's length reader, this constructs
  `squareSquareMachine`. The theorem
  `computableInTimeAndSpace_squareWord_squareWord` proves that it
  computes `Expr.comp squareWord ![squareWord]`, with quartic output,
  in time `512 * (n + 1)^4` and space `6 * (n.size + 1)` on two tapes.
  It counts the intermediate output and regenerates it for each repetition.
  `squareSquareFromHome_emitsIn` also proves initialization and cleanup
  from dirty work tapes. This is a composition through a generated
  length reader and an emitter. The general substitution theorem below
  extends this construction to arbitrary expressions.
- [Streaming generated digits][repeat] implements
  `squareViaReaderMachine`, which reconstructs `squareWord` entirely
  through generated digit queries on four work tapes.
  `squareViaReaderFromHome_emitsIn` verifies scratch initialization,
  repeated calls, and preservation of other caller registers.
  `squareViaReaderMachine_computes` proves simultaneous polynomial time
  and logarithmic space for that machine using contract realization.
- [Machine checks][machine-checks] execute the readers and transducer,
  including leading zeroes, empty words, out-of-range queries, dirty
  scratch tapes, protected registers, existing output prefixes, repeated
  generated-reader calls, the quartic-output composition, and streaming
  through generated digit queries. Allocated-reader checks move scratch
  past a protected caller tape whose head starts away from zero.
- [Streaming constructor rules][constructors] prove numerical length,
  string successor, string product, and the conditional for generated arguments.
  `productGenerator_emitsIn` counts the second argument and regenerates
  the first argument once per counted digit, using one additional tape.
  [Finite-state output transformations][output-maps] preserve the
  original work-head bound and add one final flushing step.
  [Initial-function transducers][initial-machines] apply this rule to
  numerical successor and saturated predecessor, string predecessor,
  and last-digit extraction, including the empty-word cases.
- [Index arithmetic][index-arithmetic] provides counter addition and
  saturating subtraction. [Segment readers][segments] translate a
  query into an index of a source word, preserving the saved offset
  and clearing the addition scratch. The offset is at most the source
  length; queries include the first position after the segment.
  `minCounter_transformsIn` clamps a binary counter to a saved bound.
  `iterPredGenerator_emitsIn` uses this clamp to handle arbitrary
  iteration counts, including counts longer than the source word,
  and streams the suffix with cleared query ports.
- [Digitwise subtraction][subtraction] proves
  `shortlexSub_eq_numericSub` for the existing shortlex encoding.
  The scan carries a signed value between minus one and one through
  the paired sentinel digits, then removes trailing zeroes and the
  sentinel. This constructive arithmetic proof was developed with
  Aristotle and adapted and verified locally.
  [The subtraction machine][subtraction-machine] now proves
  `numericSubGenerator_emitsIn`: virtual length and sentinel-digit
  readers determine the loop bound, then two scans compute the sign,
  significant index, and canonical output. Seven working ports contain
  only digits and binary counters. All are cleared on return, and the
  argument readers retain their common space bound. Executable checks
  cover 256 word pairs with reused counters and protected caller tapes.
- [Output-prefix capture][capture] retains a mask-bounded prefix while
  continuing the generator to its own halt. The low-level simulation
  `captureOutput_runsTo` was developed with Aristotle and verified
  under the repository's toolchain. `generatedPrefix_transformsIn`
  initializes and clears capture scratch, parks every head, and copies
  the captured prefix into a saved register only after the generator
  returns. The generator can read the previous saved value throughout
  its run.
- [Retained-prefix machine loops][machine-recursion] proves
  `retainedLoop_transformsIn`: a binary countdown iterates a generator,
  replacing the saved word by each captured prefix. Its indexed
  invariant records all registers, including mask and scratch.
  `lengthRecLoop_transformsIn` instantiates it with `prefixLoop` for
  `lengthByRec`, using backwards digit queries into the recursion input.
- [Recursive length over generated input][recursive-length] implements
  `squareRecLengthMachine`. The machine counts the generated square to
  initialize its countdown and mask, then computes the recursive value
  from the empty base using digit queries and saved-prefix replacement.
  `squareRecLengthMachine_computes` proves simultaneous polynomial time
  and logarithmic space on this eight-tape machine. All work heads stay
  in `[-1, 2 * n.size + 1]` and the work tapes are cleared on return.
  Execution checks cover the recursive implementation, streaming carry
  and borrow, segment boundaries, zero-length masks, and dirty capture
  scratch.
- [Generators over a protected environment][realizer] package a fixed
  finite emitter whose scratch tapes start and finish blank. The
  contract holds for every sufficiently large workspace bound.
  `Generator.rename` copies selected caller registers into a private
  environment and clears it after the call; repeated selections are
  permitted. Allocation combines independently compiled generators.
  The interface covers physical input, stored words, and all initial
  functions. [Generated reader adapters][realizer-readers] return length
  and digit answers to designated caller registers, clear their private
  workspace, and preserve a common caller layout. Digit queries may
  exceed the generated word's length. [Initial-function assembly][realizer-initials]
  supplies subtraction, iterated predecessor, and conditional selection.
  `Initial.realize` proves closure under every initial function for
  polynomially bounded generated arguments. `Generator.computes` supplies
  simultaneous polynomial time and logarithmic space for closed
  generators. Execution checks cover nested arithmetic and product with
  a source register supplied to both argument slots, generated reader
  calls, and the assembled arithmetic, segment, and conditional machines.
- [Compositional realization][realizer-compile] defines `Expr.Realized`:
  any polynomially bounded family of virtual arguments over a protected
  environment can be replaced by generators. `Expr.Realized.comp`
  assembles finite families of child witnesses constructively and uses
  their syntax-derived output bounds. `Expr.Realized.logTransition`
  realizes the derived normal expression with the safe value supplied
  as an extra normal argument.
- [Indexed generator assembly][realizer-loop] proves `Generator.indexed`
  and `Generator.withLength`. They initialize generated binary lengths,
  run restoring continuations or indexed steps, and clear the counters.
  [Retained generator assembly][realizer-retained] constructs logarithmic
  capture masks and proves `Generator.retained`, including the base
  capture, every intermediate step, full final output, and cleanup.
- [Syntax-wide realization][realizer-recursion] proves closure under
  both recursion schemes and `Expr.realized` by the syntax recursor.
  `Expr.computable_polytime_logspace` combines this result with
  `Expr.Realized.computes` and the finite-configuration time theorem.
  Its machine and both complexity bounds refer to the same transducer.

The machine construction below bounds both the retained data and the
workspace used by every subcall that computes it.

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

`productGenerator_emitsIn` supplies string product for arbitrary
restoring argument generators. `lengthGenerator_emitsIn` supplies
numerical length. Generated length and digit wrappers apply to both
outputs. `numericSuccGenerator_emitsIn`, `numericPredGenerator_emitsIn`,
`predGenerator_emitsIn`, and `lastGenerator_emitsIn` implement their
unary constructors through finite-state output transformations.
`iterPredGenerator_emitsIn` combines argument-length readers with a
saturating segment generator. `condGenerator_emitsIn` counts the selector
and invokes the appropriate branch. `numericSubGenerator_emitsIn`
implements numerical subtraction on virtual words using length and
sentinel-digit readers. It includes counter initialization, sign handling,
shortlex normalization, and cleanup; its output is linked to the word
model by `shortlexSub_eq_numericSub`.

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

The `Generator` interface provides fixed private layouts, uniform
workspace bounds, restoring calls, and environment substitution.
`Initial.realize` supplies every initial constructor in this interface.
`Expr.Realized.comp` instantiates the head with its child generators,
using `lengthPoly` to obtain a common polynomial bound for their outputs.
Finite families of witnesses are assembled with `Nat.rec`.

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

`generatedPrefix_transformsIn` supplies bounded capture and replacement,
and `retainedLoop_transformsIn` supplies the indexed loop with reusable
tapes. `lengthRecLoop_transformsIn` uses `prefixLoop` as its invariant.
The eight-tape `squareRecLengthMachine` verifies this recursion over
generated input with a live saved value and digit queries.

`Expr.recursionCutoff h N` is the maximum of the two branch cutoffs,
each computed as the binary size of `lengthPoly` for the branch's
`truncationBound`. `Expr.eval_safeRec_cons_prefixCutoff` verifies the
final step using this cutoff. The cutoff remains logarithmic when
`N` is polynomial in physical input length.

`Generator.exists_prefixMask` supplies a sufficient executable mask.
For a cutoff bounded by `A * (n.size + 1)`, fixed string products stream
a word of length `(4 * (n + 1)) ^ A`. Its binary length is logarithmic
and at least the required cutoff. `Generator.withLength` stores that
binary length in a protected register for `Generator.retained`.

`Expr.Realized.safeRec` realizes the base and step expressions, supplies
generated suffixes and the saved safe value, and instantiates the
retained machine with `prefixLoop`. It handles the empty input by
emitting the base directly; otherwise the final step emits its full
answer. All bounds belong to realization, so the expression syntax
still requires only arity conditions.

### Concatenation recursion

The result consists of the base word and one digit per recursion
step. A requested digit identifies either a base-word position or a
step expression applied to the appropriate recursion prefix. Step
expressions receive no previous recursive result. The machine can
therefore answer digit queries independently using length counters and
prefix readers, and emit the complete answer by iterating over output
positions in the representation's order.

`concatRec_eq_concatDigits` gives the output order explicitly: indexed
step digits first, followed by the base word.
`concatRecGenerator_emitsIn` implements this order with a countdown and
a forward index, given contracts for the indexed step and base.
`EmitsIn.whileReg` verifies the growing output invariant.
`emitPrefix_emitsIn` uses the same indexed loop to emit a specified
number of digits through a reader, storing only binary counters even
when the requested prefix is polynomially long.
`Expr.Realized.concatRec` instantiates these steps with generated
suffixes and compiled child expressions, then appends the base output.

### Log-transition

Use the proved closed form from [the semantics][basic]: the child
receives a normal offset whose rank is
`rank z + min(iterationWord.length, rank safe)`.
By `cappedRank_take_size`, the capped safe contribution can be computed
from a logarithmic prefix. That contribution is a small integer because
the iteration word has polynomially bounded length.

The offset `z` can still be a long normal word. The derived expression
`Expr.transitionOffset` computes its new value using only length,
string successor, string product, numerical subtraction, projection,
and normal composition. Two subtractions cap the safe value; three
more add the capped contribution by subtracting from a sufficiently
large virtual word. That upper word consists of
`iterationWord.length + 1` copies of `false :: z`, so its length is
polynomial in the normal word lengths. `Expr.eval_transitionOffset`
proves the exact offset.

`Expr.logTransitionNormal` supplies the safe input as an additional
normal input and invokes the child with this derived offset.
`Expr.eval_logTransitionNormal` proves equivalence to log-transition.
`Expr.Realized.logTransition` realizes this expression through normal
composition and the verified initial-function adapters. Its virtual
safe argument has the polynomial bound required by `Expr.Realized`;
the safe-recursion caller supplies a logarithmically bounded prefix.

[Bounded-carry addition][addition] also supplies a direct digit algorithm
and `shortlexAdd_eq_unrank_add`. It remains an alternative arithmetic
implementation; the derived subtraction expression needs no additional
addition machine.

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
`EmitsIn.computes_polytime_logspace` packages this final step for an
emitter contract whose precondition holds on blank registers.
`Expr.realized` constructs that contract for every expression.
`Expr.Realized.computes` supplies the physical input and empty safe
environment, and `Expr.computable_polytime_logspace` states the resulting
unary soundness theorem with identity encodings.

## Verified checkpoints and scope

| Checkpoint | Verified evidence |
| --- | --- |
| Reader contracts | Physical, stored, and generated length and digit readers preserve caller registers and restore scratch. |
| General substitution | `Expr.Realized.comp` substitutes independently realized normal arguments with a common polynomial length bound. |
| Initial functions and log-transition | `Initial.realize` covers every initial function; `Expr.Realized.logTransition` uses the derived normal expression. |
| Concatenation recursion | `Expr.Realized.concatRec` streams indexed child digits, then the base result. |
| Safe recursion | `Expr.Realized.safeRec` initializes a sufficient logarithmic mask, retains the semantic prefix invariant, and emits the full final result. |
| Full soundness | `Expr.realized` covers all syntax; `Expr.computable_polytime_logspace` supplies exact output and simultaneous bounds for a finite unary transducer. |

The constructor theorem permits arbitrary normal arities and the
permitted safe arity, with polynomially bounded virtual arguments over
any protected caller environment. The closed machine theorem uses one
physical input word and no safe inputs. Extending that interface to an
encoded tuple requires readers for the chosen encoding.

Generator constructors are executable. Machine witnesses for arbitrary
expressions are assembled constructively inside the realization theorem.
The expression is fixed before execution, and both complexity constants
and the number of tapes may depend on it. The final axiom audit reports
exactly `propext`, `Classical.choice`, and `Quot.sound`, inherited from
the machine framework, with no proof holes or additional axioms.

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
[output-reading]: ../Geb/Prototypes/Computability/Oitavem/Machine/ReadOutput.lean
[generated]: ../Geb/Prototypes/Computability/Oitavem/Machine/Generated.lean
[allocation]: ../Geb/Prototypes/Computability/Oitavem/Machine/Allocate.lean
[streaming-readers]: ../Geb/Prototypes/Computability/Oitavem/Machine/Reader.lean
[repeat]: ../Geb/Prototypes/Computability/Oitavem/Machine/Repeat.lean
[constructors]: ../Geb/Prototypes/Computability/Oitavem/Machine/Compose.lean
[output-maps]: ../Geb/Prototypes/Computability/Oitavem/Machine/MapOutput.lean
[initial-machines]: ../Geb/Prototypes/Computability/Oitavem/Machine/Initial.lean
[index-arithmetic]: ../Geb/Prototypes/Computability/Oitavem/Machine/Counter.lean
[segments]: ../Geb/Prototypes/Computability/Oitavem/Machine/Segment.lean
[subtraction]: ../Geb/Prototypes/Computability/Oitavem/Subtraction.lean
[subtraction-machine]: ../Geb/Prototypes/Computability/Oitavem/Machine/Subtraction.lean
[addition]: ../Geb/Prototypes/Computability/Oitavem/Addition.lean
[capture]: ../Geb/Prototypes/Computability/Oitavem/Machine/Capture.lean
[machine-recursion]: ../Geb/Prototypes/Computability/Oitavem/Machine/Recursion.lean
[recursive-length]: ../Geb/Prototypes/Computability/Oitavem/Machine/RecursiveLength.lean
[realizer]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer.lean
[realizer-readers]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Reader.lean
[realizer-initials]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Initial.lean
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
[realizer-compile]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Compile.lean
[realizer-loop]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Loop.lean
[realizer-retained]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Retained.lean
[realizer-recursion]: ../Geb/Prototypes/Computability/Oitavem/Machine/Realizer/Recursion.lean
