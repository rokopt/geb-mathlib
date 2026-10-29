# Bootstrap architecture review

Review recorded on 2026-10-29 against repository revision `848e7902`.
The review below is preserved in full, with line wrapping and link targets
adapted for this document. Source links are relative to this file; their
line numbers refer to the reviewed revision. The generated C link points
to a local build artifact. Statements about leaving the workspace unchanged
refer to the original review, before this document was saved.

My assessment is that there is a substantial architectural problem. I would
locate it in **how the mathematical specification is turned into executable
checking**, rather than conclude that the free-topos foundation or the existence
of separate certificates was a mistake.

The recurring pattern is that a compact operation becomes a large symbolic
computation: constructing categorical terms to obtain a type, constructing
derivations to obtain a reduction result, expanding shared structures through
tree traversals, and asking Lean’s definitional equality to establish
substantial program equivalences. These costs compound.

I would preserve the semantic and soundness work, while substantially changing
the operational representation and verification interfaces. Your proposal to
make equality evidence part of a typed language fits that direction, but it
addresses only part of the problem.

I reviewed the bootstrap chapter and design documents, the kernel and loading
machinery, the internal-language compiler/checker/prover, certificate storage,
agreement proofs, and the latest completed CI run. The timings below come from
the [October 28
run](https://github.com/rokopt/geb-mathlib/actions/runs/40688483627):

| Work | Observed result |
| --- | --- |
| `rfl` loading | Checker layer: 149 minutes; Translation: 74 minutes; Prover: 91 minutes. The job was cancelled at six hours, with work remaining. |
| `Certified.DatatypeList` | That module alone took 14,748 seconds—about 4 hours 6 minutes. |
| `datatype-app` generation | Cancelled at six hours. The interval between `rawListR proved` and `lamOneCase proved` was about 4 hours 43 minutes. |

The last example runs the **compiled** certificate generator. Consequently,
moving everything from Lean’s interpreter to native executables would not be
sufficient.

1. **The loading proof makes definitional equality do too much work.**

   [`declareLoading`](../Geb/Prototypes/Kernel/LoadCommand.lean#L128) gives each
   global a type expressed as `defType pre dk`.
   [`defType`](../Geb/Prototypes/Kernel/Loading.lean#L50) runs the
   checker/evaluator to obtain that type. Subsequent definitions refer to
   globals containing those computations, and the loading equations are proved
   by reflexivity.

   Naming these expressions does not make them cached computation results for
   kernel conversion. Establishing later definitional equalities can require
   unfolding computations through the preceding environment again.

   The representation aggravates this: rose trees are W-types with
   function-valued children, and their paramorphism reconstructs trees. The
   manual explicitly records that reconstructed types and literal types are not
   interchangeable by the definitional equality the casts require. This is why
   simply storing the inferred type was not an adequate fix. See [the
   representation](../Geb/Prototypes/RoseTree/Basic.lean#L68) and [the loading
   explanation](../manual/GebManual/Bootstrap.lean#L6835).

   I would replace this proof strategy with **compositional loading
   correctness**: stable type representations, a correctness lemma for each term
   constructor, and each global’s proof using already-established facts about
   earlier globals. A global’s computational type should not require replaying
   its definition’s inference whenever conversion reaches it.

   This is a redesign of the interface between syntax, typing, and denotation.
   Splitting the same reflexivity calculation into more modules can improve
   incremental builds, but does not remove the underlying work.

2. **Sharing currently saves storage much more effectively than it saves
   checking.**

   The certificate reader does something useful: it computes readings once per
   table node and preserves physical sharing. But it returns ordinary `Term` and
   `Deriv` trees. The internal-language checker then uses `RoseTree.para`,
   traversing occurrences in those trees rather than checking a table of
   already-validated judgments. See
   [`Stored.paraOfNats`](../GebTests/Prototypes/FreeTopos/Stored.lean#L271) and
   [`Internal.check`](../Geb/Prototypes/FreeTopos/Internal/Derivation.lean#L684).

   I independently counted the current certificates, and the derivation counts
   match CI:

   - Across the certificates: **871,983 stored table nodes**, representing
     **18,774,973 derivation-node occurrences**.
   - `datatype-app`: **49,652 table nodes**, representing **2,798,267
     derivation-node occurrences**.
   - CI additionally counts **89,600,130 term-node occurrences** in
     `datatype-app`’s rule arguments.

   These are structural counts, not measurements of allocations or instructions.
   Nevertheless, they explain why the small certificate files are misleading.

   Equality also traverses structure:
   [`WType.beq`](../Geb/Mathlib/Data/W/Basic.lean#L132) recursively compares
   shapes and children. Sharing a term does not, through this implementation,
   turn its equality checks into comparisons of identifiers.

   I would retain an explicit shared representation throughout checking:
   references for terms, types, contexts, and evidence; checked annotations; and
   reusable judgment results. There is a necessary qualification: a derivation’s
   meaning depends on its context, hypotheses, and input term. Memoizing solely
   by derivation-node identity would be wrong. Either judgments must include
   those dependencies explicitly, or caches must include them.

   The repository already demonstrates parts of this design in the [shared
   combinator checker](../Geb/Prototypes/FreeTopos/Check.lean#L58). However,
   that checker is not the path used by these internal-language certificates.
   Its techniques need to reach this path.

3. **Some frequently used operations compute substantial results that their
   callers discard.**

   The clearest example is:

   ```lean
   def typeIn ... :=
     (compile G n t (ctxObj Γ) (stdEnv Γ)).map Prod.snd
   ```

   A request for a term’s type compiles it into categorical combinators and
   discards the arrow.
   [`compileStep`](../Geb/Prototypes/FreeTopos/Internal/Compile.lean#L292)
   constructs compositions, pairings, currying, parameterized folds, and
   projection environments. Typing queries occur repeatedly during checking and
   reduction.

   I checked the generated C:
   it calls the full compiler and subsequently extracts the type. The compiler
   has not eliminated this work.

   A dedicated type-synthesis function, proved equal to this projection, is
   therefore a concrete optimization with a clear correctness obligation. Its
   actual contribution to the hours-long checks still needs profiling.

   The conversion checker has the same pattern. Its `norm` and `eval` cases call
   reductions returning a term **and a derivation**, then retain the term. The
   reductions construct congruence and transitivity trees along the way. See
   [`convStep`](../Geb/Prototypes/FreeTopos/Internal/Conversion.lean#L122) and
   [`eval`](../Geb/Prototypes/FreeTopos/Internal/Prove.lean#L461).

   I would make type-only inference and result-only reduction separate
   executable functions, with equivalence or soundness proved once. The proof
   can remain in Lean’s `Prop`; the executable need not manufacture a `Deriv`
   value to justify every invocation.

4. **Primitive rewriting is accounting for almost all the evidence, and the
   intended replacement is not yet in the production path.**

   Of the 18.77 million derivation-node occurrences, **18.62 million—99.19%—lie
   within rewritings**. Replacing each such rewriting subtree by one conversion
   node would leave approximately 209,000 nodes: the manual’s roughly ninetyfold
   reduction.

   That is a projection of certificate size, **not a ninetyfold speedup**. The
   current conversion checker can still spend its time reconstructing the
   derivation it discards. The newest continuation section acknowledges this,
   and also states that no prover emits the conversion steps and no stored
   certificate uses them yet. See [the
   continuation](../manual/GebManual/Bootstrap.lean#L7045).

   This is where I would change the development order. Efficient conversion
   should be exercised against the difficult datatype proofs before requiring
   completion of all the expensive developments that would benefit from it.

   The literal evaluator is evidence for the approach: the manual records a
   multiplication example taking tens of seconds through the base proof
   machinery and fractions of a millisecond through the verified literal
   evaluator. That is a workload-specific measurement, but it demonstrates that
   some enormous costs come from the chosen justification mechanism rather than
   the mathematical operation. [Recorded
   measurements](../manual/GebManual/Bootstrap.lean#L7009).

   I would combine verified conversion with preservation of sharing during
   substitution and evaluation. Merely hiding an expansive reduction inside one
   certificate instruction will improve file size without necessarily improving
   time.

There is also a distinction about what the current checks establish. The `rfl`
job does **not** remove all operational assumptions from the bootstrap argument.
Loading facts become kernel-checked theorems in that mode, but large certificate
checks still use
[`evaluation_axiom`](../GebTests/Prototypes/ProgramCommand.lean#L180), which
evaluates a Boolean and adds an axiom in either mode. This is documented, and
does not invalidate the generic soundness proofs. It means that parts of the
end-to-end argument still depend on asserted evaluations. I would make efficient
discharge of those assertions an explicit architectural objective.

On your suggestion about internalizing equality, I agree with an important part
of it.

An interface with objects, typed morphisms, and equality evidence indexed by its
endpoints can make valid construction compositional. A factorization can require
its equalizing evidence at construction; later users can reuse the resulting
checked object. That can substantially reduce bookkeeping and repeated
reconstruction of formation conditions.

The current choice was mathematically defensible. Partial Horn logic supplies a
constructive account of partial operations and their equations. But its
convenience as a semantic specification does not establish its suitability as an
executable representation. Kovács’s discussion explicitly identifies the
encoding overhead of the fibered presentation relative to indexed presentations
in mechanized mathematics.
[Palmgren–Vickers](https://sjvickers.github.io/partialalgebras.pdf), [Kovács,
§4.7](https://arxiv.org/pdf/2302.08837).

I would distinguish three changes:

| Change | What it can accomplish |
| --- | --- |
| Equality evidence is available as a typed part of the language | Better formation rules, interfaces, and reuse of established judgments |
| Routine computation is handled by verified conversion procedures | Removes explicit traces of elementary reductions |
| Terms and checked judgments retain sharing during execution | Avoids repeated traversal, construction, and validation |

The first does not automatically provide the other two. The current language
already has equality formulas, and `Deriv` already represents evidence. Moving
that evidence into a third syntactic sort would still leave the beta reductions,
substitutions, and repeated traversals unless their execution changes too.

There is also a design obligation around proof relevance. If proof choices
become part of morphism identity, changing a proof can change a term’s identity.
For the intended ordinary categorical semantics, I would make the irrelevance or
erasure of that evidence explicit. A typed authoring interface can provide this
while still translating into the existing presentation; it need not require
discarding the current model theory.

I would also keep a prover/checker separation. A typed equality proof still
needs checking, and separating search from acceptance permits changing search
strategies without expanding the trusted basis. Metamath Zero is particularly
relevant here: its separate verifier is efficient because its format controls
sharing and makes equality tests cheap. Separation itself does not force
expansive checking. [Carneiro, §3.2](https://arxiv.org/pdf/1910.10703).

What I would reconsider is the amount of work required to prove that the
**prover** reproduces another prover’s exact output. The essential acceptance
contract is that its result proves the requested statement. Your [compatibility
contract](../manual/GebManual/Bootstrap.lean#L3197) already says this and hides
certificate representation from clients. I would use that boundary to permit
algorithmic changes now, while preserving the existing agreement results for the
implementations they describe.

Similarly, certificate regeneration and certificate validation serve different
purposes. Regeneration tests the search implementation and reproducibility;
validation establishes acceptance of an existing artifact. Both are useful, but
repeatedly reproducing an expensive search should not become the mechanism by
which ordinary development obtains confidence in an unchanged certificate.

My preferred direction would be:

1. **Separate executable computations from reference definitions.** Start with
   type-only synthesis and result-only reduction, each proved to agree with the
   existing implementation. These are relatively contained changes with
   measurable effects.
2. **Connect conversion to real developments.** Extend declarations, tactics,
   and storage, then measure `datatype-app` and `datatype-list`. Measure
   construction, sharing, checking, and serialization separately—the current
   logs cannot attribute all the time after the last “proved” message.
3. **Keep shared terms and judgments shared through checking.** Reuse the
   existing store techniques, with scope-aware validation and incremental
   development states. Avoid checking common prefixes repeatedly from an empty
   environment, as the [current certificate
   interface](../GebTests/Prototypes/FreeTopos/Certified/Basic.lean#L70) does.
4. **Replace the dependent reflexivity loading strategy.** Establish correctness
   compositionally over stable type codes and previously verified globals. This
   can proceed independently of certificate-format work.
5. **Build the typed equality-evidence interface over those foundations.**
   Assess it by how much repeated formation checking and proof bookkeeping it
   removes, while preserving the existing semantics.

I would make the first deliverable a measured improvement on one of the
presently prohibitive cases, with its correctness argument intact. That would
give a much better basis for deciding how extensive the representation redesign
should be. A wholesale foundational rewrite would otherwise risk reproducing the
same execution costs inside a more attractive syntax.

I left the workspace unchanged. I did not rerun the six-hour builds; the timing
evidence is from CI, and the certificate counts were independently recomputed
locally. The proposed implementation changes still require measurements before
assigning them speedup estimates.
