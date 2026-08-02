# Handoff: the presheaf p.r.a. code system after the five-rule redesign

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The task](#the-task)
- [State of the branch](#state-of-the-branch)
- [What the redesign established](#what-the-redesign-established)
- [What remains open](#what-remains-open)
- [Proof-engineering hazards met in the redesign](#proof-engineering-hazards-met-in-the-redesign)
- [Process notes](#process-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

A transient planning document, removed with the spec and the plan.

## The task

Continue the workstream on morphisms of presheaf parametric-right-adjoint
functors and the codes denoting them.
`docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md` is the
design record; `Geb/Internal/PresheafIRProto/` is the prototype it transcribes.
Where the two disagree the prototype is right, since it compiles and is
axiom-audited.

`docs/superpowers/specs/2026-07-30-presheaf-pra-handoff.md` is the previous
handoff. Its task, writing the spec, is complete; it survives only for its
verified-literature and repository-hazard sections and is removed with this
document.

## State of the branch

The branch is `feat/presheaf-pra-ir-codes`, on `main`. The bookmark is several
commits behind the working copy: it points at the `ι` commit, and the redesign
that followed is not under it. Advancing it is the user's call.

`lake build`, `lake lint`, `lake test` and `scripts/lint-imports.sh` all pass
at the tip. Every prototype declaration is `Classical.choice`-free except the
six in `Functor.lean`, which is on `GebMeta.classicalAllowedModules`.

The spec converged through ten adversarial rounds against a three-rule code
system. The redesign below happened *after* that convergence, so the spec's
current state has not been adversarially reviewed. Re-running the rounds is the
first thing to do, and the reorganisation § The rules as a generalization of
small induction recursion defers — leading with the codes and their
interpretation rather than with the setting — is now unblocked and should
happen in the same pass.

## What the redesign established

The design is now presented as a rule-by-rule generalization of *small*
induction recursion rather than of Section 6's `IIR`, under one principle:
replace equality by a morphism. Over a discrete base `Hom(x, y)` is `x = y`, so
each rule collapses to its small-`IR` counterpart.

Three rules became five, and each split has a distinct reason.

- **`ι` splits into `ι` and the unit.** Small `IR`'s `ι` does two jobs a
  discrete base conflates: it is the pointed generator, and it is the terminal
  foot a `σ` chain needs to build an arbitrary shape set. Over a category
  `y j₀` and the terminal presheaf are different functors. `elSliceEquiv` is
  what exhibits the difference: `el(S) → 𝔹` is a discrete fibration, so the
  slice of `el(S)` over an element collapses to the slice of `𝔹` over its
  output object, and `σ` over `ι` therefore contributes no shapes at all.
- **`δ` splits into a non-recursive and a fused rule.** The fused rule sums
  over the decodings and so adds them to the shapes, which is what
  induction-recursion wants and what the p.r.a. formula does not. Their
  arities are over *different categories*: the fused rule's over the raw input
  base whose decodings it sums, the non-recursive rule's over the
  interpretation's own input base. `CodeShape` therefore depends on `D`.
- **`σ` is unchanged.** The collapse above indicts the chain's foot, not `σ`.

`praWitnessCode` is the chain `σ` at an arbitrary shape presheaf over the
non-recursive `δ` at an arbitrary arity over the unit;
`interp_praWitnessCode` is definitional, and
`praWitnessLiftShapeVal_naturality` and `praWitnessLiftDirEquiv_restr` identify
its shape presheaf and its arity with the target's, as presheaves rather than
objectwise. All five computation rules are `rfl`.

## What remains open

The spec's § Open questions is the authority; these are the two that carry
work rather than curiosity.

- **Obligation 8, uniqueness.** The witness's *data* is settled. What is open
  is whether the witness is the only code for a given functor, and what the
  interpretation's fibres over a functor look like. This is open question 7.
- **Obligations 6 and 7, the bound.** The three generator and four operation
  cases are proved, but the code type they run over is a different one from the
  prototype's — the fragment's `δ` carries a `PshMor`-indexed subcode family —
  and building it, running the induction, and supplying composition on `PshHom`
  and the iso-transport are all outstanding.

## Proof-engineering hazards met in the redesign

Three obstructions blocked `praWitnessLiftShapeVal_naturality`, and each
recurs wherever a shape presheaf is presented as a subtype of a `ULift`ed
sigma. None is mathematical.

- **A dependent match on the membership proof blocks the functor laws.**
  Writing an identification as `match x with | ⟨⟨⟨_, t⟩⟩, rfl⟩ => t` stops
  `simp` reaching the `g ≫ eqToHom h` that shape restriction produces. An
  explicit `cast (congrArg (fun k ↦ T.obj ⟨k⟩) x.2) …` does not, and is the
  form `iotaConstData.shapeRestr` already uses.
- **An `Equiv` coercion around the transport blocks reduction.** With the
  `cast` in place the goal is still `DFunLike.coe {toFun := …} x`, and the
  structure literal never beta-reduces. The transport has to be named and the
  lemma stated about the name; `elEqToHom` exists for the same reason.
- **`subst` on the membership proof substitutes the unreduced projection.**
  `obtain ⟨…, rfl⟩` eliminates `x.1.down.1 = j` by replacing `j` with the left
  side, so a morphism's codomain becomes `q {down := ⟨jj, t⟩}` and
  `Category.comp_id` cannot match `g ≫ 𝟙 jj` against `g ≫ 𝟙 (codomain g)`.
  Ascribing the equation's type first — `have hj' : jj = j := hj` — makes
  `subst` go the other way.

Whether mathlib's `CategoryOfElements` API dissolves all three is worth
checking when obligation 4's `ElObj` versus `S.Elementsᵒᵖ` decision is taken;
it would shift the balance of that decision.

Two further hazards, both confirmed by the axiom linter rather than by
reading:

- **Treat `Equiv`'s combinators as choice-suspect by default.**
  `Equiv.sigmaAssoc` and `Equiv.sigmaFiberEquiv` are `Classical.choice`-
  dependent, as `Equiv.arrowCongr` and `Equiv.piCongrLeft` already are per
  `docs/rules/lean-coding.md`. Hand-rolling was cheaper than auditing.
- **Stating a lemma about `interp` of a code forces the W-type fold** and
  times out in `whnf`. State it about the semantic operation and let the
  definitional computation rule carry it across.

## Process notes

Every claim recorded in the spec is to be verified against its source before
it is written, not after. Two defects in this session came from not doing
that: the nLab polynomial characterization was recorded from memory and had
both halves wrong (it is the *last* leg that is a discrete fibration, and the
first two form a *two-sided* one), and a batch of spec edits was reported as
applied when the string matching had silently failed. Whitespace-insensitive
matching with a hard assertion per edit, and a grep after each batch, catch
the second class.

The prototype is treated as part of the specification. Two conclusions in this
session were reached by argument and then overturned by building the Lean —
that the fused `δ` needed a new operation, and that `σ` needed a Grothendieck
form. Both times the construction was cheaper than the argument and settled it
outright.
