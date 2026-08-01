# Handoff: the retraction for the rose spelling

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Lifespan](#lifespan)
- [The task](#the-task)
- [Where the work stands](#where-the-work-stands)
- [Decisions already taken](#decisions-already-taken)
- [Facts established by experiment](#facts-established-by-experiment)
- [Design guidance for the task](#design-guidance-for-the-task)
- [Corollaries that should fall out](#corollaries-that-should-fall-out)
- [Recorded but not scheduled](#recorded-but-not-scheduled)
- [Working discipline](#working-discipline)
- [Environment notes](#environment-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Lifespan

This file is a transient process artifact in the sense of
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape and
[docs/process.md](../../process.md) § Specs and plans are transient. It
records how the current state was reached and what to do next, not what
the code is. It is deleted in the final commits of the branch, before
the branch is pushed. The same applies to any successor handoff.

It supersedes `concrete-syntax-port-handoff.md`, whose findings are all
discharged.

## The task

`Geb.Rose.print` is a printer without a parser, so `Geb.Retraction` is
not instantiated at it and the rose spelling is not yet a syntax. Write
the parser and prove the retraction. Then take whatever corollaries fall
out quickly; see [Corollaries](#corollaries-that-should-fall-out).

Nothing else on this branch is outstanding. Do not start other
workstreams here.

## Where the work stands

Twenty-three commits on `ws2@`, none pushed. `scripts/pre-push.sh` is
clean, which is the gate.

Two Lean modules and their tests:

| Module | Content |
| --- | --- |
| `Geb/Internal/ConcreteSyntax.lean` | `Ast`, `Tree`, `Rose` as W-types; the `Retraction`/`format` law skeleton; `Csexp`, the [RFC9804] canonical S-expression syntax on the bare tree |
| `Geb/Internal/CanonicalSExpr.lean` | `CSexp`, the non-dependent form of [FormalSExpr]'s family, with `CSexp.render` its index; `Ast.toCSexp` and `Rose.toCSexp` |

`Geb/Internal/ConcreteSyntax.lean` is 50 theorems, 26 of them in
`Csexp`; axioms 11 none, 8 `propext`, 7 `Quot.sound`, 24 both.
`Geb/Internal/CanonicalSExpr.lean` is 7 theorems; 2 none, 3 `propext`,
2 both. No declaration in either depends on `Classical.choice`.

What is proved:

- `Csexp.parse_print` — the retraction law for the implemented syntax,
  with `Csexp.format_idem` and `Csexp.print_injective` instantiating the
  generic corollaries at it.
- `Csexp.print_eq_render_toCSexp` — the printer's output is the
  rendering of a `CSexp`, hence a canonical S-expression by
  construction. This is the conformance statement `parse_print` does not
  make.
- `Ast.ofRose_toRose`, `Ast.toRose_ofRose` — the rose bijection.
- `Tree`'s two functor laws, three comonad laws and two naturality
  squares.

`docs/concrete-syntaxes.md` is the design document; `docs/index.md` and
`TODO.md` carry the persistent entries. All three agree on the counts
and the axiom partition — if you change the theorem set, re-measure and
update all three.

## Decisions already taken

Do not reopen these; each was put to the user and answered.

1. **W-types throughout.** Every tree type is a `WType` and every
   recursion runs through `WType.elim`, `WType.para`, `WType.rec`,
   `Nat.rec` or `List.rec`.
   [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion
   and induction through recursors binds this: no self-referential
   `inductive`, no self-calling `def`, no `induction` tactic. The
   parser's fuel is a `Nat.rec` application, not an equation-compiler
   recursion.
2. **The hashing layer is deleted**, to be restored at roadmap stage 3
   when there is a hash to run. Its specification stays in
   `docs/concrete-syntaxes.md`.
3. **The occurrence-path vocabulary is deleted** — `Dir`, `Path`,
   `rosePathToBin` and its lemmas — because deleting `Ast.subtreeAt`
   left nothing to interpret a path against. `TODO.md` records what
   reinstating it takes.
4. **The rose orientation is curried application.** A rose node is a
   function applied to its arguments; a fork `(l, r)` is `l` applied to
   `r`; application is left-associative, so `l` carries the label and
   every argument but the last, and the children are consumed as a
   **snoclist**. `Ast.ofRose` folds by `Fin.foldl` into the left spine.
   A `#guard` in the test module pins the orientation, because both
   round trips hold under either choice.

## Facts established by experiment

Each was measured. Do not re-derive them, and do not accept a reviewer's
contrary assertion without re-measuring.

1. **An arity family used as a W-type index must be a plain `def`, not
   an `abbrev`, unless a proof needs it reducible.** Instance search
   matches at reducible transparency, so a reducible family lets it whnf
   past `Ast.Arity .fork` to `Fin 2` and select mathlib's
   `Classical.choice`-dependent `FinEnum` instead of the named
   choice-free one. `Ast.Arity` and `Tree.Arity` are `def`s for that
   reason. `Rose.Arity` cannot be — `Ast.ofRose_cons` and
   `Ast.toRose_ofRose` fail without reducibility — so the hole survives
   there and its docstring says so.
2. **mathlib's `FinEnum.fin` and `FinEnum.empty` depend on
   `Classical.choice`**, both being `FinEnum.ofList` applications.
   `Geb.finEnumFin` and `Geb.finEnumEmpty` are the choice-free
   replacements; every arity instance is built from them.
3. **Every `String` decomposition in core depends on
   `Classical.choice`** — `String.toList`, `String.data`,
   `String.length`, `String.foldr`. Only `String.ofList` and
   `String.utf8ByteSize` are clean. This is why test inputs are built as
   `List Char`. A `chars! "leaf"` macro was tried; its *output* is
   clean, but the macro rule's own body calls `String.toList` and the
   axiom linter flags that declaration. Left unresolved by the user's
   choice.
4. **Core's decimal layer cannot be reused.** `Nat.toDigits` agrees with
   `Csexp.decOf` pointwise on base 10 and core does supply a decoder,
   `Nat.ofDigitChars`, with the round trip
   `Nat.ofDigitChars_ten_toDigits`. But that theorem depends on
   `Classical.choice`, as does every core lemma descending from
   `toDigits b n` to `toDigits b (n / b)`, so the round trip can be
   neither imported nor reproved.
5. **`by decide` discharges every `#guard` in the test modules.**
   `#guard` is used because it exercises the compiled evaluator, which
   is the path a parser is used through — not because the kernel cannot.

## Design guidance for the task

The rose spelling is `Rose.print r = CSexp.render r.toCSexp`, which
spells a node as `(` label `)` with its children between: for the
five-node sample tree, `(1:0(1:1(1:2)))`.

The parser is harder than `Csexp.parseAst` in exactly one respect, and
it is worth knowing before starting. `Csexp.parseAst` reads *exactly
two* children at a fork; this one reads until the closing parenthesis.
So:

- The child loop needs its own bounded recursion, as a `Nat.rec`
  application taking the child parser as a parameter — the shape
  `Csexp.parseStep` already uses to avoid a `mutual` block. The
  remaining input length is a sufficient bound.
- The loop naturally returns a `List (Rose k)`, but a `Rose` node needs
  a `Fin n → Rose k`. Rebuilding the node from the list is a transport
  along `List.length_ofFn`, which the fixed-arity case never meets. This
  is the expensive step. Consider factoring it as a named lemma
  (`Rose.ofList i (List.ofFn f) = Rose.node i f`) proved once, rather
  than inline.
- Consider parsing to `CSexp` first and decoding `CSexp → Option (Rose k)`
  second. That splits the retraction into a general
  `parseCSexp (render c) = some c` and a decoder round trip, and the
  first half is reusable by any later csexp-shaped syntax. Whether it is
  cheaper overall is unmeasured — measure before committing to it.

`Fin.foldr`, `Fin.foldl`, `Fin.snoc`, `Fin.snoc_init_self` and
`Fin.foldl_succ_last` are all choice-free and already in use.

## Corollaries that should fall out

Once `Retraction (Rose.parse k) (Rose.print (k := k))` is proved:

- `Geb.format_idem` and `Geb.print_injective` instantiate at it, exactly
  as `Csexp.format_idem`/`Csexp.print_injective` do.
- Injectivity of `Rose.toCSexp` follows from `print_injective` plus
  injectivity of `CSexp.render`, if the latter is wanted; it is not
  currently stated. Do not prove injectivity separately first — it would
  be discarded.
- A syntax on `Ast` follows by composing with the rose bijection:
  `Ast.printViaRose` already exists, and its parser is
  `Ast.ofRose ∘ Rose.parse`. The retraction transports along
  `Ast.ofRose_toRose`.
- `docs/concrete-syntaxes.md` § The canonical grammar as a data type
  says the spelling "is not yet a syntax"; that paragraph and the
  `TODO.md` entry both need restating once it is.

## Recorded but not scheduled

- **The JSON core profile** is roadmap stage 1b and is the syntax that
  would actually test data-model independence. The rose spelling would
  not: it is still canonical S-expressions.
- **Temper** was considered as a second syntax and rejected — it defines
  no wire format. It is retained as a possible route for deploying an
  unverified implementation to several languages at once. See
  `docs/concrete-syntaxes.md` § Temper.
- **`finEnumFin`/`finEnumEmpty` belong in `Geb/Mathlib/Data/FinEnum.lean`**
  and duplicate fixtures in
  `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean`. That is a
  separate concern per § Concern shape and wants its own branch.
- **The occurrence vocabulary** and the **prose-conformance pass over
  the survey**, both in `TODO.md`.

## Working discipline

Eight rounds of fresh-context adversarial review ran on this branch, per
[AGENTS.md](../../../AGENTS.md) § Adversarial review. They converged on
the mathematics by round four; what kept failing was *explanatory
prose*. Five rounds running, a docstring's stated reason for a design
choice was false, and the replacement was false in a new way — each time
because a plausible-sounding reason was written instead of a measured
one.

The rule that follows: **before writing any "because" clause, run the
thing that would falsify it.** `#print axioms`, a mutated copy of the
definition, a `#eval` of both sides. This applies to a reviewer's
findings too — verify before acting, per § Verify agent claims. One
correction on this branch was applied on a reviewer's word and had to be
reverted a round later.

Run further adversarial rounds when the task is done, until no blocker
and no serious finding remains.

## Environment notes

- Use `jj`, never a mutating `git` subcommand; a hook blocks them.
- `scripts/pre-push.sh` is the gate. `lake build` passing is not
  sufficient: `lake lint`, `lake lint -- GebTests` and `lake shake` all
  run only there.
- **`curl` crashes this machine.** It took WSL down twice. Use the
  harness's fetch tool instead, which has been reliable.
- A test module containing only `#guard`s leaves no olean reference to
  its imports, so `lake shake` reports them removable;
  `-- shake: keep` on the import line is the sanctioned suppression, and
  a `#guard` over another module's declarations additionally needs a
  `public meta import` of it.
- `#` commands are banned in the `Geb` library and available in
  `GebTests`.
- `lake env lean <path>` from the repository root is fine for
  `#print axioms` measurements on a scratch file.
