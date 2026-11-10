/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Geb

/-! # The first Geb authoring milestone

A documented program, its statement and proof script, their durable encodings, and the record
from which the program and its checked certificate can be reproduced.
-/

open Verso.Genre Manual
open GebManual.Geb

#doc (Manual) "Writing a first Geb development" =>
%%%
tag := "first-authoring"
%%%

The development under `examples/authoring/` is a small program written
and proved in Geb. Its manifest chooses edition `0` and the source,
annotation and prose profiles. The statements and proof scripts live in
`Pair.proofs.geb`; the computational definitions live in `Pair.geb` and
`Lists.geb`.
The commands below compile the program, check the examples in its notes,
produce a certificate and replay it. This chapter includes the files
directly, checks their prose and references, and replays their certificate
while it builds.

# The development

{gebProgram "examples/authoring/pair.manifest" "Pair.proofs.geb" "record/pair.cert"}

The first theorem equates two closed functions, including their
abstractions; the second states the same equality at every pair of
arguments, and the example in the note separately checks one evaluation.
The others use a hypothesis, induction on a list, and an earlier theorem.
There is no Lean source belonging to this development.

# Running it

From the repository root:

```
lake build geb-author geb-defs
lake exe geb-author compile examples/authoring/pair.manifest /tmp/pair.img
lake exe geb-defs /tmp/pair.img /tmp/pair.defs
lake exe geb-author prove examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.cert
lake exe geb-author replay examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.cert
```

`compile` checks every example before writing the image. An example's two
expressions use fully qualified definition names and must return trees;
it evaluates both and compares their results. `prove` runs the script in
the prover written in Geb, checks the
result with the checker written in Geb, and replays it before writing the
certificate. A rejected input leaves an existing output in place. A program
the compiler rejects is reported at the line and column of the declaration
concerned, and a theorem whose statement or script does not read, or whose
script does not prove it, at the theorem's name, as
`FILE:LINE:COLUMN: error: MESSAGE`.

`replay` checks the saved derivations against the source statements and
their names. It performs no proof search. Reducing `normalize`'s budget
to zero can make `prove` fail while `replay` continues to accept the saved
certificate. Changing the statement, its name, the program, or its
profile prevents that reuse. Comments and notes may change while the
compiled program stays the same; examples are checked again on replay.

# The proof-source profile

A proof document is `(proofs V THEOREM…)`, its version `V` being `0`, `1` or
`2`, with one or more theorems of distinct names, each
`(theorem NAME STATEMENT (by SCRIPT))`. Version `1` reads:

```
STATEMENT ::= (forall ((x A) …) PROPOSITION) | PROPOSITION
PROPOSITION ::= (implies (h EQUATION) … EQUATION) | EQUATION
EQUATION ::= (equal TERM TERM)
SCRIPT ::= (normalize FUEL RULE…) | (reduce DEPTH RULE…)
         | (auto DEPTH SPLITS RULE…) | (extensionality x SCRIPT)
         | (induction x (y ys ih) SCRIPT SCRIPT)
         | (cases x (y ys) SCRIPT SCRIPT)
         | (reduce-hypotheses DEPTH (h …) SCRIPT)
DEPTH ::= head | weak | open | full
```

A type `A` is a type of the kernel: `T`, `Unit`, `(Prod A B)`,
`(Arrow A B)` or `(List A)`. A term is a term of the kernel, read by the Geb
reader in the scope of the bound variables, innermost last, with the
program's definitions under their qualified names; its translation into the
metalogic is that of the program's definitions. The two sides of an
equation have one type. The bound variables and the hypotheses are named
by atoms that are neither numerals nor reserved, distinct from one another,
from the program's definitions and from the theorems.

A script proves the equation of its goal in the goal's context and under
its hypotheses. `normalize` normalizes both sides within a budget,
unfolding definitions and computing applications of abstractions, the
components of pairs, the folds of lists and trees at their constructions,
the case analysis of a coproduct at its injections and the element of the
terminal type. `reduce` reduces both sides to a depth, the weak
head normal form, the weak normal form, the normal form but for the starts
and steps of folds, or the normal form, and `auto` reduces to a depth and
splits a list or coproduct variable on which the reduction is stuck, up to a number of
times, using the instances of the hypotheses. A rule names a hypothesis or
an earlier theorem, which each of these then rewrites by. `extensionality`
proves an equation of functions by that of their applications to a new
variable `x`. `induction` proves an equation by induction on its innermost
variable, of a list type: at the empty list, and at the list of a head `y`
and a tail `ys`, under the induction hypothesis `ih`. `cases` proves it by
the case analysis of any list variable, the variable kept in the context
and its cases named. `reduce-hypotheses` reduces the named hypotheses to a
depth, so that a rule rewrites by their reduced forms. The tactics
introduce no names but those a script writes, so a script names every
variable and hypothesis it refers to. These are the tactics of
`bootstrap/free-topos/tactics.geb` and `bootstrap/free-topos/prove.geb`,
`Geb.FreeTopos.Tactics` in Lean.

The reductions rewrite a term once its head is reduced, so a theorem's
left side as written rarely occurs in a reduced goal. In version `1` each
theorem is therefore followed in the certificate by its companion: the
theorem with its sides in weak normal form, derived from it at its own
variables and hypotheses, and a rule naming the theorem rewrites by its
companion.

Version `0` admits only theorems `(theorem NAME (equal LEFT RIGHT)
(by (normalize FUEL)))` whose sides are the names of definitions. It reads
their statements as version `1` does, and its normalization unfolds
definitions and computes applications of abstractions and the components
of pairs alone, so a document of either version keeps its meaning. It
cites no theorem, so its certificate saves no companion and has the format
`geb-proof/v1`, whose certificates therefore still replay; version `1`
writes `geb-proof/v2`, and version `2` `geb-proof/v3`. An unknown or unbound
name, a name declared twice,
a malformed form, an unsupported version, a false equation or an
unsuccessful search is rejected. Failure of a bounded search does not establish that the
statement is false.

Statements are not yet written over the datatypes of the datatype language.
The statement reader and the script interpreter are in
`bootstrap/authoring.geb`; they add no rule to the metalogic.

# Statements over the internal language
%%%
tag := "internal-statements"
%%%

Version `2` reads what version `1` reads, and adds the program a document
names and the documents it cites, statements over the metalogic's internal
language in object variables, rules at objects, and the tactics of trees
and coproducts:

```
DOCUMENT ::= (proofs 2 HEADER… THEOREM…)
HEADER ::= (program NAME) | (import PATH)
STATEMENT ::= … | (internal (X…) QUANTIFIED)
QUANTIFIED ::= (forall ((x TYPE) …) PROPOSITION) | PROPOSITION
TYPE ::= T | Unit | (Prod TYPE TYPE) | (Arrow TYPE TYPE) | (List TYPE)
       | Bit | Bits | Omega | (Sum TYPE TYPE) | (Rose TYPE) | X
ITERM ::= x | NAME | unit | (pair ITERM ITERM) | (fst ITERM) | (snd ITERM)
        | (lam ((x TYPE) …) ITERM) | (ITERM ITERM…) | (equal ITERM ITERM)
        | (nil TYPE) | (cons TYPE ITERM ITERM) | (node TYPE ITERM)
        | (inl TYPE TYPE ITERM) | (inr TYPE TYPE ITERM)
        | (case TYPE TYPE TYPE ITERM)
        | (list-rec ITERM (y r) ITERM ITERM)
        | (rose-rec TYPE (n) ITERM ITERM)
        | (lib NAME TYPE… ITERM…) | (kernel TERM)
RULE ::= … | (NAME TYPE…)
SCRIPT ::= … | (fold-induction x (y r) ITERM FUEL RULE…)
         | (tree-fold-induction x (l rs) ITERM FUEL RULE…)
         | (sum-cases x (y) SCRIPT SCRIPT)
         | (tree-cases x (l cs) NAME SCRIPT)
         | (auto-trees DEPTH SPLITS NAME RULE…)
         | (generalize (y TYPE) ITERM SCRIPT)
         | (pointwise NAME DEPTH RULE…)
         | (mask-rewrite TYPE TYPE NAME LEMMA (ITERM…)
             ITERM ITERM ITERM ITERM ITERM ITERM)
LEMMA ::= NAME | (NAME TYPE…)
```

A statement `(internal (X…) Q)` binds the object variables `X…`, and `Q` has
the form of a statement of version `1` with the types and terms of the
internal language, an equation's sides `ITERM`s of one type. A type is the
translation of a kernel type, `T` the rose trees over the bitstrings and
`Unit`, `Prod`, `Arrow` and `List` the terminal object, products,
exponentials and list objects; the bits, `Bit`, which is `(Sum Unit Unit)`;
the bitstrings, `Bits`, which is `(List Bit)`; the truth values, `Omega`; a
coproduct; the rose trees over a type of labels, `T` being `(Rose Bits)`; or
an object variable.

A term of the internal language is a variable; a definition of the program by
its qualified name, at its translated type; the element `unit` of the
terminal type; a pair or a component; an abstraction; an application, the
function before its arguments; an equation, of the type `Omega`; or one of
the forms below. Each form carries the types that the internal language does
not infer.

* `(nil A)` is the empty list of `A`, and `(cons A h t)` the list of a head
  before a list.
* `(node A p)` is the tree of the pair `p` of a label of `A` and a list of
  trees.
* `(inl A B t)` and `(inr A B t)` are the injections into `(Sum A B)`, and
  `(case A B C p)` the function from `(Sum A B)` to `C` of the pair `p` of a
  function from `A` and one from `B`.
* `(list-rec z (y r) s l)` is the fold of the list `l`: `z` at the empty
  list, and at a head `y` before a list the term `s`, in which `r` is the
  fold's value at that list.
* `(rose-rec C (n) s t)` is the fold of the tree `t` into `C`: at a node the
  term `s`, in which `n` is the pair of the node's label and the list of the
  fold's values at its children.
* `(lib NAME A… t…)` applies a definition of the translation's library, with
  an object for each of its object parameters before its arguments. The
  names are `bnil`, `b0`, `b1`, `lab`, `unnode`, `children`, `cond`, `tail`,
  `headD`, `lcase`, `isNil`, `succ`, `length`, `pred`, `dbl`, `add`, `cmp`,
  `ltB`, `eqB`, `subE`, `sub`, `mul`, `divMod`, `log2`, `iter`, `mapApp`,
  `and`, `allZip` and `equal`, those of `Geb.FreeTopos.Translation.D`.
* `(kernel t)` is a term of the kernel, read and translated as version `1`
  reads a statement's terms, in the variables whose types are kernel types.

The names `inl`, `inr`, `case`, `list-rec`, `rose-rec`, `lib` and `kernel`
head these forms wherever a term of the internal language is read, and no
variable of an internal statement or of a script of version `2` takes one.
The terms a script writes are terms of the internal language. A statement of
either kind is rejected unless its sides have one type in its context.

A rule `(NAME A…)` rewrites by an earlier theorem in object variables at the
objects `A…`. The tactics added:

* `fold-induction` proves the goal by induction on its innermost variable
  `x`, a list, in the form of the uniqueness of a fold: the sides are equal
  at the empty list, and each side at a head `y` before a list is the step,
  in which `r` is that side's value at the list, each of the three by
  normalization within the budget.
* `tree-fold-induction` proves a goal whose one variable `x` is a tree by the
  uniqueness of the tree's fold: each side at the node of a label `l` is the
  step, in which `rs` is the list of that side's values at the children,
  each by normalization within the budget.
* `sum-cases` proves the goal at each injection of a new variable `y` for a
  variable of a coproduct, a bit among them, and `tree-cases` at the node of
  a new label `l` and children `cs` for a variable of the trees; `NAME` is
  the theorem that a tree is the node of its unfolding.
* `auto-trees` reduces to a depth and splits the list, coproduct or tree
  variable the reduction is stuck on, as `auto` does for lists and
  coproducts, with that theorem.
* `generalize` proves the goal with a new variable `y` for the occurrences of
  a term.
* `pointwise` proves an equation from the earlier theorem `NAME` that equates
  two functions: the goal's sides and the applications of the theorem's
  sides to the goal's innermost variable have the same normal forms at the
  depth.
* `mask-rewrite A B ABSORB LEMMA (t…) c d x x' z y` proves that the
  conditional on the test `c` between `y` and `d`, of the type `A`, is the
  conditional between `y` with `x'` for the occurrences of `x`, of the type
  `B`, and `d`. `LEMMA`, at its objects and at the terms `t…` for its
  variables, equates the conditionals on `c` between `x` and `z` and between
  `x'` and `z`, and `ABSORB` is the theorem that inside the branch a test
  selects, a conditional on the same test is its first branch.

The tactics that cite a theorem by `NAME`, and a `LEMMA`, cite it as stated,
where a rule rewrites by its companion. `fold-induction` is
`Geb.FreeTopos.Internal.byListInd` and `tree-fold-induction`
`Geb.FreeTopos.Internal.byRoseInd`; the others but `pointwise` are tactics of
`Geb.FreeTopos.Tactics`, and `pointwise` composes the derivation of the Lean
developments' pointwise lemmas in `bootstrap/authoring.geb`.

A form `(import PATH)` names a proof document whose theorems the document
cites, by a path as a manifest's source is, relative to the document's own
directory. A development is the documents a document imports, and those they
import, each read once and before the documents importing it, followed by
the document; an imported document is of version `1` or `2`. The theorems of
a development are one list: their names are distinct, a theorem cites those
before it, and the certificate holds the declarations of the imported
theorems before the document's own, so that it replays from the documents
alone and a change to an imported statement prevents its reuse.

A form `(program NAME)` names the program a document is proved against
where the command gives no manifest: the manifest whose program has that
name in the document's directory, or else in the nearest directory above
it that holds one, a directory holding several being rejected. A document
names no more than one program, and a manifest the command gives takes the
place of the program named. Only the document proved is consulted: the
documents it imports are read against its program, whatever they name, so
that a document that holds in every program names none, and a development
is proved again in a larger program by a document that imports it.

```
lake exe geb-author prove PROOFS CERTIFICATE
lake exe geb-author replay PROOFS CERTIFICATE
lake exe geb-author check FILE
```

`check` writes nothing. It proves a proof document, a file holding a form
`(proofs V …)`, against the program it names, and compiles any other file
as a source of a program, with the sources that the nearest manifest
listing it lists before it; an editor runs it on the file being edited.

The documents under `bootstrap/proofs/` state and prove in this profile the
development of `GebTests/Prototypes/FreeTopos/TreeCases.lean`, whose
statements are Lean values and whose scripts are Lean code, about the program
of `bootstrap/expansion.manifest`: `trees.proofs.geb` the lemmas on the
unfolding of trees, which hold in every program and name none, and
`tree-cases.proofs.geb`, which names the program `expansion` and imports
it, the conditional lemmas, the
soundness of the equality of bitstrings, the rewriting under a test, and that
a tree the reader names by the atom of the head of a definition's form is
that atom. Each theorem is stated as it is written and followed by its
companion, where the Lean development states a lemma's sides in the normal
form it computes.

```
lake exe geb-author prove bootstrap/proofs/tree-cases.proofs.geb \
  /tmp/tree-cases.cert
lake exe geb-author replay bootstrap/proofs/tree-cases.proofs.geb \
  /tmp/tree-cases.cert
```

No tactic of scripts yet performs induction on trees with the hypothesis at
each child, by which the Lean developments prove weakening and substitution.

# Keeping the source

The authoring spelling and the canonical, advanced and basic transport
encodings hold the same source document, including comments, names,
notes, examples and unknown optional fields. For example:

```
lake exe geb-author convert canonical examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.proofs.csexp
lake exe geb-author convert advanced examples/authoring/pair.manifest \
  /tmp/pair.proofs.csexp /tmp/pair.proofs.advanced
lake exe geb-author convert authoring examples/authoring/pair.manifest \
  /tmp/pair.proofs.advanced /tmp/pair.proofs.geb
```

The same commands work on the program source. `compile`, `prove` and
`replay` accept every spelling. The `convert` output choices are
`canonical`, `advanced` and `authoring`; the reader also accepts canonical
bytes encoded in base-64 between braces. An authoring document gets its
profile from the manifest; a strict document carries it explicitly and
must agree with the manifest. Unsupported mandatory profile features are
rejected. The existing document retraction laws apply to these documents;
conversion does not promise to keep a particular whitespace layout.

The record in `examples/authoring/record/` contains the checked program
image, its elaborated definitions, the certificate, the compiler image, canonical copies of
the program's and the proofs' source documents, and the SHA-256 digests of the inputs. The digests
pin the compiler image and emitted compiler, the authoring runner and its
source dependencies, the manifest and sources, the Lean toolchain and
dependency lockfile. `record/compiler.img` retains the exact bytes of
`bootstrap/compiler.img` used at the milestone. The certificate envelope separately identifies
its format (`geb-proof/v2` for version `1`, `geb-proof/v3` for version `2`), theory
(`free-topos/base/v1`),
document profile and exact compiled program; its declarations retain the
statements, their companions and their source names.

```
scripts/authoring.sh check
scripts/tests/test-authoring.sh
```

The first command regenerates and compares the record. Use
`scripts/authoring.sh regen` when intentionally updating it, then review
the sources and record together. `scripts/authoring.sh runtime` regenerates
only the emitted proof runner when its Geb source changes. The second
command tests conversion, metadata preservation, compilation, replay and
rejection through the command-line interface.

Edition `0` is still a pre-release edition. Keep the whole record with
work written against it. No migration to a future edition is implemented
here; its durable document, elaborated definitions and exact compiler
give that migration explicit inputs. Suspended holes in proofs, statements
over datatypes, induction on trees with the hypothesis at each child, and
completion of datatype soundness remain separate work.

# Preserving a development

The preservation workflow applies the same compilation, example checking,
document conversion and certificate replay to any program manifest and
proof document accepted by the current authoring commands. For the
development under `examples/roundtrip/`, whose manifest orders a library
and its application in separate layers:

```
python3 scripts/preserve.py record examples/roundtrip/roundtrip.manifest \
  examples/roundtrip/Roundtrip.proofs.geb /tmp/roundtrip-record
python3 scripts/preserve.py verify /tmp/roundtrip-record
python3 scripts/preserve.py check /tmp/roundtrip-record
python3 scripts/preserve.py compare /tmp/roundtrip-record \
  examples/roundtrip/roundtrip.manifest examples/roundtrip/Roundtrip.proofs.geb
```

`record`, `check` and `compare` build the host executables first. Pass
`--no-build` before the subcommand to use the executables already built
in this checkout.

`record` first copies the manifest, every source in its order, and the
proof document with the documents it imports, retaining their original
bytes and relative paths.
It compiles those copies, checks the examples, produces and replays a
certificate, and writes canonical copies of the complete documents.
The record also holds the checked image, the elaborated definitions,
the exact compiler image and emitted compiler, the emitted proof runner,
the Geb source closures of the compiler and proof runner, the Lean
toolchain and dependency lockfile, and the SHA-256 identities of the
native host executables. Native executables and installed dependencies
are not copied; rebuilding a historical native host is outside this
workflow. The retained images, emitted code and source inputs are
available to a future migration.

The directory is published only after its checks succeed, by
[renaming](https://docs.python.org/3/library/os.html#os.rename) a
staged directory on the same filesystem. An existing record is never
replaced. A new record uses a new directory, so earlier inputs and results
remain available. To retain a proof that already checks, pass
`--certificate PATH` to `record`: it replays that certificate instead of
running proof search. In particular, insufficient search fuel does not
prevent recording or checking a development whose saved proof replays.

`record.json` identifies format `geb-development/v1`, the archived
manifest and proof document, the ordered source paths, and the SHA-256
digest of every other file; where the proof document imports documents the
format is `geb-development/v2`, and the record names them. `verify` checks
this inventory without Lake
or the original project. It rejects missing, modified and unlisted files,
symbolic links, paths outside the record and unsupported record formats.
These digests check integrity relative to the index; they neither
authenticate it nor establish a theorem.

`check` reads the archived sources with the current host, compares their
canonical documents, checked image and elaborated definitions with the
record, and replays its saved certificate, checking examples again.
It performs no proof search and does not regenerate the record. A moved
record therefore remains checkable after the original project is removed,
provided the current host still reads its profile and reproduces its core.

`compare` performs the same compilation and replay on the supplied
current sources. It reports document changes separately: edits to
comments, notes and script budgets may preserve the checked core and
permit replay. A different compiled program, even one equivalent by a
theorem, is rejected; comparing meanings through such a theorem requires
an explicit migration. A statement changed to another true statement is
also rejected by replay. Failure leaves the record unchanged.

The committed record under `examples/roundtrip/record/` is checked and
compared with its sources by `scripts/tests/test-preservation.sh`, which
also exercises relocation, documentation changes, reuse of a saved proof,
corrupt records and failed creation. Continuous integration runs this test.
The Pair development's earlier record remains in its original format.
No conversion between semantic editions or proof-language versions is
implemented here; those conversions have the retained source documents,
profiles, compiler inputs and checked results as their inputs.
