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
certificate. A rejected input leaves an existing output in place.

`replay` checks the saved derivations against the source statements and
their names. It performs no proof search. Reducing `normalize`'s budget
to zero can make `prove` fail while `replay` continues to accept the saved
certificate. Changing the statement, its name, the program, or its
profile prevents that reuse. Comments and notes may change while the
compiled program stays the same; examples are checked again on replay.

# The proof-source profile

A proof document is `(proofs V THEOREM…)`, its version `V` being `0` or `1`,
with one or more theorems of distinct names, each
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
writes `geb-proof/v2`. An unknown or unbound name, a name declared twice,
a malformed form, an unsupported version, a false equation or an
unsuccessful search is rejected. Failure of a bounded search does not establish that the
statement is false.

Statements are not yet written over the datatypes of the datatype language,
and no tactic yet performs induction on trees, which needs the lemmas on
the unfolding of trees the Lean developments prove first. The statement
reader and the script interpreter are in `bootstrap/authoring.geb`; they
add no rule to the metalogic.

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
its format (`geb-proof/v2` for version `1`), theory (`free-topos/base/v1`),
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
over datatypes, induction on trees, editor acceptance and completion of
datatype soundness remain separate work.

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
proof document, retaining their original bytes and relative source paths.
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
digest of every other file. `verify` checks this inventory without Lake
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
