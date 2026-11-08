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
annotation and prose profiles. The statement and proof script live in
`Pair.proofs.geb`; the computational definitions live in `Pair.geb`.
The commands below compile the program, check the examples in its notes,
produce a certificate and replay it. This chapter includes the files
directly, checks their prose and references, and replays their certificate
while it builds.

# The development

{gebProgram "examples/authoring/pair.manifest" "Pair.proofs.geb" "record/pair.cert"}

The equality is between the two closed functions, including their
abstractions. It therefore states equality at every pair of arguments;
the example in the note separately checks one evaluation. There is no
Lean source belonging to this development.

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

# The proof-source fragment

Version `0` has one nonempty sequence of uniquely named theorems:

```geb
(proofs 0
  (theorem first-pair
    (equal Pair.first Pair.left)
    (by (normalize 64))))
```

The sides of `equal` are fully qualified names of closed definitions in
the compiled program. They resolve to the definitions' translations into
the metalogic. `normalize` takes a natural-number budget and uses
definition unfolding, beta reduction and the projections of pairs.
An unknown name, duplicate theorem name, malformed form, unsupported
version, false equation or unsuccessful search is rejected. Failure of a
bounded search does not establish that the statement is false.

This first fragment does not expose contexts, hypotheses, arbitrary
terms, theorem dependencies, datatype induction or the other existing
tactics. It gives those extensions an existing document and replay path.
The current statement reader and script executor are in
`bootstrap/authoring.geb`; they add no rule to the metalogic.

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
both source documents, and the SHA-256 digests of the inputs. The digests
pin the compiler image and emitted compiler, the authoring runner and its
source dependencies, the manifest and sources, the Lean toolchain and
dependency lockfile. `record/compiler.img` retains the exact bytes of
`bootstrap/compiler.img` used at the milestone. The certificate envelope separately identifies
its format (`geb-proof/v1`), theory (`free-topos/base/v1`), document profile
and exact compiled program; its declarations retain the statements and
their source names.

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
give that migration explicit inputs. Suspended holes, full proof syntax,
editor acceptance and completion of datatype soundness remain separate
work.

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
