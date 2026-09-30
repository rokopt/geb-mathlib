# Settling Geb's source format

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [The compatibility contract](#the-compatibility-contract)
- [What the existing guarantees do not cover](#what-the-existing-guarantees-do-not-cover)
- [The state of the repository](#the-state-of-the-repository)
- [Source documents and a verified formatter](#source-documents-and-a-verified-formatter)
- [The considerations](#the-considerations)
  - [Readable and canonical S-expressions](#readable-and-canonical-s-expressions)
  - [Documents and separate annotations](#documents-and-separate-annotations)
  - [Hashes and content identity](#hashes-and-content-identity)
  - [Files, assembly and the host boundary](#files-assembly-and-the-host-boundary)
  - [Namespaces and name uniqueness](#namespaces-and-name-uniqueness)
  - [Datatypes, type parameters and interfaces](#datatypes-type-parameters-and-interfaces)
  - [Free-monad and cofree-comonad addressing](#free-monad-and-cofree-comonad-addressing)
  - [Documentation through Verso](#documentation-through-verso)
  - [Structural editing and parinfer](#structural-editing-and-parinfer)
  - [Tree-sitter and a language server](#tree-sitter-and-a-language-server)
  - [Typed holes](#typed-holes)
  - [Synthesis and certificates](#synthesis-and-certificates)
  - [Canonical](#canonical)
  - [Tokens, numerals and editions](#tokens-numerals-and-editions)
  - [Stability of elaboration](#stability-of-elaboration)
  - [Proof scripts and certificates](#proof-scripts-and-certificates)
  - [Comment conventions](#comment-conventions)
  - [N-ary chains in the surface language](#n-ary-chains-in-the-surface-language)
  - [Further requirements before substantial authoring](#further-requirements-before-substantial-authoring)
  - [Scale](#scale)
- [A sequence and its acceptance](#a-sequence-and-its-acceptance)
- [Decisions](#decisions)
- [Open decisions](#open-decisions)
- [Sources](#sources)

<!-- END doctoc -->

This report states what must be fixed about Geb's source and its
authoring tools before most of Geb's code is written in Geb, so that every
later change of format or implementation is a mechanical, provable
translation. It covers the compatibility contracts, the concrete syntax,
comments and documentation, names, files and the host boundary, content
identity, editor tooling, typed holes and synthesis. Two prototypes
implement first steps:

- source documents that keep comments, with a verified formatter:
  [Geb/Prototypes/Kernel/Document.lean](../Geb/Prototypes/Kernel/Document.lean),
  its tests, and `lake exe geb-fmt` ([GebFmtMain.lean](../GebFmtMain.lean));
- checked filling of one contextual hole:
  [Geb/Prototypes/Kernel/Hole.lean](../Geb/Prototypes/Kernel/Hole.lean).

The [Bootstrap chapter](../manual/GebManual/Bootstrap.lean) § Authoring
across bootstrap revisions records their state as milestones; the
[syntax survey](concrete-syntaxes.md) supplies the constructions of syntax
and annotation, and [definitions](definitions.md) those of blocks, linking
and addresses.

Status: report of 2026-09-29. Measurements of the repository refer to
`main` at commit `b3aa139a` with the two prototypes added; those of
external tools name the version measured. The recommendations are
proposals; [Open decisions](#open-decisions) lists those that are the
user's.

## Summary

A later change of format is a mechanical, provable translation exactly
when the source written now records every piece of information a person
supplies, the reading of that source is fixed by a recorded version, and
every artifact that persists has a versioned contract. Whatever a program
can compute from the source — digests, addresses, the separation of
comments from code, highlighting, rendered documentation, reports of
holes, synthesized terms — can be added later without touching what was
written. The work to do first:

1. Read comments and empty lines as data, in a document type that also
   carries declaration and binder names, prose, examples and links
   ([Source documents](#source-documents-and-a-verified-formatter),
   [Documents and annotations](#documents-and-separate-annotations)).
2. Write source in the syntaxes of [RFC9804] (decided): its canonical and
   transport encodings for exchange, hashing and signing, its advanced
   encoding, and a Geb authoring profile extending the advanced encoding
   by line comments and UTF-8 in strings, all four reading into one
   document type
   ([Readable and canonical S-expressions](#readable-and-canonical-s-expressions),
   [Tokens](#tokens-numerals-and-editions)).
3. Make name resolution a function of recorded data: a manifest per
   program, rejection of duplicate and ambiguous names, a namespace
   separator, and hygienic generated names
   ([Files](#files-assembly-and-the-host-boundary),
   [Namespaces](#namespaces-and-name-uniqueness)).
4. Pin elaboration as well as syntax: an edition per program, and a
   committed record of each program's elaborated definitions compared in
   continuous integration ([Elaboration](#stability-of-elaboration)).
5. Version every interface that persists: document and core schemas,
   semantic profiles, datatype encodings, certificates and host protocols
   ([Further requirements](#further-requirements-before-substantial-authoring)).
6. Write comments in Verso markup (decided), with explicit links for
   references to code, since links cannot be added mechanically to prose
   written without them ([Documentation](#documentation-through-verso)).
7. State which steps of the pipeline are proved and which are tested
   ([The compatibility contract](#the-compatibility-contract)).

Content storage, a network of identifiers, a language server,
tree-sitter, richer holes and synthesis derive from the source and follow;
each consideration below states its present obligation, usually none or a
reserved character.

## The compatibility contract

For a syntax with parser `p : C → Option D` and printer `q : D → C`, the
required equation is `p (q d) = some d`: the parser retracts the printer.
Parsing followed by printing is then a partial idempotent, and the printer
is injective; [ConcreteSyntax.lean](../Geb/Prototypes/ConcreteSyntax.lean)
proves both consequences once. For two syntaxes of one document type,

```text
migrate₁₂ c = (p₁ c).map q₂
(migrate₁₂ c).bind p₂ = p₁ c
(migrate₁₂ c).bind migrate₂₃ = migrate₁₃ c
```

follow from the destination's retraction alone. A migration preserves the
parsed document, not its whitespace; a formatter chooses a normal layout
while preserving every name, comment and link the document type holds.

A change of the document or core schema needs a computable map and its
preservation theorem: for a document migration `M`, a core migration `m`
and erasures `erase₁`, `erase₂`,

```text
erase₂ (M d) = m (erase₁ d).
```

Widening a grammar is the case in which `M` is an embedding and `m` the
identity. A lossless change needs an inverse or a retained representation
of the old information. Three conditions make migration available:

- completeness of the document type: whatever a person wrote that it
  omits is lost by every migration
  ([concrete-syntaxes.md](concrete-syntaxes.md) § The laws must be lifted
  to the annotated level);
- determinism of the reader relative to recorded context: a migration
  replays the old reader, its rules of resolution included, and whatever
  the reader consults, such as the order in which files are joined, is
  recorded;
- an image in the new edition for every old document.

Two consequences follow. Restrictions cost little before code exists and
much after, and extensions the reverse, so the grammar is made as narrow
as present code requires. And a feature may be deferred when its data is
a function of the document.

Until the bootstrap completes, no source is kept unchanged for its own
sake (decided; [Decisions](#decisions)). Geb is built from scratch and has
no users to keep compatible, so whatever is preferable is adopted
everywhere, every source converted to it, mechanically where the
contract above permits and by hand where it does not. And the languages
admit exactly what the mathematics states: no implicit coercion, no
silent conversion, no convenience that makes a term differ from the
mathematical object it denotes. Editions and importers exist to make
conversions mechanical and to state what a conversion preserves, not to
keep old code in use.

Universal properties fix the interpretation up to the relevant
isomorphism, or equivalence where categories are compared. They supply no
serialized schema, executable migration, source location or bound on
cost. A replacement implementation provides the comparison and shows that
interpretation commutes with it; where representations of input or output
change, the maps of observation commute as well.
[definitions.md](definitions.md) § Content identity separates equality of
presentations from equality of their denotations in the same way.

Libraries need their own contract. Two sound provers may return different
certificates, or succeed on different inputs; soundness does not make them
equal as Geb functions returning certificates. A replacement keeps the old
dependency available or is proved equal for the observations its interface
permits. Hiding a certificate behind a proved abstraction permits changes
of its representation; promising only some checked witness does not erase
differences a client can observe. Exact agreement with the Lean
implementation is a milestone of the bootstrap, not a choice of that
public contract.

The compatibility policy covers accepted programs of a named profile. A
program that depended on an implementation error may admit no migration to
the corrected meaning preserving its semantics: its source and compiler
profile are kept, the discrepancy is identified, and a repair is decided
explicitly. Neither a universal property nor a converter infers which
behavior the author intended.

The verification boundary is tracked through the whole pipeline.
Soundness of the metalogic's checkers and their agreement do not prove the
reader, the serializer, the code generator, the host compiler or the file
driver correct, and the bootstrap's fixed points, byte for byte, are
evidence against regression, not preservation theorems. Which steps are
proved and which tested is stated explicitly, the agreement of the word
codec with the wire form, tested and not proved, among them.

## What the existing guarantees do not cover

Geb specifies an abstract syntax with a retraction to each concrete one,
and its semantics by universal properties: the first protects the kernel
term and the second its denotation. Four things lie outside both.

1. Content that is not a kernel term: comments, names of bound variables,
   abbreviations and layout. A retraction at the level of kernel terms
   prints `app (lam A b) e` where a person wrote `let` or `defn`, and loses
   numeral abbreviations such as `Label.app`, which the reader expands
   before resolution. The formatter's retraction therefore belongs at the
   level of documents; the retraction at the level of kernel terms, the
   Bootstrap chapter's printer for the kernel's readable syntax, serves
   generated code and decompilation.
2. Elaboration. The datatype language is defined by a Geb program,
   [bootstrap/stage1/datatype.geb](../bootstrap/stage1/datatype.geb), and
   its encoding (the constructor of position `i` as the node of label `i`
   over its fields, `&` taking the remaining children) is observable:
   sources use it directly, as
   [bootstrap/free-topos/base.geb](../bootstrap/free-topos/base.geb) does
   for optional trees. A revision of the expansion changes the meaning of
   existing source while every universal property still holds. Elaboration
   need not be invertible, since a printed expansion cannot recover the
   author's abstractions: the authoring document is kept beside its
   elaborated result, and the elaborator is versioned
   ([Elaboration](#stability-of-elaboration)).
3. Proof scripts. A proposition of the metalogic keeps its meaning, but a
   tactic script is a program for one prover
   ([Proof scripts](#proof-scripts-and-certificates)).
4. Organization: which definitions form a program, their order, files,
   sections and namespaces, recorded now in the source lists of
   [scripts/bootstrap.sh](../scripts/bootstrap.sh) and in the
   `include_str` definitions of the tests.

## The state of the repository

| Component | Contract or limitation |
| --- | --- |
| [Kernel reader](../Geb/Prototypes/Kernel/Reader.lean) and [its Geb counterpart](../bootstrap/reader.geb) | Resolve definition names to positions in the bundle and binders to de Bruijn indices; expand abbreviations; discard comments. An atom is any run of characters other than whitespace, parentheses and `;`, one character per byte; there are no strings and no program printer. |
| [Source documents](../Geb/Prototypes/Kernel/Document.lean) | Read comments and empty lines into a document conservatively over the kernel reader, and print it at any layout with a proved retraction ([Source documents](#source-documents-and-a-verified-formatter)). Binder names at the level of kernel terms are not yet kept. |
| [Canonical S-expressions](../Geb/Prototypes/CanonicalSExpr.lean) | Proved retractions for the presentations of trees over a finite alphabet; the generic renderer counts characters, so its conformance to [RFC9804] holds for ASCII atoms. |
| [Readable S-expressions](../Geb/Prototypes/ReadableSExpr.lean) | A proved syntax of rose trees labelled by numerals, distinct from the kernel reader and from the advanced encoding of [RFC9804]. |
| [Definition vertices](../Geb/Prototypes/Definition/Vertex.lean) | Selection of subterms, composition of addresses and their laws: a basis for addressing occurrences. |
| [Images](../Geb/Prototypes/Kernel/Image.lean) | A versioned bundle keeping definition names, without binder names or comments; the word codec's agreement with the wire form is tested, not proved. |
| [File driver](../Geb/Prototypes/Kernel/Command.lean) | Joins ordered source files with a newline; file operations stay in the host. |
| [Lean emitter](../bootstrap/stage1/lean.geb) | Emits definitions under their names with a generated module comment; variables are named by depth, and author documentation and source spans are not carried. |
| [Contextual hole filling](../Geb/Prototypes/Kernel/Hole.lean) | Checks and fills one explicitly typed contextual hole, with theorems for the result's typing and denotation; a Lean interface, not a surface or editor feature. |

The syntax prototypes' retractions do not yet certify the migration of
bootstrap programs: the connection needs arbitrary atom bytes, the program
grammar, name resolution and the document. The facts below were measured
at commit `b3aa139a`.

- The 21 files under `bootstrap/` (about 250 kilobytes):
  - use atoms from `[A-Za-z0-9.&-]` only, each a numeral, an identifier
    beginning with a letter, or `&`;
  - contain only whole-line comments: a header per file followed by an
    empty line, blocks immediately before a top-level form, and blocks
    immediately before a sub-form, the last all in the chains of
    conditionals of
    [bootstrap/goedel-t/equations.geb](../bootstrap/goedel-t/equations.geb)
    but for one each in
    [bootstrap/stage1/lean.geb](../bootstrap/stage1/lean.geb) and
    [bootstrap/goedel-t/prove.geb](../bootstrap/goedel-t/prove.geb);
  - have comments whose only character special in Verso or Markdown
    markup is a single `_`;
  - form programs, joined as `scripts/bootstrap.sh` joins them, without a
    duplicated name.
- The reader resolves a duplicated definition name to the first
  definition, and a duplicated `deftype` or `defnum` to the latest, and it
  substitutes numeral abbreviations into binder names, `expandNums`
  running before resolution. No source relies on these; a migration
  replays them.
- Dependencies between files are recorded in prose only ("Requires the
  prelude, the reader and the checker").
- Content identity is designed: the node-digest rule, the migration from
  positions to digests and the annotation tables keyed by vertex
  ([Bootstrap chapter](../manual/GebManual/Bootstrap.lean) § Definitions,
  references and identity; [definitions.md](definitions.md) § Content
  identity). The choice between BLAKE3 and SHA3-256 is open.

## Source documents and a verified formatter

A document is a list of items, each a `RoseTree Lab` with
`Lab = {gap : Bool, kind : atom s | list | comment s}`. Comments are items
in document order, not annotations of the nodes after them: the design of
the lossless syntax trees of Roslyn and of rust-analyzer's rowan, and of
rewrite-clj, on which cljfmt and zprint are built. Reading attaches no
comment to a node; an attachment is a separate function of the document.
An empty line is a flag on the item after it, as gofmt and ormolu keep at
most one empty line between items. The lexer reads one character per
byte, as the kernel's readers do, so atoms and comments keep their bytes.

Three theorems hold, none depending on `Classical.choice`:

- `readDoc_erase`: `(readDoc t).map (·.filterMap eraseItem) = readSExps t`
  at every text `t`. Erasing the comments of what the new reader reads
  gives what the kernel's reader reads, so adopting it changes the meaning
  of no file.
- `readDoc_print`: `readDoc (print L items) = some items` at every
  well-formed document and every layout `L`, a function from the positions
  of tokens to a choice of line break and indentation. The separator
  before a token is a fixed function of the token before it, the token and
  the layout's choice (`sepFor`), and the lexer is proved correct for every
  sequence of separators so formed, so the layout policy is outside what
  is proved.
- `format_format`: the formatter is idempotent.

Measured on a copy of the files under `bootstrap/`:

| Check | Result |
| --- | --- |
| Formatting all files | 0.11 s |
| `geb-fmt --check` after formatting | no file changes |
| Stage-0 image from formatted sources, built by the seed | the original's, byte for byte |
| Stage-1 image from the formatted compiler, built by the stage-0 compiler | the original's, and `bootstrap/compiler.img`, byte for byte |
| Lean emitted by `bootstrap/compiler.img` from the formatted compiler | `bootstrap/lean/GebBoot.lean`, byte for byte |
| parinfer 3.13.1, Paren Mode and Indent Mode, on formatted files | no file changes |
| parinfer on the files as written | 16 files changed by Paren Mode, 15 by Indent Mode, and an Indent Mode error in `goedel-t/prove.geb` |
| Lines beyond 100 columns after formatting | 17, all comments in the chain of conditionals of `goedel-t/equations.geb` |

The layout policy (`planStep`, `planElem`) writes a list that fits on one
line; otherwise its elements fill the first line while they fit, the
parentheses that close after them included, and the rest begin lines
indented past the list's opening parenthesis, by two columns after an
atom at its head and by one otherwise (decided; [Decisions](#decisions)).
An element that does not fit is not hung on the current line: a body's
indentation then depends on its depth of nesting alone, so renaming a
definition changes one line of a diff rather than every line of the body,
and a chain of nested forms indents by two columns a level rather than by
the width of everything before it. Its output meets parinfer's
invariant: each continuation line is indented beyond the innermost open
parenthesis and not beyond a parenthesis closed at the end of the line
before ([parinfer](https://shaunlebron.github.io/parinfer/#mathematical-foundation)).
The written files place a nested `let` or conditional at its parent's
indentation, which parinfer's Indent Mode reads as closing the parent. The
same cause produces the long lines: the kernel's binary conditional and
single-binding `let` make chains nest, and nesting is indentation under
any layout parinfer admits
([N-ary chains](#n-ary-chains-in-the-surface-language)). Parinfer's Paren
Mode, which never changes the tree, would also serve as a formatter, but
its equations are stated properties, not proofs for Geb's grammar; the
formatter here has its proofs.

The prototype leaves three things open. A list whose last element is a
comment prints its closing parenthesis at the start of a line, which
parinfer rejects; no file has one. The alphabet of atoms is the kernel
reader's, without quoted atoms. And the attachment of comments to
vertices, which hover text and a store need, is a fold over the document
not yet written.

## The considerations

### Readable and canonical S-expressions

Geb's source is written in the syntaxes of [RFC9804] (decided;
[Decisions](#decisions)). The RFC specifies a canonical encoding, designed
for hashing and signing, a basic encoding for transport, which is the
base-64 of the canonical one, and an advanced encoding for people. It is an
Informational RFC, not on the standards track, and requires an
implementation to support the first two, the third being optional (§ 6).
Its atoms are octet strings with optional display hints, and canonical
lengths count bytes. An advanced token is a letter or one of
`- . / _ : * + =` followed by letters, digits and those marks, so it cannot
begin with a digit. Quoted strings admit printable ASCII alone: a line
break or any other byte is escaped (`\n`, `\xhh`, `\ooo`) or continued by a
backslash before the break. The advanced grammar has no comments (§§ 4,
7.1).

Four syntaxes read into one document type:

- the canonical encoding, for exchange, hashing and signing: a
  definition's digest is taken over the canonical bytes of its
  identity-bearing payload ([Hashes](#hashes-and-content-identity)), and
  the canonical bytes of a source document identify the document;
- the basic encoding for transport, completing conformance;
- the advanced encoding, strictly as specified, printed when a conforming
  readable file is wanted;
- a Geb authoring profile, in which source is written by hand: the
  advanced encoding with its extensions, `;` line comments, read as items
  of the document as in
  [Source documents](#source-documents-and-a-verified-formatter); UTF-8
  and line breaks inside quoted strings; numerals as bare runs of digits;
  `&` as a token; and `?name` as shorthand for the form `(hole name)`
  ([Tokens](#tokens-numerals-and-editions)). Each
  extension is unambiguous against the advanced grammar, so every strictly
  conforming advanced file is a file of the profile. The profile is not
  called [RFC9804].

The strict encodings have no comments, so they carry the document's
comments and empty lines as annotation forms, lists headed by a reserved
token such as `*ann`, as the survey's annotated examples do
([concrete-syntaxes.md](concrete-syntaxes.md) § One tree, every recommended
encoding); a list of code headed by that token is excluded, so that
annotation and code are never confused. A strict quoted string escapes each
non-ASCII byte and line break, and a canonical verbatim atom holds the
bytes as they are, so prose passes through every syntax unchanged.

Each syntax's printer is a section of its parser into the document type,
so the migrations among the four are those of
[The compatibility contract](#the-compatibility-contract): each preserves
the parsed document, and they compose. The four share code as far as their
grammars allow:

- the document type and its well-formedness, and the encoding of comments
  and empty lines as annotation forms;
- the choice of an atom's spelling from its bytes: a token where one is
  legal, else a quoted string, else a hexadecimal or verbatim atom;
- the decimal layer of length prefixes, which verbatim atoms and quoted
  and hexadecimal atoms with lengths share, and which `Csexp.decOf` and
  `Csexp.digitsVal` implement already;
- base-64, for the transport encoding and for base-64 atoms;
- escaping and its inverse, parameterized by the bytes a profile admits
  unescaped;
- the loop over a list's elements (`Rose.parseChildren`);
- for both advanced syntaxes, the lexer and printer of
  [Source documents](#source-documents-and-a-verified-formatter), with its
  separators chosen by the layout;
- the generic corollaries of the retraction law, proved once in
  [ConcreteSyntax.lean](../Geb/Prototypes/ConcreteSyntax.lean).

The present `.geb` sources are in a legacy syntax, the kernel reader's,
which the document reader of the prototype reads. An importer converts
them into the authoring profile; it is accepted when the actual bootstrap
sources convert with names and comments preserved and compile to the same
checked bundles, which a proof over trees of numerals does not show. Until
the readers of the seed and of Geb read the profile, a converter from the
profile to the legacy syntax, proved to preserve the document, feeds the
compilers.

Further:

- Atoms are byte strings preserved exactly; human names and prose are
  UTF-8, without implicit Unicode normalization. Whether an atom names a
  numeral, an identifier or a datum is decided by Geb's grammar, not by
  the S-expression layer, so a change of spelling changes no decoded
  bytes.
- A canonical file holding arbitrary bytes is not an editor buffer, since
  trimming whitespace or converting encodings corrupts a length-prefixed
  atom.
- Display hints are excluded, as [RFC9804] § 8 permits; format
  information is a field of the document, and hints accepted later keep
  their bytes.
- The existing canonical codec,
  [CanonicalSExpr.lean](../Geb/Prototypes/CanonicalSExpr.lean), is proved
  over trees of numerals and counts characters, so its conformance holds
  for ASCII atoms; it is generalized to byte atoms and to lists of every
  shape, empty or headed by lists. The advanced encoding's parser and
  printer and the inverse of its escaping are new, the separators and
  lexer lemmas of the document prototype carrying over.
- Kernel terms also have a canonical, versioned exchange format, the image
  (`Geb.Kernel.writeImage`), compared by bytes in continuous integration.
- The syntax unification of the Bootstrap chapter, one reader over the
  canonical data model with a quoted spelling for atoms that are not
  tokens, is this decision; its first use replaces the lists of character
  codes of [bootstrap/stage1/datatype.geb](../bootstrap/stage1/datatype.geb),
  such as `(quote (1 108 101 116))`, by quoted atoms.

### Documents and separate annotations

Comments never reach the image, and the compiler reads the core tree only,
so their separation has no motive at compilation. Its motives are identity,
the digest excluding annotations; reuse of a checked core when only
documentation changes, whose benefit is to be measured; and a future
content store. Two arrangements are available.

- Text is primary, comments are data in it, and the separation into core
  and annotations is derived when reading, in memory and in build
  artifacts. The file is the combined view, so editors, diffs, merges,
  reviews and searches need nothing new. Precedents:
  [Clojure's metadata](https://clojure.org/reference/metadata), which does
  not affect equality or hashes;
  [Dhall](https://docs.dhall-lang.org/discussions/Safety-guarantees.html),
  which hashes a normal form without comments; and
  [Yatima](https://github.com/argumentcomputer/yatima-lang-alpha), whose
  `Term::embed` separates a nameless tree for the content identifier from
  a tree of names of the same shape, and whose `unembed` rejoins them and
  fails when the shapes differ. Darklang returned from a structure editor
  to text as the source of truth
  ([status update](https://blog.darklang.com/an-overdue-status-update/)).
- Two independently authoritative artifacts, core and annotations, with
  text as a projection: Unison, Lamdu, MPS, and Unison's design of 2019,
  not built, of comments keyed by a hash and a path
  ([unison#443](https://github.com/unisonweb/unison/issues/443)). They need
  atomic updates, detection of stale annotations and coordinated merging.
  Keys by path move under edits, as Go's comment map does
  ([golang/go#20744](https://github.com/golang/go/issues/20744)); keys by
  hash conflate structurally equal definitions
  ([unison#462](https://github.com/unisonweb/unison/issues/462)); Unison
  drops comments inside terms when they are added to its codebase
  ([language reference](https://www.unison-lang.org/docs/language-reference/comments/),
  [unison#6262](https://github.com/unisonweb/unison/issues/6262)) and
  removed its metadata links
  ([unison#4574](https://github.com/unisonweb/unison/pull/4574)).

The first is recommended; the second is adopted when a store or editor
provides those operations, with a proved conversion from the single
document. The document keeps at least:

- declaration and binder names, ordered prose, links, examples, and the
  associations of source to core;
- unknown annotation fields of a known version, kept on read and write;
- everything that affects elaboration — type annotations, datatype
  encodings — in the checked input, since calling such information a
  decoration must not let its erasure change meaning.

The side table is a function `attach : List Item → Core × (Vertex ⇀ Notes)`
of the document. Its keys identify occurrences relative to one revision of
a document or definition: two equal subtrees can carry different comments,
which a key made from their hash cannot distinguish, while metadata meant
for every instance of an equal definition uses that definition's content
identity; the two are different attachments
([concrete-syntaxes.md](concrete-syntaxes.md) § Wrapper model, environment
model, and the occurrence pitfall). A path means something only at its
identified root, and a change of representation transports paths. An edit
of a program can delete, duplicate or merge occurrences, so a migration of
meaning cannot place every comment: an explicit map of the edit is kept,
or unmatched annotations are kept for reconciliation, never attached to
the nearest equal subtree. A map of sources through elaboration is a
relation, one source form generating several core nodes. A store, when one
exists, keys annotations by the named entry, a core digest with its names,
as Yatima does, and checks shapes as `unembed` does.

### Hashes and content identity

The payload that bears identity is frozen before durable identifiers are
published. The block proposal of [definitions.md](definitions.md)
§ Content identity is its starting point:

```text
(schema version, semantic profile reference,
 import interface, export layout, definition bodies)
```

The profile fixes primitive identities, binding rules and the
interpretation of the representation; display names and comments stay
outside the payload; types and certificates are inside it when they affect
meaning, and a separately checked certificate of an identified term is an
artifact of its own.

- An identifier is versioned and carries a multihash, or is a CIDv1 of an
  actual serialized block with a specified codec. A multihash names an
  algorithm and a digest; it neither versions Geb's schema nor specifies
  the bytes hashed, and a CID also names the codec
  ([IPLD primer](https://ipld.io/docs/intro/primer/)). A structural digest
  of the Merkle kind is not presented as the CID of unrelated exchange
  bytes.
- One algorithm is chosen, between BLAKE3 and SHA3-256, before
  identifiers are assigned; the envelope and the tags of
  [concrete-syntaxes.md](concrete-syntaxes.md) § Structural
  content-addressing specification are fixed then. The choice does not
  delay writing source. A local store of canonical blocks suffices at
  first; networking, CAR archives, digests per node and deduplication
  across graphs are features of storage for later.
- This is structural identity, not semantic identity: renaming bound
  variables leaves the resolved representation unchanged, while inlining,
  changing a derived operation or choosing another proof usually does
  not, and semantic equivalence belongs to checked certificates. Equal
  finite digests prove nothing about unbounded trees: retrieved content is
  verified, payloads are compared before objects are identified, and an
  identifier associated with conflicting payloads is rejected.
- Unison separates names from identity and refers to a member of a
  recursive component by the component's hash and an index
  ([hashes](https://www.unison-lang.org/docs/language-reference/hashes/));
  Geb uses its validated export direction for the index.

Nothing is needed in the source now. Before digests exist, a reference is
a position relative to a complete frozen bundle and its profile, never a
globally meaningful integer; complete bundles, their profiles and their
order of dependencies are kept. The migration to digests runs in that
order, rewrites the constructor of external references, produces a map
from old references to new, and re-keys annotations with it; a later
change of algorithm or schema computes new identifiers without promising
equal ones. The traversal follows the grammar: a data tree inside a
quotation may contain the label of the reference constructor without
being a reference, as
[the substitution traversal](../Geb/Prototypes/Kernel/Subst.lean) already
treats quotations apart from term children, and reflective code values
need an identified schema and a transport of their own. A digest literal in
source, pinning a dependency as Unison's `#…` does, is a hexadecimal or
base-64 atom of [RFC9804] that Geb's grammar reads as a reference.

### Files, assembly and the host boundary

Files stay outside Geb's semantics: they organize writing and delivery,
and semantic dependencies are references to definitions.

- A manifest per program, an S-expression naming the program, its edition,
  its sources in order and its entry points, is read by the host driver,
  the tests, the formatter and a language server. It replaces the lists in
  `scripts/bootstrap.sh` and the tests, and the dependencies stated in
  comments. No scan of directories or working directory decides the order
  of binding implicitly.
- The first linker keeps the present well-founded order, resolves each
  import to an explicit definition, rejects unresolved and ambiguous
  references, and checks the bundle; references by digest replace frozen
  positions later. General cyclic blocks and a canonical order of
  recursive components are unnecessary for the bootstrap's recursion by
  folds, and sorting the members of a cycle by their digests does not
  solve symmetric cycles.
- Generated names are made hygienic before a large library is written:
  identifiers the expansion generates are reserved or its expansion is
  hygienic, and emitted Lean names escape injectively with the runtime's
  names qualified. The Bootstrap chapter records the capture of primitives
  in the datatype language's expansion and the conflicts with emitted `T`,
  `leaf` and `mk`.
- Converting existing source replays the old resolver, so that the
  meaning to be re-expressed is known exactly, and the converted source
  then follows the new reader's rules, duplicates rejected; no present
  source has one.

Interaction with the operating system stays a pure interface of requests
and results with an interpreter in the host. Byte encoding, framing of
input and output, errors and exhaustion of resources have explicit
contracts, which a later interface of effects implements. Paths, clocks,
environment variables and the width of machine integers are never hidden
semantic inputs.

With content identity, a file is a view: a path in a namespace names a
definition's digest, and a program's order is the order of its references.
The manifest migrates mechanically into that; names being unique, a file
resolves alike in every program that includes it.

### Namespaces and name uniqueness

A namespace is a block form, `(namespace X forms…)` (decided;
[Decisions](#decisions)). It does not depend on files, so the same source
can be kept in files, in a database or in a content-addressed store, and
membership in a namespace is structural: a namespace is a subtree of the
document, and a definition's namespace travels with it. Blocks nest, each
level indenting its contents by two columns under the layout policy, so the
depth of nesting shows at a glance. A block may be reopened: several blocks
of one name contribute to one namespace, so a namespace can span files or
entries of a store. `(open Y)` within a block opens `Y` for that block
alone. A name resolves in the current namespace, then in the enclosing
ones, then in the opened ones, then as a name qualified from the root; an
ambiguous or unresolved name is rejected. `.` separates the components of a
qualified name, being a token character of [RFC9804] and already used so
(`Label.app`, `Prim.add`, `Rule.hyp`); `namespace` and `open` are keywords
no definition may shadow.

A block's export list names the definitions visible outside it, and a
block without one exports nothing (decided): a test's ad hoc definitions,
for instance, stay unreachable from other code. The resolver rejects an
entry naming nothing; the interface of a reopened namespace is the union of
its blocks' lists; and a nested block's name is visible outside an
enclosing block only if every block on the way exports it.

Names are annotations and bear no identity, so namespaces are a matter of
the reader and migrate mechanically. Now: reject duplicates and reserve `.`
for qualification. Then organize the present sources into namespace
blocks with export lists, before the sources grow. Prefixes that avoid collisions,
such as `mTypeIn` beside `typeIn`, otherwise accumulate, and removing them
later is renaming by hand. A whole namespace written as one block is one
form, so an unbalanced parenthesis inside it leaves the block unreadable;
the kernel's reader already rejects an unbalanced text as a whole, and a
language server's recovery from errors, not the reader, answers it. The
block's closing parenthesis ends the line of its last definition, so
appending a definition changes that line too.

### Datatypes, type parameters and interfaces

The sources annotate every value of a declared datatype as `T`:
[bootstrap/free-topos/partial-horn.geb](../bootstrap/free-topos/partial-horn.geb)
declares `(data Eqn (eqn T T))`, and functions over optional trees take
`(m T)`. The expansion of the datatype language ignores the types of
fields. Which datatype a value is meant to belong to is therefore recorded
nowhere, and it is information no tool recovers later. It is not the
intended state: the Bootstrap chapter's layers make the datatype
language's types denote recognized types, a datatype being the subset of
trees its recognizer accepts, a subobject `{t : T | rec_D t}` of the tree
object in the metalogic, whose language is typed throughout; and it lists
the datatype language's completion, generated recognizers, type
parameters and a static check of datatypes, as ready. The completion comes
before substantial authoring (decided; [Decisions](#decisions)), in these
parts:

| Part | Content |
| --- | --- |
| Datatype names as types | `(m Opt)` rather than `(m T)`, in fields, parameters and results |
| Static check at every use | constructors produce `D`, case analysis and structural recursion consume `D`, fields and results are checked; `D` and `T` are distinct types, with no implicit conversion between them |
| Representation and decoding | `D`'s representation `D → T` and its decoding `T → 1 + D`, each written explicitly where it is used |
| Generated recognizers | the kernel program deciding membership in `D`, which decoding and the meaning of `D` need |
| Type parameters checked opaquely | a parameter `X` has no representation; instantiated at elaboration, the Bootstrap chapter's decision, with the interface's operations passed as values |
| Soundness of the typing | a checked program maps members of `D` to members of `E`, so that typed programs translate into morphisms between subobjects |

All six precede substantial authoring (decided); the last is proved with
the metalogic's prover in Geb, which is being written.

The types are exactly those of the mathematics. A datatype `D` is the
initial algebra of the polynomial functor its declaration presents: its
constructors are the algebra's structure map, its case analysis the
inverse that Lambek's lemma gives, and its structural recursion the fold.
The encoding of a constructor as the node of its position over its fields'
encodings makes the trees an algebra of the same functor, so initiality
determines the representation `D → T` as the unique algebra morphism,
chosen by no convention; it is a monomorphism, and `D`'s recognizer cuts
out its image. The recognizer decides membership, so the image is a
complemented subobject and decoding `T → 1 + D` is a total morphism. `D`
and `T` are distinct types: a tree operation such as `label` or `child`
applies to a value of `D` only through its representation, written where
it is used, which marks exactly the code that depends on the encoding.
The kernel erases the distinction, the representation compiling to the
identity on trees, and the soundness of the typing relates the two.

The first five are work of the elaborator, a Geb program; the kernel is
unchanged, and the check is outside the trusted base, since a wrong check
can accept an ill-typed program but cannot change a kernel term's meaning.
Every source of the datatype language is retyped exactly, the metalogic's
checker in Geb included; the stage-0 sources, written in the kernel's
syntax, keep the kernel's types, exact for a kernel whose only type of data
is the trees. The soundness theorem lets a proof use a datatype's type as a
hypothesis; it is proved by induction on the check.

Abstraction is mathematical, not syntactic, and needs no mark of its own.
An interface is a theory, a presentation of operations and axioms
([definitions.md](definitions.md) § Definitions as presentations). Generic
code is a term over it, parameterized by an opaque type and by the
interface's operations, so it holds no reference to a concrete type and
has no representation to inspect. Instantiation is interpretation by the
universal property, evaluation into an implementation, a model of the
theory, as `Geb.Definition.eval` and `derivedAlg` evaluate. In the
metalogic this is the topos generated by the language extended by the
interface's constants and axioms, from which an implementation determines
a logical functor, so a theorem proved of the generic code holds of every
instance [LambekScott1986]. A certificate is a hypothesis: code using a
proof of a proposition works under it, the slice over the proposition's
subterminal, and instantiating supplies the proof. The prover's contract,
any checked certificate of the statement, is kept by clients written so.

Type parameters are sorts through the bootstrap. After it, written in Geb
among the first items, they become parameters over internal universes
(decided; [Decisions](#decisions)). A universe is a family `El → U`, `U` an
object of codes and `El X` the type the code `X` names. Two are defined
from the exponentials and power objects every topos has
[MacLaneMoerdijk1992], and interpret a code by membership. Every value is a
tree and a datatype is a complemented subobject of `T`, so the datatypes
have codes in `2^T`, the morphisms `T → 1 + 1`, a datatype's code being the
transpose of its recognizer, with `El X = {t : T | X t = 1}`; and the
subobjects of `T`, the setoid language's subset types of trees among them,
have codes in the power object `Ω^T`, with `El X = {t : T | t ∈ X}`.
Internal categories whose objects and arrows are carried by subobjects of
`T` form an object too, a subobject of a product of power objects, so a
pair of such a category and one of its objects is a parameter of an
ordinary type; using the elements of that object takes an interpretation
of the category in a universe. Code generic over an opaque sort converts to
code over a universe by the universal property above: sending the sort to
the generic family `El → U` is a model of the extended language in the
slice over `U`, which determines a logical functor, so every theorem about
the generic code holds of the converted code [LambekScott1986].

No universe interprets every object of the topos. The free topos with a
natural numbers object contains arithmetic, and its syntax, being
inductively generated, has codes in it. A family `El` over the codes of its
objects with `El ⌜A⌝ ≅ A` for every closed object `A` would, at the codes
of subterminals, make `Tr c := ∃ e : El c` satisfy `Tr ⌜φ⌝ ↔ φ` for every
closed proposition `φ`. The diagonal lemma gives a `ψ` with
`ψ ↔ ¬ Tr ⌜ψ⌝`, hence `ψ ↔ ¬ψ`, which is contradictory in intuitionistic as
in classical logic; the free topos being non-degenerate, no such family
exists, which is the undefinability of truth [Tarski1935]. The codes of the
whole language are therefore data that a program constructs and inspects
but that no program interprets uniformly, and each universe interprets a
part of the topos. Within their parts `2^T` and `Ω^T` meet no such limit,
since their codes are not syntax: a code is the subobject itself, an
element of an exponential or a power object, and no step interprets a
program's text.

### Free-monad and cofree-comonad addressing

The constructions of
[Geb/Prototypes/Definition/Vertex.lean](../Geb/Prototypes/Definition/Vertex.lean)
are reused. A direction of the free monad selects a variable leaf, a
vertex any node; an export layout marks exports as variable leaves
deliberately, and an annotation on an internal expression uses a vertex.
Treating the two kinds of address as one loses occurrences.

Now: record the vocabulary of addresses as those vertices, with the root
of each, and check paths on input wherever a path is read; the compact wire
spelling and a surface syntax for navigation wait. Addresses become
persistent only when a table keyed by vertex is stored, which the
arrangement recommended above never does, or when a reference is a digest
of a block with a direction, which blocks of several members, absent from
the kernel, need. A change of representation supplies a transport of
addresses with a proof that selection commutes with it; an isomorphism of
values alone does not preserve a chosen set of addressable intermediate
nodes. The finite decorated trees of
[ConcreteSyntax.lean](../Geb/Prototypes/ConcreteSyntax.lean), with their
comonad laws, or their side-table presentation with a proved
correspondence, serve the annotations; [concrete-syntaxes.md](concrete-syntaxes.md)
§ The document type is a μ, not a ν distinguishes them from the possibly
infinite cofree comonad, and no new comonad is a prerequisite. The
prototype's `RoseTree Lab` keeps comments as siblings, and `attach` makes
them the `Ann` components.

### Documentation through Verso

The markup of comments is Verso's (decided; [Decisions](#decisions)).
Its storage is fixed before substantial prose is written, and rendering
follows once storage round-trips. The comments of the sources read as
Verso inline text but for one `_`, whereas a reference such as
``{name}`infer_subst` `` cannot be inferred mechanically from prose that
reads "the substitution theorem". A migration keeps unmarked prose byte for
byte but cannot tell which words were meant as references, so references
that should follow renaming are marked from the start. The roles are the
four the repository's Lean modules use, `{name}` resolving Lean constants
as it does there, and one more, `{geb}`, for Geb definitions,
resolved through the compiler's maps of names and sources against the
manifest, so that a comment citing both a Geb definition and the Lean
theorem about it is unambiguous; both are checked when documentation is
built. Verso's design suits this use: its markup fails on mismatched or
unmatched delimiters rather than guessing, parses with little lookahead,
and extends by roles and directives rather than textual sub-formats
(Verso's user guide, § Design Principles). Verso's markup is defined by
its implementation in Lean rather than by an independent specification,
so a field of format and version with the prose's bytes records the
subset in use, and permits starting from that subset without a complete
parser; `scripts/extract-pr.sh` converts the four roles to Markdown where
Markdown is wanted. The convention the sources follow is kept: a block of
comments immediately before a form documents it, and a block followed by
an empty line is prose.

Documentation renders as a literate page per Geb file, generated from its
document (decided; [Decisions](#decisions)): top-level comments become
prose and forms become code blocks of a `geb` expander (Verso supports
`@[code_block]` expanders, as its `InlineLean` shows), which reads each
block, fails the build of documentation on one that does not read, and
anchors each definition; Lean may still check its examples. The page shows
the Geb source, rendered as the repository's literate Lean modules are,
and the compiler is unchanged. One implementation writes each Geb file as a
generated literate module holding only its prose and `geb` blocks, which a
chapter includes by `includeLiterate` as it includes any literate module.

The alternative, docstrings in the emitted Lean, would render Geb's prose
beside the Lean denotations, generated artifacts, rather than the source,
and would change the backend
[bootstrap/stage1/lean.geb](../bootstrap/stage1/lean.geb) and its committed
artifacts. What it alone offers, documentation on hover where a Lean proof
cites an emitted definition and the emitted definitions in doc-gen4's
reference, remains available as a further renderer of the same document:
docstrings pointing to the page, generated with Lean's comment delimiters,
quoted identifiers and markup escaped explicitly, since a string
interpolated into generated Lean is not a safe encoding of a document.

The model of documentation stays independent of its renderer, which
permits either view and renderers without Lean. Files whose comments come
first and literate Markdown whose prose comes first are two printers of
one document type, so either can be adopted later mechanically. The
acceptance is a module with a description, a documented definition, a
checked example and a cross-reference; editing only its documentation
changes the rendered manual and the document's identity and leaves the
checked core's identity unchanged.

### Structural editing and parinfer

The following was determined for VS Code on 2026-09-29.

- Bracket pairs are coloured without an extension
  (`editor.bracketPairColorization.enabled`, the default since version
  1.67); brackets inside comments are skipped only when a TextMate grammar
  marks the comment as one
  ([bracket pair colorization](https://code.visualstudio.com/blogs/2021/09/29/bracket-pair-colorization)).
  A language configuration and a small TextMate grammar are declarative
  features and need no language server
  ([language extensions](https://code.visualstudio.com/api/language-extensions/overview)).
- [Mike's Paredit](https://marketplace.visualstudio.com/items?itemName=MikeDelmonaco.paredit)
  (`MikeDelmonaco.paredit`, MIT) extracts Calva's structural operations
  (navigation, selection, slurp, barf, raise, splice, transpose, wrap,
  kill), is independent of language, takes delimiters per language
  (`paredit.customDelimiters`) and reads the comment configuration of a
  language's extension. It had 29 installations, so it is pinned and
  tested. `ailisp.strict-paredit` 0.3.1 fixes the languages it serves
  (`commonlisp`, `clojure`, `lisp`, `scheme`), and Calva's paredit serves
  Clojure only.
- The parinfer extensions (`shaunlebron.vscode-parinfer` 0.6.2 and its
  forks) fix their languages likewise. The library `parinfer` 3.13.1
  exposes `parenMode` and `indentMode` over whole texts and treats `[`,
  `]`, `{`, `}` as parentheses, `"` as a string delimiter and `\` as an
  escape, so atoms containing them break it. Paren Mode never changes the
  tree; Indent Mode changes it by design and is an operation of editing,
  not a formatter.

Paredit and parinfer are alternative models of editing the same balanced
text, and neither bears on the document type, the reader or the
formatter. Paredit's commands change the tree explicitly and keep
parentheses balanced by construction, whatever the layout, `geb-fmt`
restoring the layout after them. Parinfer infers while one types, and
depends on layout: Indent Mode infers parentheses from indentation, so it
changes the tree by design and is an operation of editing, never a
formatter; Paren Mode infers indentation from parentheses and keeps the
tree. Either serves the same Geb source: the authoring profile uses no
brackets or braces, whose display hints and transport encoding are never
written by hand, and its strings are those parinfer reads, delimited by
double quotes with backslash escapes; the formatter's output is a fixed
point of both modes.

The editor is a `geb` language, a declarative extension of a manifest, a
language configuration and a TextMate grammar of some fifteen lines, with
Mike's Paredit configured for it as the structural editor (decided;
[Decisions](#decisions)). Parinfer is optional: its extensions fix their
languages and are unmaintained, so it enters, if wanted, through the
`geb` extension calling the `parinfer` library's `parenMode` or
`smartMode` on formatted files. `geb-fmt` is the formatter; a test in
continuous integration, `parenMode(x).text === x && indentMode(x).text ===
x` at a pinned parinfer, keeps its output usable under parinfer. For the legacy
syntax until the extension exists, associating `*.geb` with `scheme` (`"files.associations":
{"*.geb": "scheme"}`), with `sjhuangx.vscode-scheme` for a grammar and
language configuration, serves Mike's Paredit or `ailisp.strict-paredit`,
sound because atoms avoid the characters Scheme treats specially.

Before an extension is the supported default, it passes a fixture of the
profile: nested bindings, parentheses in comments, parentheses and
semicolons in quoted atoms, escaped quotes, Unicode names, input with
CRLF, and incomplete syntax. Navigation, selection, wrap, slurp, barf and
undo are tested in VS Code; formatting is tested by comparing the parsed
documents, annotations included, before and after, and structural edits by
their intended change of the tree with the checker run again. An editor's
recognition of other brackets or reader macros never defines Geb syntax.
Formatting on save, through `pucelle.run-on-save` calling `geb-fmt`, stays
off until the fixture passes.

### Tree-sitter and a language server

Tree-sitter is an incremental concrete-syntax parser that recovers from
errors ([introduction](https://tree-sitter.github.io/tree-sitter/)); it
helps selection and incomplete buffers independently of a language
server. VS Code offers no user-extensible tree-sitter highlighting
(experimental grammars for a few built-in languages only;
[vscode#50140](https://github.com/microsoft/vscode/issues/50140) is open);
[tree-sitter-vscode](https://github.com/AlecGhost/tree-sitter-vscode)
highlights with a supplied grammar through semantic tokens, and Neovim,
Helix, Zed and Emacs 29 use tree-sitter natively. A grammar for Geb is
derived from the same profile when those services need it, from
tree-sitter-scheme (MIT) as a base, and its recovery from errors never
supplies trusted input to the compiler. Nothing is needed now.

Diagnostics come before a language server:
[efm-langserver](https://github.com/mattn/efm-langserver) turns a checker
on the command line into diagnostics, with a generic client for VS Code,
and the checker to run is `Geb.Kernel.diagnose`, which names the first
failing definition, applied after the stage-0 expansion for the datatype
language. A language service then needs source spans and structured
diagnostics, lookup of definitions, inferred and expected types, and the
obligations of holes
([language-server guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide)).
The protocol transports those services between the checker and the
editor; it does not store or rebuild annotations. The existing checker
serves behind it; the server tracks versions of buffers, cancels stale
checks, and translates offsets of bytes into the position encoding the
editor negotiates, which reliable diagnostics after Unicode edits require.
Diagnostics with locations need a map from vertices to spans, a derived
annotation, and a checker that reports the failing vertex; the trusted
checker stays as it is, and the locating checker is a separate, untrusted
function.

### Typed holes

The first step is implemented.
[Hole.lean](../Geb/Prototypes/Kernel/Hole.lean) treats a sketch with one
hole of type `A` in context `Γ` as a kernel term in `A :: Γ`, the
innermost free variable standing for the hole, its occurrences under
binders included, and a filling as a term of type `A` in `Γ`:

```text
sketch : A :: Γ ⊢ B
filling : Γ ⊢ A
subst filling sketch : Γ ⊢ B
```

In the cartesian interpretation the sketch is a map `A × Γ → B`, the
filling a map `Γ → A`, and filling composes the sketch with
`⟨filling, id⟩ : Γ → A × Γ`: ordinary substitution, whose denotation is the
kernel's `infer_subst`. `fillHole` checks the expected type, the filling
and the sketch before substituting; `infer_fillHole` gives the type and
denotation of every accepted result, and `fillHole_of_infer` accepts every
valid input. The [kernel examples](../GebTests/Prototypes/Kernel.lean)
cover capture avoidance, repeated occurrences, and rejection of wrong
types, variables escaping their scope, invalid sketches and malformed
expected types. No slice or presheaf construction is needed for this
operation.

The literature for the richer interface:

- A hole of type `A` in a context `Γ` is a metavariable `u :: A[Γ]`
  occurring as `clo(u, id_Γ)` [NanevskiPfenningPientka2008]. Their Theorem
  4.6 translates such a metavariable into an ordinary variable of type
  `B₁ → … → Bₘ → A`, instantiation being substitution followed by β:
  holes are lambda-lifted variables, of which `fillHole` is the case of one
  hole, and in a cartesian closed category a term with a hole is a
  morphism out of the exponential `[Γ ⇒ A]`, by functional completeness
  [LambekScott1986].
- Hazelnut studies typed editing states, incomplete terms included
  [OmarVoyseyHiltonAldrichHammer2017]; Hazelnut Live assigns a hole its
  type in checking mode (rule EAEHole), and filling commutes with
  evaluation (Theorems 4.1 and 4.2) [OmarVoyseyChughHammer2019].
- The free Σ-monoid over presheaves on contexts characterizes
  metavariables, metasubstitution being the monad's bind [FioreHur2010]
  [FioreSzamozvancev2022].
- An Isabelle proof state with subgoals `ψ₁ … ψₙ` is the theorem
  `[ψ₁, …, ψₙ] ⇒ C`, the subgoals lifted over their parameters, and admits
  nothing [Paulson1989], unlike an axiom such as Lean's `sorryAx`.

These are references for the interface; their calculi need not enter
Geb's trusted logic.

Holes in programs, the next layer:

- Holes are forms `(hole name)`, written `?name` in the authoring profile
  ([Tokens](#tokens-numerals-and-editions)). The reader takes them as
  variables of the free monad of the definition, the directions of
  [definitions.md](definitions.md), so that
  filling is `link`, the Kleisli composition the definitions prototype
  proves associative.
- Each hole has an identity, a declaring context, an expected type and
  its occurrences in the source; repeated uses of a named hole share one
  obligation, and unrelated holes of one type do not. Uses in contexts
  other than the declaring one carry explicit substitutions from it, the
  closures of [NanevskiPfenningPientka2008].
- Expected types come from bidirectional checking, with first-order
  unification of simple types, which is decidable; people fill holes, so
  no higher-order unification arises. An initial implementation may
  require explicit types and decline to evaluate through holes; inference
  of missing types and live evaluation are extensions.
- Each hole is reported with its context, the names of its binders taken
  from the document, and its type. The trusted checker is unchanged: a
  program with holes checks exactly when its lambda-lifting does.
- A slice `Set/(Ctx × Ty)` is the bookkeeping; presheaves on contexts are
  needed only for metasubstitution capturing ambient variables or for
  first-class contextual types, neither of which is wanted.

Holes in proofs: a leaf `hole` carries an open sequent `Γ_h | Φ_h ⊢ ψ_h`;
the checker returns the conclusion with the list of open obligations and
certifies `(⋀_h ∀Γ_h. (⋀Φ_h ⇒ ψ_h)) ⊢ goal`, sound in every topos since it
uses intuitionistic `∀` and `⇒` alone. Filling is grafting, the bind of the
free monad of derivation trees. Only a closed derivation is accepted as
the original theorem; a sketch is state of the editor, not an axiom or a
completed program.

The stronger checkers are decided ([Decisions](#decisions)), and the
bootstrap requires two. The first is the Bootstrap chapter's checker with
a step of conversion to a normal form under named rules, supported further
by [Canonical](#canonical)'s measurements, with the evaluation of
primitives at literals as a family of its rules; the chapter's measurement
of derivation nodes by rule selects the rules it carries. The second is
the checker of holes, admitted beside the first rather than beside the
base checker: its certificates are
the conversion checker's with leaves for holes, its translation targets the
conversion checker, and soundness chains from holes to conversion to the
base, as Milawa's levels layer. Its conclusions are conditional, the
obligations of the holes implying the goal, which the base checker can
state, so admission applies to it as to any checker. Admitting a checker of
open sketches is not admitting their unresolved conclusions. It waits on
the metalogic's prover in Geb. The chapter's third candidate, the checker
of shared certificates, becomes a requirement only if measurement of
checking or storing cached certificates calls for it.

The checker of holes in programs is written now, in Lean, in the
suspending form (decided; [Decisions](#decisions)). A checker written as
Canonical-min's is, suspending at unassigned metavariables, reports each
hole's goal as the constraints suspended on it, so the report of holes and
the search that fills them share one implementation
([Canonical](#canonical)). Canonical-min keeps suspended work as closures
of Lean in a continuation monad, through `partial` functions; the
repository's rules admit no function calling itself, so the checker keeps
it as explicit finite work items, each carrying its context, its
substitution and the check that remains, resumes those an assignment
affects, and runs within a natural-number budget, driven by recursors.
That is the form a checker written in Geb needs, so it is transcribed into
Geb later and proved in Lean to agree, by the method of the metalogic's
checker. It extends `fillHole` from one hole to many, and leaves
`Geb.Kernel.infer`, the trusted checker, unchanged: a program with holes
checks exactly when its lambda-lifting does.

### Synthesis and certificates

The obligation of a hole is the interface to synthesis. A request carries
the frozen dependencies, the profile, the context, the target type or
proposition, the permitted grammar, examples and a budget of resources; a
result carries a candidate and, when a semantic property is claimed, its
certificate, with the revision of its input, so that it is not applied
silently to another hole. Failure or exhaustion of the budget refutes
nothing.

The target is explicit. Inhabiting a computational type such as
`Tree → Tree` specifies no behavior, so a program and a derivation of its
specification are searched together, sharing unknowns. A derivation of an
internal existential statement is not an executable witness: a topos
interprets existential quantification through images, without sections
of every epimorphism
([Borceux, *Some flavours of topos theory*, §§ 3.5, 4.4–4.5](https://www.uclouvain.be/system/files/uclouvain_assetmanager/groups/cms-editors-irmp/Lecture%20Notes.pdf)),
and a broader claim of extraction needs its own theorem. For unique
existence the repository proves the property of descriptions in
[Internal/Connectives.lean](../Geb/Prototypes/FreeTopos/Internal/Connectives.lean).
When a program is requested, a term of the executable fragment is
required.

In order of availability:

1. Lookup of matching local terms, introduction of constructors,
   application, rewriting by named theorems and bounded enumeration, with
   the prover as the producer of certificates: these make explicit typed
   holes useful without a new dependency.
2. A typed enumerator beside
   [Geb/Prototypes/FreeTopos/Prover/](../Geb/Prototypes/FreeTopos/Prover.lean),
   recursing only through `iter`, `fold`, `para` and `foldr`, so that
   totality is given. The universal property of the fold turns the
   synthesis of a recursive function from examples into the synthesis of
   its non-recursive step [Hutton1999] [FeserChaudhuriDillig2015]
   [OseraZdancewic2015]; candidates are pruned by observational
   equivalence and by evaluating partial candidates, the suspension of
   [Canonical](#canonical) supplying the latter. A certificate is the
   kernel term with its examples, checked by typing and evaluation, or,
   against a specification, a derivation from the prover's normalization
   and induction.
3. Search over the prover's choices, with equality saturation
   [WillseyNandiWangFlattTatlockPanchekha2021] whose explanations become
   the prover's certificates of rewriting, and refinement in the manner of
   [Canonical](#canonical) for choices of induction, motive and lemma.
4. SMT and syntax-guided synthesis for fragments with suitable encodings.
   Z3 already proposes decorations in the
   [elementary-affine prototype](../scripts/eal/eal.py), validated in Geb;
   cvc5's SyGuS interface also restricts candidates by a grammar
   ([example](https://cvc5.github.io/docs/latest/examples/sygus-fun.html),
   [SyGuS 2.1](https://arxiv.org/abs/2312.06001)). An SMT proof is not a Geb
   proof: its theory, Boolean reasoning and encoding must be related to the
   constructive metalogic, and a proof of unsatisfiability of the negated
   goal in a classical encoding yields constructively only a doubly
   negated conclusion. A first integration takes candidates checked by
   Geb's rules, or a fragment with a proved translation of certificates,
   and a report of no solution is never trusted.
5. Shared enumeration in the manner of SupGen.

SupGen's mechanism, from its two
[gists](https://gist.github.com/VictorTaelin/7fe49a99ebca42e5721aa1a3bb32e278)
and the public sources of [HVM4](https://github.com/HigherOrderCO/HVM4):
given a type, helper functions and equations between inputs and outputs,
the candidates form one term with a labelled superposition at each
choice; the interaction rules for applying and duplicating superpositions
share every computation independent of a choice; failed tests erase
branches; and a breadth-first collapse reads the survivors back. This is
pull-tabbing [Antoy2011] with the pruning of partial candidates of Lazy
SmallCheck [RuncimanNaylorLindblad2008], shared under optimal reduction.
SupGen's source is not published and HVM4 has no licence; Bend 2, launched
without it, states that it has no tactics or proof search. Its reported
speeds are not reproduced independently, and its programs recurse through
`Y`, so they need not be total. Material for a bounded experiment exists:
[HVM3](https://github.com/HigherOrderCO/HVM3)'s
[enumerator of affine λ-terms](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_lam_smart.hvm),
which bounds the depth of binding and the arity of application, and its
[type-directed enumerator](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_coc_smart.hvm),
both needing adaptation of their discipline of contexts and grammar of
candidates to Geb; and the
[SupVM gist](https://gist.github.com/VictorTaelin/7ae3d262e4d0b80a4e8817a80f976a68),
a small evaluator in TypeScript for a stated subset of HVM, representing
correlated labelled choices by a map, which is neither a specification nor
a verification of HVM. Superposition is a representation of search, not a
new constructor of the accepted language; the decoded result passes Geb's
checker whatever found it. Stage 4 of the interaction-net arm of the
Bootstrap chapter, superpositions for searching certificates, is where it
would enter, after typed and shared enumeration are compared on one finite
grammar and set of obligations, measuring generation, checking, size of
certificates, time and peak memory together.

Constraint pruning and sharing address different costs and may later be
combined. None of these is a prerequisite for preserving source across
revisions of the bootstrap; synthesis produces source and constrains the
format through holes only.

### Canonical

Canonical is a solver for type inhabitation in dependent type theory
[NormanAvigad2025].

- Its format is that of the Logical Framework [HarperHonsellPlotkin1993]
  without universes, with let definitions carrying reduction rules.
- Every term is β-normal and η-long, with one constructor,
  `λ x̄. let ȳ := M̄. f Ā`, and the type of a symbol determines its arity.
- A search refines one metavariable at a time. It chooses a head from the
  metavariable's local context and creates fresh metavariables for the
  head's arguments, all at once, so that they may be refined in any order
  and a later argument, a proof for instance, can constrain an earlier
  one, the witness it is about.
- Terms carry explicit substitutions, so an equation between partial
  terms is found violated as soon as its head symbols differ, and the
  branch is abandoned.
- Metavariables with a rigid equation are refined first, as unit
  propagation in SAT.
- Iterative deepening bounds a measure it calls entropy, estimated from
  statistics of earlier refinements, and branches are searched in
  parallel.
- The algorithm is Dowek's complete method [Dowek1993] with this
  representation.
- On the Natural Number Game it proves 62 of 74 statements in 51 seconds
  in all, against 27 for Aesop and 45 for Duper, with shorter proofs.
- Its future work names forward reasoning, the invention of lemmas and
  tactics as absent. Canonical produces cut-free proofs.

Canonical-min [NormanAvigad2026] is a reference implementation in 185
lines of Lean ([repository](https://github.com/chasenorman/Canonical-min),
cited here at revision `72a24f13ec2e6ff3150e609cb5edbc70ef59a236`).

- Its type checker for dependent type theory runs in a continuation
  monad. Meeting an unassigned metavariable, the checker stores the rest
  of the check as a constraint on that metavariable, and continues the
  independent checks of other arguments (`judgment`); assigning the
  metavariable resumes it.
- The search is iterative deepening over assignments of heads, favoring
  rigid constraints and otherwise later arguments, and raising both a
  bound on the size of terms and a heuristic budget.
- On DTTBench, 31 problems from Lean's library needing β-reduction only,
  with a timeout of 60 seconds, it solves 31. Twelf solves 8, sauto 6 and
  Mimer 2.
- Its search is written with `partial` functions, so being Lean source
  proves neither soundness nor completeness of the search; and its tactic
  wrapper imports Canonical itself for preparing premises, translation and
  reconstruction of proofs.

Canonical is available under the MIT licence: the solver in Rust with the
Lean tactic ([Canonical](https://github.com/chasenorman/Canonical),
[CanonicalLean](https://github.com/chasenorman/CanonicalLean)), released
for each Lean version with precompiled libraries for three platforms, the
latest for Lean v4.34.0 on 2026-09-27. Outside Lean it reads a problem in
an undocumented JSON form. A mode for program synthesis, in which an
equation stuck on the major argument of a recursor counts as stuck rather
than violated (§ 3.3.1 of the paper), is absent from the released tactic.
A stuck check is not a failed one — `natRec z s ?n = z` becomes true when
`?n` is zero — so a search claiming completeness over its grammar keeps
stuck branches that remain viable. The paper's encoding of Lean (§ 4)
erases universes; it is not a foundation for Geb, whose final checker
stays the boundary of acceptance.

Three properties of Geb fit it.

- A checker of Geb is a fold over a tree of rule applications, that is,
  over the terms of a signature of the Logical Framework: judgements are
  families of types indexed by the terms they relate, and rules are
  constants. An inhabitant of a judgement is, after decoding, a
  certificate for Geb's trusted checker to check again, and a wrong
  encoding costs completeness, never soundness.
- Canonical's metavariables with local contexts are the metavariables of
  contextual modal type theory, and a checker written as Canonical-min's
  is reports each hole's goal as the constraints suspended on it: the
  report of holes and the search that fills them are one program
  ([Typed holes](#typed-holes)).
- Canonical accepts reduction rules. Given the kernel's computation rules
  (β, projections, the folds at constructors) as rules, an equation that
  holds by computation holds definitionally, and the search is left the
  structural choices of induction, motive and lemma, which complements
  the normalizing prover.

Experiments, on one machine, with Canonical and Canonical-min at Lean
v4.34.0, the goals stated in Lean as Canonical-min's DTTBench states them,
the signature as hypotheses:

| Goal | Encoding | Canonical | Canonical-min |
| --- | --- | --- | --- |
| `foldr cons nil xs = xs` | rules of Gödel's T as axioms | found, about 1 s | not found in 60 s |
| uniqueness of the right fold | the same, with symmetry and congruence of an argument | found, about 100 s | not run |
| uniqueness of the right fold | equality by reflexivity and a Leibniz eliminator | not found in 180 s | not run |
| associativity of appending | rules of Gödel's T as axioms | not found in 60 s | not run |
| the three theorems above | Lean's `List`, the fold's equations as reduction rules | all found, 11 s in all | not run |
| length and sum of `List Nat` from three examples each | Lean's `List` and `Nat` | not found in 30 s and 60 s | not run |

The machine has 16 threads (AMD Ryzen AI 9 HX 370); Canonical used all of
them. Canonical-min was measured at the revision above, Canonical at tag
`v4.34.0` of CanonicalLean. To reproduce: the manifest of Canonical-min
pins an untagged revision of CanonicalLean, for which no release archive
exists, so the revision is replaced by the tag's; and the tactic's native
library is loaded when a goal is built as a module of the package by
`lake build`, not by `lake env lean`.

The signature of the rules of Gödel's T over lists, in higher-order
abstract syntax, with nothing computing definitionally, is:

```lean
(Ty : Type) → (Tm : (A : Ty) → Type) →
(Eq : (A : Ty) → (a : Tm A) → (b : Tm A) → Type) →
(trans : (A : Ty) → (a b c : Tm A) → Eq A a b → Eq A b c → Eq A a c) →
(List : (A : Ty) → Ty) → (nil : (A : Ty) → Tm (List A)) →
(cons : (A : Ty) → Tm A → Tm (List A) → Tm (List A)) →
(congCons : (A : Ty) → (x : Tm A) → (xs ys : Tm (List A)) →
  Eq (List A) xs ys → Eq (List A) (cons A x xs) (cons A x ys)) →
(foldr : (A B : Ty) → Tm B → (Tm A → Tm B → Tm B) → Tm (List A) → Tm B) →
(foldrNil : (A B : Ty) → (z : Tm B) → (s : Tm A → Tm B → Tm B) →
  Eq B (foldr A B z s (nil A)) z) →
(foldrCons : (A B : Ty) → (z : Tm B) → (s : Tm A → Tm B → Tm B) →
  (x : Tm A) → (xs : Tm (List A)) →
  Eq B (foldr A B z s (cons A x xs)) (s x (foldr A B z s xs))) →
(indList : (A : Ty) → (P : Tm (List A) → Type) → P (nil A) →
  ((x : Tm A) → (xs : Tm (List A)) → P xs → P (cons A x xs)) →
  (xs : Tm (List A)) → P xs) → …
```

For the goal `Eq (List A) (foldr A (List A) (nil A) (λ x r. cons A x r) xs)
xs`, Canonical returns the following term, a derivation in these rules
(induction on the list, the fold's rules and congruence of `cons`), its
motive synthesized:

```lean
indList A (fun xs ↦ Eq (List A) (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs) xs)
  (foldrNil A (List A) (nil A) fun x r ↦ cons A x r)
  (fun x xs ih ↦
    trans (List A) (foldr A (List A) (nil A) (fun x r ↦ cons A x r) (cons A x xs))
      (cons A x (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs)) (cons A x xs)
      (foldrCons A (List A) (nil A) (fun x r ↦ cons A x r) x xs)
      (congCons A x (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs) xs ih))
  xs
```

The encoding is in higher-order abstract syntax, and Geb's checker of
Gödel's T works with de Bruijn contexts and hypotheses; the terms found
were not decoded into Geb certificates and checked, so they establish
which encodings search well, not a working route. Four conclusions follow
from the measurements, within their small number.

- With the rules as axioms, Canonical finds derivations of a few steps
  with a synthesized motive, and those that chain several equational
  steps take minutes or are not found, as its paper reports of
  equational problems. Explicit rules of congruence, which Geb's checkers
  have, served better than a Leibniz eliminator here.
- With the computation rules as reduction rules, the same theorems are
  found in seconds, the search being left the induction and its motive.
  This is the configuration of the first stronger checker the Bootstrap
  chapter names, a checker with a step of conversion to a normal form
  under named rules: a term found against reduction rules is a
  certificate of that checker, which reaches the metalogic's derivations
  through the translation that admits it. Canonical returns such proofs
  as `simp only` steps with the equations it rewrote by, which is the
  information that translation needs.
- Programs from examples are not found, the released tactic lacking the
  mode for synthesis; they remain the enumerator's.
- Canonical-min, without the heuristics and parallelism of the solver in
  Rust, did not find the shortest derivation in 60 s; it specifies the
  algorithm rather than serving as a solver.

The operations that transfer to Geb are three: each unknown has its
declaring context and an explicit substitution at each use, and a
candidate application is its head with all its argument holes; a check
needing an unassigned hole is suspended on it while independent checks
continue; and a step chooses a hole and a head, allocates the argument
holes together, resumes the checks waiting on that assignment, rejects
the branch when a constraint fails, and undoes its assignments and
constraints on backtracking. Two routes implement them:

| Route | Benefit | Work required |
| --- | --- | --- |
| Encode Geb's derivations as a signature for Canonical | Exercises an existing, parallel search at once | Specify the signature, scoping, substitution and decoding exactly; decode each found term into a Geb derivation and check it; a Lean proof of an analogous statement alone is insufficient |
| Implement refinement over Geb's terms and derivations | Uses the actual language and checker; a bounded search written in Geb survives the bootstrap | Contextual metavariables and suspended constraints; checking, branching and reduction adapted to partial syntax |

The second is the implementation meant to last, and the first serves
experiment. The Geb-native search starts from the finite grammar of
selected heads and proof rules for actual obligations; for logical goals
it searches for a Geb derivation of the sequent, and for computational
goals it shares the holes of a candidate term with the derivation of its
required property, which needs no dependent types in Geb's object
language. It reuses the
[internal-language prover](../Geb/Prototypes/FreeTopos/Internal/Prove.lean)
— scoped matching of theorems, normalization producing certificates,
function extensionality, case analysis and combinators of induction —
whose matcher handles supplied terms, suspension and shared unknowns being
additional work rather than an existing general unifier; normalization in
search uses justified computational equations and does not treat equality
in the metalogic as decidable by normalization. Where Canonical-min keeps
suspended work as closures of Lean, a first implementation in Geb keeps it
as explicit finite work items carrying contexts and substitutions, resumes
only those an assignment affects, and bounds search and reduction by a
natural number, returning unfinished state when the bound is spent, so
that each run is a total operation of System T that the host may repeat;
a heuristic entropy in floating point is not needed at first.

Its obligations are separate: checking every completed candidate gives
correctness of accepted results through the existing checker; correct
pruning also needs that a rejected partial state has no valid completion;
and completeness also needs coverage of the chosen grammar, correct
scoping and backtracking, and fair exploration as bounds grow. An
exhausted finite run establishes none of the global claims. The first
experiment compares refinement with typed enumeration on one finite
grammar, with composition, repeated holes under binders, a proof
constraining an earlier witness, and a fold stuck on an unknown
argument; it replays every certificate and records nodes searched,
reduction, time of checking and size of certificates; the search for
induction motives follows once the basic constraints work, the existing
combinators of induction serving meanwhile. It needs contextual holes
richer than `fillHole`.

Recommendations: nothing in the source format beyond the syntax of holes;
the checker of holes written to suspend, so that it serves as the search's
checker; and the Geb-native refinement as the lasting implementation.
Canonical is a dependency of the package for experiments throughout the
bootstrap (decided; [Decisions](#decisions)). It enters `lakefile.toml` at
tag `v4.34.0`, which was measured to build and run under the repository's
toolchain, and has no dependencies of its own. The experiments form a
library of their own that no module of `Geb`, `GebLang` or `GebTests`
imports, so a default build never fetches its solver library, and
committed experiments call the solver as a program — the tactic leaves
`sorry`, which committed code excludes — and check what they decode with
Geb's checkers, the first route above. `TODO.md` § Triggers records the
condition for removing it: everything done or planned with it written in
Geb, or writable in Geb by the Geb-native search.

### Tokens, numerals and editions

Identifiers are tokens of [RFC9804]: ASCII letters, digits and
`- . / _ : * + =`, not beginning with a digit (decided). Every identifier
of the present sources is one already. A name beyond ASCII is a quoted
atom, readable in the authoring profile, whose quoted strings admit UTF-8.
Names are compared byte for byte, and since no reader normalizes, a quoted
name not already in Unicode's normalization form C is rejected, so that
equal-looking names are equal.

Numerals, which no token spells, are bare runs of digits in the authoring
profile, unambiguous against the advanced grammar since a digit there
begins a length only when `:`, `"`, `#` or `|` follows it; the strict
printers write them quoted (`"0"`). The datatype language's `&`, not a
token character, is a token of the authoring profile, and the strict
printers write it `"&"` (both decided). A hole is the form `(hole name)`,
of tokens alone, in the document type and in every syntax, and the
authoring profile writes it `?name`, as a Lisp writes `'x` for
`(quote x)`: the profile's reader reads `?name` as the form, and its
printer writes a hole form of one argument as `?name`, deterministically,
so the retraction holds (decided). The form extends where the prefix
cannot: `(hole name T)` gives an expected type, which a first
implementation may require, and `(hole)` an anonymous hole. No atom prefix
is reserved, and the strict encodings need nothing of their own; `hole` is
a keyword that no definition may shadow, as the Bootstrap chapter requires
of the names its expansions use.

Record an edition per program in the manifest, as Racket's `#lang`, Rust's
editions and Go's `go` directive do. An edition fixes the reader, its rules
of resolution included, and the elaborator. An elaborator is a committed
image and the kernel is fixed, so an old edition's image runs unchanged.
Before the bootstrap completes, sources are converted to the current
edition rather than kept under old ones; editions preserve meaning across
revisions for code relied on beyond the bootstrap.
Mixing editions in one program needs an interface between the
environments of elaborators, such as declarations of constructors; that
is its cost.

### Stability of elaboration

The higher-level source is kept beside its resolved core, the rules of
expansion and name resolution are versioned by edition, and generated
names are hygienic ([Files](#files-assembly-and-the-host-boundary)).
Commit, for each program, the elaborated definitions that
`lake exe geb-defs` writes, regenerate them in continuous integration and
compare them: any change of expansion or resolution that alters existing
code is then detected, before digests exist, as `bootstrap/compiler.img`
detects it for the compiler alone. State the encoding of the datatype
language in the manual as part of the first edition. A specification of
the expansion in Lean, as the checkers have, would free its meaning from
one Geb program; that is larger and can follow.

### Proof scripts and certificates

Before many proofs are written in Geb, fix the durable artifact. Scripts
are the source. A certificate is kept with its statement, theory and
profile, dependencies and format, and replayed, or translated by a
certified translator, when rules or encodings change. Certificates,
derivations under the fixed rule set, are cached artifacts of the build,
keyed by the statement and the elaborated definitions it cites, and a
script that fails after a change of the prover falls back to its cached
certificate while it is repaired. The complete proofs about the compiler's
components have from 600000 to 1240000 nodes, so the cache holds the form
of shared certificates. The metalogic has no surface syntax for statements
in Geb text yet, and it will need its own retraction at the level of
documents.

### Comment conventions

The sources' convention is whole-line comments, a block before a form
documenting it and a block followed by an empty line being prose. It is
recommended as it stands; the graded semicolons of Common Lisp's style
(the HyperSpec, section 2.4.4.2) serve if headings and documentation must
be told apart without empty lines. The formatter reads a comment after
code on the same line and moves it before the next item. A comment as the
last element of a list is excluded, being the one construct parinfer
cannot lay out stably.

### N-ary chains in the surface language

The kernel's conditional and `let` are binary, so chains of tests and of
bindings nest, and under a layout parinfer admits, nesting is
indentation. The chain of tests of rules in
[bootstrap/goedel-t/equations.geb](../bootstrap/goedel-t/equations.geb)
gives the only lines the formatter cannot keep within 100 columns, and the
written files' flat chains are what parinfer's Indent Mode restructures.
Forms `let*`, of several bindings, and `cond`, of several guarded
branches, expanded by the reader as the lists of binders of `lam` are,
remove both; they are widenings, and precede long chains.

### Further requirements before substantial authoring

| Requirement | Minimum contract |
| --- | --- |
| Schema and feature versions | Syntax, core, annotations, certificates and semantic profile are identified separately; an unsupported mandatory feature is rejected and an optional field kept opaque. |
| Persistent data | Serialized values, tags of datatype constructors, examples and saved inputs of programs are versioned interfaces; migrating code does not migrate values stored outside it. |
| Library behavior | Dependencies are frozen; an implementation is replaced only with proved equality for the observations its interface permits, or kept under its old identity ([contract](#the-compatibility-contract)). |
| Verification boundary | Which steps of parsing, elaboration, serialization, code generation and host execution are proved and which tested is stated, and correctness is carried through the whole path that runs a program. |
| Reproducible builds | Source, the closure of dependencies and the compiler profile are kept; the identities of document, checked core and generated artifacts are distinct; a corpus of previously accepted programs is kept. |
| Diagnostics | A structured result of success or error with its source occurrence; an empty output of the compiler is not an interface for developers. |
| Editing and recovery | Incomplete documents, obligations of holes and unattached annotations are saved; drafts are distinguished from accepted programs; updates of several artifacts are atomic. |
| Performance and limits | Exhaustion of resources is distinct from falsity and from ill-typing; representative operations of editing, checking and compiling are measured; implementations may improve without promising equal cost. |
| Reflection | Representations of code are distinguished from ordinary data; which structural observations are stable, and how quoted schemas migrate, is stated. |
| Host protocols | Contracts of bytes, framing, errors and types of entry points are fixed independently of files, the width of machine words and the names of backends ([host boundary](#files-assembly-and-the-host-boundary)). |

### Scale

The Bootstrap chapter's section on improvements lists the limits that
more Geb code meets:

- the Geb reader's stack in proportion to a program's length;
- about 480 bytes of memory per byte of input;
- the rebuilding of every test module on a change of a Geb source;
- a Geb compiler that names no failing definition.

Content identity also gives incremental compilation, a cache per
definition keyed by digest, which is a reason to take it early, though
not one of format.

## A sequence and its acceptance

Before most Geb code is written; the steps that change
`bootstrap/reader.geb` and the committed images follow other work on the
reader:

| Step | Acceptance |
| --- | --- |
| Adopt the document reader and the formatter | `bootstrap/` formatted in one mechanical change with images and emitted Lean unchanged, as measured above; `geb-fmt --check` and the test of parinfer's fixed points in continuous integration |
| Reject duplicate and ambiguous names | both readers reject duplicates and accept every present source unchanged |
| The syntaxes of RFC 9804 and the authoring profile, with the importer | the four retractions proved over one document type; the bootstrap sources convert, and compile to the same checked bundles |
| Manifests with editions; the record of elaborated definitions | the build and tests read manifests; the regenerated record equals the committed one |
| A durable document with versioned profiles | declaration and binder names, prose, examples, links and unknown optional fields survive reading, printing and conversion |
| Hygienic elaboration, explicit assembly, diagnostics | shadowing a primitive cannot alter generated operations; imports resolve deterministically; failures name a source occurrence and preserve existing outputs |
| Markup and conventions of comments; documentation | one Geb module renders prose, a checked example and a link through Verso; editing only its documentation leaves the core identity unchanged |
| The `geb` language with Mike's Paredit | the pinned extensions pass the profile's fixture |

Early in writing, alongside the first substantial module where it helps:
namespaces; `let*` and `cond`; quoted atoms; the syntax of holes, the
suspending checker of holes in programs and the display of their
obligations; diagnostics with locations through
efm-langserver; literate pages generated from documents; and the typed
enumerator. When their consumers exist: digests and the store, `attach`
and hover text, a language server, tree-sitter, holes in proofs, the cache
of certificates, the export to canonical S-expressions, and the
Geb-native refinement search. The library then written in Geb drives
content storage, richer language services, adapters to solvers and
optimization of the runtime; none of them may discard the document,
binding or dependency information already kept.

## Decisions

- 2026-09-30: the markup of comments and documentation is Verso's, over
  Markdown, with `{name}` for Lean constants and a role `{geb}` for Geb
  definitions ([Documentation](#documentation-through-verso)).
- 2026-09-30: documentation renders as literate pages generated from Geb
  source, not as docstrings in the emitted Lean
  ([Documentation](#documentation-through-verso)).
- 2026-09-30: the editor is a `geb` language with Mike's Paredit as the
  structural editor; parinfer is optional, through the `geb` extension
  ([Structural editing](#structural-editing-and-parinfer)).
- 2026-09-30: Canonical is a dependency of the package for experiments,
  removed once everything done or planned with it is written, or
  writable, in Geb ([Canonical](#canonical); `TODO.md` § Triggers).
- 2026-09-30: the bootstrap requires two stronger checkers: first the
  conversion step, with the evaluation of primitives at literals as a
  family of its rules, and second the checker of holes, admitted beside
  the first ([Typed holes](#typed-holes)). The checker of shared
  certificates becomes a requirement only if measurement of checking or
  storing cached certificates calls for it, and is otherwise an early item
  after the bootstrap (`TODO.md` § Triggers).
- 2026-09-30: the checker of holes in programs is written now, in Lean,
  in the suspending form with explicit work items and a budget, to be
  transcribed into Geb and proved to agree ([Typed holes](#typed-holes)).
- 2026-09-30: source is written in the syntaxes of [RFC9804]: its canonical
  and transport encodings, its advanced encoding, and a Geb authoring
  profile extending the advanced encoding by line comments and by UTF-8
  and line breaks in quoted strings, all reading into one document type
  and sharing code; identifiers are its tokens
  ([Readable and canonical S-expressions](#readable-and-canonical-s-expressions)).
- 2026-09-30: in the authoring profile, numerals are bare runs of digits
  and `&` is a token; the strict printers write `"0"` and `"&"`
  ([Tokens](#tokens-numerals-and-editions)).
- 2026-09-30: a hole is the form `(hole name)`, with `(hole name T)` for
  an expected type; the authoring profile writes a one-argument hole as
  `?name` ([Tokens](#tokens-numerals-and-editions)).
- 2026-09-30: a namespace is a reopenable block form `(namespace X …)`,
  independent of files, with `(open Y)` scoped to its block
  ([Namespaces](#namespaces-and-name-uniqueness)).
- 2026-09-30: the prover's public contract is any checked certificate of
  the statement, behind an abstraction clients may check or cite but not
  inspect; exact agreement with the Lean prover is a milestone of the
  bootstrap, not a promise to clients
  ([The compatibility contract](#the-compatibility-contract)).
- 2026-09-30: before substantial authoring come export lists in namespace
  blocks, a block without one exporting nothing; the datatype language's
  completion, datatype names as types with the static check; and type
  parameters checked opaquely, abstraction being parameterization over
  interfaces rather than a syntactic mark
  ([Namespaces](#namespaces-and-name-uniqueness),
  [Datatypes](#datatypes-type-parameters-and-interfaces)).
- 2026-09-30: until the bootstrap completes, no source is kept unchanged
  for its own sake: whatever is preferable is adopted everywhere, and the
  languages admit exactly what the mathematics states, without implicit
  coercions ([The compatibility contract](#the-compatibility-contract)).
- 2026-09-30: the datatype language's completion precedes substantial
  authoring entire: datatype names as exact types checked at every use,
  explicit representation and decoding maps, generated recognizers,
  opaque type parameters, and the soundness of the typing, proved with the
  prover in Geb ([Datatypes](#datatypes-type-parameters-and-interfaces)).
- 2026-09-30: the layout policy is the prototype's: a list that does not
  fit breaks every remaining element onto its own line, none hung on the
  current line ([Source documents](#source-documents-and-a-verified-formatter)).
- 2026-09-30: type parameters are sorts through the bootstrap; after it,
  among the first work written in Geb, category theory is internalized and
  type parameters become parameters over internal universes defined from
  the topos's structure, the datatypes' codes in `2^T` and the subobjects'
  in `Ω^T`, each interpreted by membership; no universe interprets every
  object ([Datatypes](#datatypes-type-parameters-and-interfaces)).

## Open decisions

None at present.

## Sources

Works of the literature are cited by their keys in
[references.bib](references.bib). Software and documentation are linked
where cited; beyond those:

- [parinfer.js](https://github.com/parinfer/parinfer.js), npm package
  3.13.1;
- [strict-paredit](https://github.com/ailisp/strict-paredit-vscode);
- [rust-analyzer's syntax trees](https://github.com/rust-lang/rust-analyzer/blob/master/docs/book/src/contributing/syntax.md);
- [rewrite-clj](https://github.com/clj-commons/rewrite-clj);
- the SupGen gists
  [60d3bc72](https://gist.github.com/VictorTaelin/60d3bc72fb4edefecd42095e44138b41)
  and
  [7fe49a99](https://gist.github.com/VictorTaelin/7fe49a99ebca42e5721aa1a3bb32e278);
- the paper's PDF,
  [Canonical for Automated Theorem Proving in Lean](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.14/LIPIcs.ITP.2025.14.pdf),
  and Chase Norman's talks on Canonical
  ([video 1](https://www.youtube.com/watch?v=y6p0hHkabXs),
  [video 2](https://www.youtube.com/watch?v=Me7WFEvoksw)).

Not verified: whether `emeraldwalk.RunOnSave` can run commands of VS Code;
whether clojure-lsp reports errors on `.geb` files; and a statement in the
literature that a derivation with open subgoals is a derivation under the
hypotheses `∀Γ_h. φ_h` in a topos's internal language, which follows from
the rules introducing `⇒` and `∀` but was not located.
