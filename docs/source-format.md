# Settling Geb's source format

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [The criterion](#the-criterion)
- [What the existing guarantees do not cover](#what-the-existing-guarantees-do-not-cover)
- [The state of the repository](#the-state-of-the-repository)
- [Source documents and a verified formatter](#source-documents-and-a-verified-formatter)
- [The considerations](#the-considerations)
  - [Readable and canonical S-expressions](#readable-and-canonical-s-expressions)
  - [Out-of-band data and editor support](#out-of-band-data-and-editor-support)
  - [Hashes and multihash references](#hashes-and-multihash-references)
  - [Files and references across them](#files-and-references-across-them)
  - [Free-monad and cofree-comonad addressing](#free-monad-and-cofree-comonad-addressing)
  - [Documentation through Verso](#documentation-through-verso)
  - [Paredit, parinfer and coloured parentheses](#paredit-parinfer-and-coloured-parentheses)
  - [Tree-sitter and a language server](#tree-sitter-and-a-language-server)
  - [Typed holes](#typed-holes)
  - [Program and proof synthesis](#program-and-proof-synthesis)
  - [Canonical](#canonical)
  - [Grammar narrowing and editions](#grammar-narrowing-and-editions)
  - [Namespaces and name uniqueness](#namespaces-and-name-uniqueness)
  - [Stability of elaboration](#stability-of-elaboration)
  - [Proof scripts and certificates](#proof-scripts-and-certificates)
  - [Comment conventions](#comment-conventions)
  - [N-ary chains in the surface language](#n-ary-chains-in-the-surface-language)
  - [Scale](#scale)
- [A sequence](#a-sequence)
- [Open decisions](#open-decisions)
- [Sources](#sources)

<!-- END doctoc -->

This report states what must be fixed about Geb's source format before
most of Geb's code is written in Geb, so that every later change of
format is a mechanical, provable translation. It surveys the concrete
syntax, comments and documentation, names and files, content identity,
editor tooling, typed holes and synthesis, and records the prototype
that settles the first of them:
[Geb/Prototypes/Kernel/Document.lean](../Geb/Prototypes/Kernel/Document.lean),
with its tests and the formatter `lake exe geb-fmt`
([GebFmtMain.lean](../GebFmtMain.lean)).

Status: report of 2026-09-29. Measurements of the repository refer to
`main` at commit `b3aa139a`; those of external tools name the version
measured. The recommendations are proposals; Section
[Open decisions](#open-decisions) lists those that are the user's.

## Summary

A later change of format is a mechanical, provable translation exactly
when the source written now records every piece of information a person
supplies, and the reading of that source is fixed by a recorded version.
Whatever a program can compute from the source — digests, addresses, the
separation of comments from code, highlighting, rendered documentation,
reports of holes, synthesized terms — can be added at any later time
without touching what was written. The work to do first is therefore
small:

1. Read comments and empty lines as data. They are the only content a
   person writes that no later tool can recover, and reading them settles
   most of the questions of out-of-band data, documentation and
   formatting ([Source documents](#source-documents-and-a-verified-formatter)).
2. Narrow the grammar now, so that every later addition widens it:
   reserve ``" ' ` , # | [ ] { } \ @`` and restrict atoms to numerals and
   identifiers beginning with a letter
   ([Grammar narrowing](#grammar-narrowing-and-editions)). No file under
   `bootstrap/` is affected.
3. Make name resolution a function of recorded data: a manifest per
   program naming its files in order, rejection of duplicate names, and a
   namespace separator ([Files](#files-and-references-across-them),
   [Namespaces](#namespaces-and-name-uniqueness)).
4. Pin the elaborator as well as the syntax: an edition per program, and
   a committed record of each program's elaborated definitions compared
   in continuous integration
   ([Elaboration](#stability-of-elaboration)).
5. Fix the markup of comments, since cross-references cannot be added
   mechanically to prose written without them
   ([Documentation](#documentation-through-verso)).

Digests, the content store, vertex-keyed annotation tables, tree-sitter,
a language server, typed holes and synthesis are derived from the source
and can follow; each consideration below states its present obligation,
usually none or a reserved character.

## The criterion

Let `read_e : Text ⇀ D_e` be the reader of an edition `e` into its
document type `D_e`, and `print_e' : D_e' → Text` a printer of an edition
`e'` with `read_e' ∘ print_e' = id`. For an embedding `ι : D_e → D_e'`,
the migration `print_e' ∘ ι ∘ read_e` satisfies
`read_e' (migrate t) = ι (read_e t)` by the retraction law alone. Three
conditions make that theorem available:

- Completeness of `D_e`: whatever a person wrote that `D_e` omits is lost
  by every migration. [concrete-syntaxes.md](concrete-syntaxes.md)
  § The laws must be lifted to the annotated level states the same
  requirement.
- Determinism of `read_e` relative to recorded context: the migration
  replays the old reader, its resolution rules included, and whatever the
  reader consults, such as the order in which files are joined, is
  recorded.
- An embedding `ι`: every old document has an image in the new edition.
  Widening a grammar supplies `ι`; narrowing one does not.

Two consequences follow. Restrictions cost little before code exists and
much after, and extensions the reverse, so the grammar is made as narrow
as present code requires. And a feature may be deferred when its data is
a function of `D_e`.

## What the existing guarantees do not cover

Geb specifies no concrete syntax, only an abstract syntax with a
retraction to each concrete one, and it specifies its semantics by
universal properties. The first protects the kernel term; the second its
denotation. Four things lie outside both.

1. Content that is not a kernel term: comments, names of bound variables,
   abbreviations and layout. A retraction at the level of kernel terms
   prints `app (lam A b) e` where a person wrote `let` or `defn`, and loses
   numeral abbreviations such as `Label.app`, which the reader expands
   before resolution. The formatter's retraction therefore belongs at the
   level of S-expression documents; the retraction at the level of kernel
   terms, the printer for the kernel's readable syntax of the Bootstrap
   chapter, serves generated code and decompilation.
2. Elaboration. The datatype language is defined by a Geb program,
   [bootstrap/stage1/datatype.geb](../bootstrap/stage1/datatype.geb), not
   by a universal property, and its encoding (the constructor of position
   `i` as the node of label `i` over its fields, `&` taking the remaining
   children) is observable: sources use it directly, as
   [bootstrap/free-topos/base.geb](../bootstrap/free-topos/base.geb) does
   for optional trees. A revision of the expansion changes the meaning of
   existing source while every universal property still holds. Unison
   avoids the problem by storing elaborated terms and printing text from
   them; a text-first Geb needs editions and a record of elaboration
   ([Elaboration](#stability-of-elaboration)).
3. Proof scripts. A proposition of the metalogic keeps its meaning, but a
   tactic script is a program for one prover and changes meaning when the
   prover changes. The durable artifact is the certificate, checked by the
   fixed rule set ([Proof scripts](#proof-scripts-and-certificates)).
4. Organization: which definitions form a program, their order, files,
   sections and namespaces. It is recorded now in the source lists of
   [scripts/bootstrap.sh](../scripts/bootstrap.sh) and in the
   `include_str` definitions of the tests.

## The state of the repository

The facts below were measured at commit `b3aa139a`.

- Three S-expression readers exist, none a superset of another:
  - the kernel's reader, `Geb.Kernel.readSExps` in
    [Geb/Prototypes/Kernel/Reader.lean](../Geb/Prototypes/Kernel/Reader.lean),
    and its counterpart in Geb,
    [bootstrap/reader.geb](../bootstrap/reader.geb): an atom is any run
    of characters other than whitespace, parentheses and `;`, a `;`
    comment is discarded, and there are no strings;
  - [Geb/Prototypes/ReadableSExpr.lean](../Geb/Prototypes/ReadableSExpr.lean),
    rose trees over `Fin k` spelled as numerals;
  - [Geb/Prototypes/CanonicalSExpr.lean](../Geb/Prototypes/CanonicalSExpr.lean),
    the canonical form of [RFC9804] over the same trees.

  The second and third validate the retraction architecture; the
  bootstrap uses neither.
- The data model of the kernel's reader is that of [RFC9804]:
  `SExp := RoseTree (Option (List Char))`, atoms and lists.
  [concrete-syntaxes.md](concrete-syntaxes.md) § Readable S-expressions
  records why the readable form of [RFC9804], its advanced
  representation, was declined: a token cannot begin with a digit, so `0`
  would be written `"0"` or `1:0`.
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
- A program is a concatenation of files whose lists are kept in
  `scripts/bootstrap.sh` and the tests; dependencies between files are
  recorded in prose only ("Requires the prelude, the reader and the
  checker").
- The image keeps the names of definitions only; the Lean backend names
  variables by depth and writes no comments. The Bootstrap chapter lists
  the names of bound variables and comments as ready.
- Content identity is designed: the node-digest rule, the migration from
  positions to digests and the annotation tables keyed by vertex
  ([Bootstrap chapter](../manual/GebManual/Bootstrap.lean) § Definitions,
  references and identity; [definitions.md](definitions.md) § Content
  identity). The choice between BLAKE3 and SHA3-256 is open.

## Source documents and a verified formatter

[Geb/Prototypes/Kernel/Document.lean](../Geb/Prototypes/Kernel/Document.lean),
with
[GebTests/Prototypes/Kernel/Document.lean](../GebTests/Prototypes/Kernel/Document.lean)
and the executable `geb-fmt`, implements the document layer.

A document is a list of items, each a `RoseTree Lab` with
`Lab = {gap : Bool, kind : atom s | list | comment s}`. Comments are items
in document order, not annotations of the nodes after them: the design of
the lossless syntax trees of Roslyn and of rust-analyzer's rowan, and of
rewrite-clj, on which cljfmt and zprint are built. Reading attaches no
comment to a node; an attachment is a separate function of the document.
An empty line is a flag on the item after it, as gofmt and ormolu keep at
most one empty line between items.

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
| parinfer 3.13.1, Paren Mode and Indent Mode, on formatted files | no file changes |
| parinfer on the files as written | 16 files changed by Paren Mode, 15 by Indent Mode, and an Indent Mode error in `goedel-t/prove.geb` |
| Lines beyond 100 columns after formatting | 17, all comments in the chain of conditionals of `goedel-t/equations.geb` |

The layout policy (`planStep`, `planElem`) writes a list that fits on one
line; otherwise its elements fill the first line while they fit, the
parentheses that close after them included, and the rest begin lines
indented past the list's opening parenthesis, by two columns after an
atom at its head and by one otherwise. Its output meets parinfer's
invariant: each continuation line is indented beyond the innermost open
parenthesis and not beyond a parenthesis closed at the end of the line
before ([parinfer](https://shaunlebron.github.io/parinfer/#mathematical-foundation)).
The written files place a nested `let` or conditional at its parent's
indentation, which parinfer's Indent Mode reads as closing the parent.

The same cause produces the long lines: the kernel's binary conditional
and single-binding `let` make chains nest, and nesting is indentation
under any layout parinfer admits
([N-ary chains](#n-ary-chains-in-the-surface-language)).

The prototype leaves three things open. A list whose last element is a
comment prints its closing parenthesis at the start of a line, which
parinfer rejects; no file has one. The alphabet of atoms is the kernel
reader's, without quoted atoms. And the attachment of comments to
vertices, which hover text and a store need, is a fold over the document
not yet written.

## The considerations

### Readable and canonical S-expressions

[RFC9804] specifies a canonical encoding and an advanced encoding for
people. The readable S-expressions of this repository are not the
advanced encoding, which cannot write a numeral as a bare token and has
no `&`; they belong to the family of [R7RS] `<datum>`, [EDN] and
`sexplib`, and the kernel's syntax lies in that family already, every atom
of the sources being a numeral or an identifier of [R7RS] and [EDN].
Neither encoding of [RFC9804] carries information the present syntax
cannot: what they add are spellings over the same data model of octet
strings (quoted atoms, hexadecimal and base-64 atoms, display hints), so
a later translation into them is mechanical.

- Now: reserve the characters those spellings use
  ([Grammar narrowing](#grammar-narrowing-and-editions)).
- Later: an export of `SExp` to the canonical encoding, atoms as
  `length:bytes`, a fold with a retraction, for exchanging source. Kernel
  terms have a canonical, versioned exchange format already, the image
  (`Geb.Kernel.writeImage`), compared by bytes in continuous integration.
  The bytes of a source identify a document; the digest of a kernel term
  identifies a definition.

The syntax unification of the Bootstrap chapter, one reader over the
canonical data model with a quoted spelling for atoms that are not tokens,
is a widening, and waits until quoted atoms are wanted; its first use is
replacing the lists of character codes of
[bootstrap/stage1/datatype.geb](../bootstrap/stage1/datatype.geb), such
as `(quote (1 108 101 116))`.

### Out-of-band data and editor support

Comments never reach the image, and the compiler reads the core tree
only, so separating them has no motive at compilation. Its motives are
identity, the digest excluding annotations, and a future content store.
Two arrangements are available.

- Text is primary, comments are data in it, and the separation is derived
  when reading. The file is the combined view, so editors, diffs, merges
  and searches need nothing new. Precedents:
  [Clojure's metadata](https://clojure.org/reference/metadata), which does
  not affect equality or hashes; [Dhall](https://docs.dhall-lang.org/discussions/Safety-guarantees.html),
  which hashes a normal form without comments; and
  [Yatima](https://github.com/argumentcomputer/yatima-lang-alpha), whose
  `Term::embed` separates a nameless tree for the content identifier from
  a tree of names of the same shape, and whose `unembed` rejoins them and
  fails when the shapes differ. Darklang returned from a structure editor
  to text as the source of truth
  ([status update](https://blog.darklang.com/an-overdue-status-update/)).
- The separation is primary and text is a projection: Unison, Lamdu, MPS,
  and Unison's design of 2019, not built, of comments keyed by a hash and
  a path ([unison#443](https://github.com/unisonweb/unison/issues/443)).
  Keys by path move under edits, as Go's comment map does
  ([golang/go#20744](https://github.com/golang/go/issues/20744)); keys by
  hash conflate structurally equal definitions
  ([unison#462](https://github.com/unisonweb/unison/issues/462)); Unison
  drops comments inside terms when they are added to its codebase
  ([language reference](https://www.unison-lang.org/docs/language-reference/comments/),
  [unison#6262](https://github.com/unisonweb/unison/issues/6262)) and
  removed its metadata links
  ([unison#4574](https://github.com/unisonweb/unison/pull/4574)).

The first is recommended. The reader of the prototype supplies the
document; the side table is a function
`attach : List Item → Core × (Vertex ⇀ Notes)`, not stored as primary
data. A store, when one exists, keys its annotations by the named entry,
a core digest together with its names, as Yatima does, rather than by a
core digest and a path, and checks shapes as `unembed` does.

### Hashes and multihash references

Nothing is needed in the source now. References are names, resolved
deterministically given the manifest and the edition, and digests are
then the fold over the order of dependencies that the Bootstrap chapter
specifies. The one decision that touches the source is whether it will
contain a digest literal, pinning a dependency as Unison's `#…` does;
reserving `#` keeps that possible. Before the first digest is stored, the
hash is chosen between BLAKE3 and SHA3-256, the envelope and the tags of
[concrete-syntaxes.md](concrete-syntaxes.md) § Structural
content-addressing specification are fixed, and the vocabulary of
vertices is versioned.

### Files and references across them

Files stay outside Geb's semantics. A toolchain needs three things:

- a manifest per program, an S-expression naming the program, its
  edition and its files in order, read by the host driver, the tests, the
  formatter and a language server, replacing the lists in
  `scripts/bootstrap.sh` and the tests and the dependencies stated in
  comments;
- rejection of duplicate names by both readers, a narrowing that affects
  no present program;
- namespaces ([Namespaces](#namespaces-and-name-uniqueness)).

With content identity, a file is a view: a path in a namespace names a
definition's digest, and a program's order is the order of its
references. The manifest migrates mechanically into that; names being
unique, a file resolves alike in every program that includes it.

### Free-monad and cofree-comonad addressing

Nothing is needed now. Vertices, the directions of the cofree comonoid
([Geb/Prototypes/Definition/Vertex.lean](../Geb/Prototypes/Definition/Vertex.lean)),
and the directions of the free monad are computed from trees; no source
mentions them. They become persistent when a table keyed by vertex is
stored, which the arrangement recommended above never does, or when a
reference is a digest of a block with a direction, which blocks of
several members, absent from the kernel, need. Before either, the
vocabulary of vertices is versioned. The annotated document type
`μX. Ann × F X` of [concrete-syntaxes.md](concrete-syntaxes.md) and the
prototype's `RoseTree Lab` are one idea: the prototype keeps comments as
siblings, and `attach` makes them the `Ann` components.

### Documentation through Verso

Now: the markup of comments. The comments of the sources read as Verso
inline text but for one `_`, whereas a cross-reference such as
``{name}`typeIn` `` cannot be inferred mechanically from prose that reads
"the type checker". Verso markup, with the four roles the repository's
Lean modules use and `{name}` resolving to Geb definitions and checked
when documentation is built, is recommended, together with the convention
the sources follow: a block of comments immediately before a form
documents it, and a block followed by an empty line is prose.

Two routes render it.

- Docstrings in the emitted Lean: the backend
  [bootstrap/stage1/lean.geb](../bootstrap/stage1/lean.geb) writes
  `/-- … -/` before each definition from comments the Geb reader keeps. The
  literate site renders them beside the Lean denotations, not the Geb
  source, and the compiler and its artifacts change.
- A literate page per Geb file, generated from its document: top-level
  comments become prose and forms become code blocks of a `geb` expander
  (Verso supports `@[code_block]` expanders, as its `InlineLean` shows),
  which reads each block, fails the documentation build on one that does
  not read, and anchors each definition. No compiler change is needed and
  the page shows Geb source. This route is recommended.

Files whose comments come first and literate Markdown whose prose comes
first are two printers of the same document type, so either can be
adopted later by a mechanical translation.

### Paredit, parinfer and coloured parentheses

The following was determined for VS Code on 2026-09-29.

- Bracket pairs are coloured without an extension
  (`editor.bracketPairColorization.enabled`, the default since version
  1.67); brackets inside comments are skipped only when a TextMate grammar
  marks the comment as one
  ([bracket pair colorization](https://code.visualstudio.com/blogs/2021/09/29/bracket-pair-colorization)).
- `ailisp.strict-paredit` 0.3.1 fixes the languages it serves
  (`commonlisp`, `clojure`, `lisp`, `scheme`); Calva's paredit serves
  `clojure` files only.
- The parinfer extensions (`shaunlebron.vscode-parinfer` 0.6.2 and its
  forks) fix their languages likewise. The library `parinfer` 3.13.1
  exposes `parenMode` and `indentMode` over whole texts, and treats `[`,
  `]`, `{`, `}` as parentheses, `"` as a string delimiter and `\` as an
  escape, so atoms containing them break it.

Now, without code: associate `*.geb` with `scheme`
(`"files.associations": {"*.geb": "scheme"}`), install
`sjhuangx.vscode-scheme`, for the grammar and language configuration,
and `ailisp.strict-paredit`, and use `shaunlebron.vscode-parinfer` on
formatted files only. This is sound because atoms avoid the characters
Scheme treats specially, and the narrowed grammar keeps it so. Paren Mode,
which never changes the tree, and strict paredit serve the files as
written; Indent Mode is safe only on the formatter's output. A test in
continuous integration, `parenMode(x).text === x && indentMode(x).text
=== x` at a pinned parinfer, keeps the formatter compatible.

Later: a `geb` language (a manifest, a language configuration and a
TextMate grammar of some fifteen lines) with one-line forks of
strict-paredit and parinfer, and formatting on save through
`pucelle.run-on-save` calling `geb-fmt`.

### Tree-sitter and a language server

VS Code offers no user-extensible tree-sitter highlighting (experimental
grammars for a few built-in languages only;
[vscode#50140](https://github.com/microsoft/vscode/issues/50140) is
open); [tree-sitter-vscode](https://github.com/AlecGhost/tree-sitter-vscode)
highlights with a supplied grammar through semantic tokens, and Neovim,
Helix, Zed and Emacs 29 use tree-sitter natively. A grammar for Geb is
small; tree-sitter-scheme (MIT) is a base. Nothing is needed now.

Diagnostics come before a language server:
[efm-langserver](https://github.com/mattn/efm-langserver) turns a checker
on the command line into diagnostics, with a generic client for VS Code,
and the checker to run is `Geb.Kernel.diagnose`, which names the first
failing definition, applied after the stage-0 expansion for the datatype
language. Diagnostics with locations need a map from vertices to spans,
another derived annotation, and a checker that reports the failing
vertex; the trusted checker stays as it is, and the locating checker is a
separate, untrusted function. A language server in Lean, with
diagnostics, hover (a definition's type and comment) and navigation
(resolution against the manifest), has typed holes as its first use.

### Typed holes

- A hole of type `A` in a context `Γ` is a metavariable `u :: A[Γ]`
  occurring as `clo(u, id_Γ)` [NanevskiPfenningPientka2008]. Their Theorem
  4.6 translates such a metavariable into an ordinary variable of type
  `B₁ → … → Bₘ → A`, instantiation being substitution followed by β.
  Holes are lambda-lifted variables, and in a cartesian closed category a
  term with a hole is a morphism out of the exponential `[Γ ⇒ A]`, by
  functional completeness [LambekScott1986].
- Hazelnut Live assigns a hole its type in checking mode (rule EAEHole),
  and filling commutes with evaluation (Theorems 4.1 and 4.2)
  [OmarVoyseyChughHammer2019].
- The free Σ-monoid over presheaves on contexts characterizes
  metavariables, metasubstitution being the monad's bind [FioreHur2010]
  [FioreSzamozvancev2022].
- An Isabelle proof state with subgoals `ψ₁ … ψₙ` is the theorem
  `[ψ₁, …, ψₙ] ⇒ C`, the subgoals lifted over their parameters, and admits
  nothing [Paulson1989], unlike an axiom such as Lean's `sorryAx`.

Programs. Holes are written `?name`, `?` being reserved as the initial
character of an atom. The reader takes them as variables of the free
monad of the definition, the directions of
[definitions.md](definitions.md), and filling is `link`, the Kleisli
composition the definitions prototype proves associative. Their types come
from bidirectional checking with first-order unification of simple types,
which is decidable; people fill holes, so no higher-order unification
arises. Each hole is reported with its context, the names of its binders
taken from the document, and its type. The trusted checker is unchanged:
a program with holes checks exactly when its lambda-lifting does. A slice
`Set/(Ctx × Ty)` is the bookkeeping; presheaves on contexts are needed
only for metasubstitution capturing ambient variables or for first-class
contextual types, neither of which is wanted.

Proofs. A leaf `hole` carries a judgement `Γ_h | Φ_h ⊢ ψ_h`; the checker
returns the conclusion with the list of open holes, and certifies
`(⋀_h ∀Γ_h. (⋀Φ_h ⇒ ψ_h)) ⊢ goal`, sound in every topos since it uses
intuitionistic `∀` and `⇒` alone. Filling is grafting, the bind of the free
monad of derivation trees.

A checker of holes is not stronger than the metalogic's checker, its
conclusions being conditional; it is admitted by a translation of its
certificates into derivations under hypotheses, so it exercises the
admission of checkers in a small case, in the form the Bootstrap chapter
prescribes, a translation with a proof in the metalogic. It waits on the
metalogic's prover in Geb.

The checker of [Canonical](#canonical) is itself a checker of holes: it
checks terms containing unassigned metavariables and suspends at each,
so the report of a hole and the search that fills it share one
implementation.

### Program and proof synthesis

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
`Y`, so they need not be total. Stage 4 of the interaction-net arm of the
Bootstrap chapter, superpositions for searching certificates, is where it
would enter.

In order of availability:

1. A typed enumerator beside
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
2. Search over the prover's choices, with equality saturation
   [WillseyNandiWangFlattTatlockPanchekha2021] whose explanations become
   the prover's certificates of rewriting, and [Canonical](#canonical) for
   the choices of induction, motive and lemma.
3. SyGuS solvers such as cvc5 for first-order steps, their results checked
   again and a report of no solution never trusted.
4. A search in the manner of SupGen on an interaction-net runtime.

Nothing is needed in the source now; synthesis produces source and
constrains the format through holes only.

### Canonical

Canonical is a solver for type inhabitation in dependent type theory
[NormanAvigad2025].

- Its format is that of the Logical Framework [HarperHonsellPlotkin1993]
  without universes, with let definitions carrying reduction rules.
- Every term is β-normal and η-long, with one constructor,
  `λ x̄. let ȳ := M̄. f Ā`, and the type of a symbol determines its arity.
- A search refines one metavariable at a time. It chooses a head from the
  metavariable's local context and creates fresh metavariables for the
  head's arguments, all at once, so that they may be refined in any order.
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
lines of Lean
([repository](https://github.com/chasenorman/Canonical-min)).

- Its type checker for dependent type theory runs in a continuation
  monad. Meeting an unassigned metavariable, the checker stores the rest
  of the check as a constraint on that metavariable; assigning the
  metavariable resumes it.
- The search is iterative deepening over assignments of heads.
- On DTTBench, 31 problems from Lean's library needing β-reduction only,
  with a timeout of 60 seconds, it solves 31. Twelf solves 8, sauto 6 and
  Mimer 2.

Canonical is available under the MIT licence: the solver in Rust with the
Lean tactic ([Canonical](https://github.com/chasenorman/Canonical),
[CanonicalLean](https://github.com/chasenorman/CanonicalLean)), released
for each Lean version with precompiled libraries for three platforms, the
latest for Lean v4.34.0 on 2026-09-27. Outside Lean it reads a problem in
an undocumented JSON form. A mode for program synthesis, in which an
equation stuck on the major argument of a recursor counts as stuck rather
than violated, is described in the paper and absent from the released
tactic.

Three properties of Geb fit it.

- A checker of Geb is a fold over a tree of rule applications, that is,
  over the terms of a signature of the Logical Framework: judgements are
  families of types indexed by the terms they relate, and rules are
  constants. An inhabitant Canonical finds is a certificate, translated
  constant by constant, and Geb's trusted checker checks it again. The
  adequacy of the encoding need not be proved, since a wrong encoding
  costs completeness and never soundness.
- Canonical's metavariables with local contexts are the metavariables of
  contextual modal type theory, and a checker written as Canonical-min's
  is reports each hole's goal as the constraints suspended on it. The
  hole report and the filling search are one program
  ([Typed holes](#typed-holes)).
- Canonical accepts reduction rules. Given the kernel's computation rules
  (β, projections, the folds at constructors) as rules, an equation that
  holds by computation holds definitionally, and the search is left the
  structural choices of induction, motive and lemma. That complements
  the normalizing prover, which makes the computational steps and not the
  choices.

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
them. Canonical-min was measured at commit `72a24f1` of its repository,
Canonical at tag `v4.34.0` of CanonicalLean. To reproduce: the manifest of
Canonical-min pins an untagged revision of CanonicalLean, for which no
release archive exists, so the revision is replaced by the tag's; and the
tactic's native library is loaded when a goal is built as a module of the
package by `lake build`, not by `lake env lean`.

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
xs`, Canonical returns the following term, a derivation of Gödel's T
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

Four conclusions follow from the measurements, within their small
number.

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
  Rust, did not find the shortest derivation in 60 s; it serves as the
  specification of the algorithm rather than as a solver.

Recommendations:

- Now: nothing in the source format beyond the syntax of holes.
- The checker of holes is written as Canonical-min's is, in a monad that
  suspends at unassigned metavariables, so that it serves as the search's
  checker.
- A first integration, from Lean: the prover
  ([Geb/Prototypes/FreeTopos/Prover/](../Geb/Prototypes/FreeTopos/Prover.lean))
  states a subgoal in a Logical Framework signature of a checker's rules,
  calls Canonical, translates the term into a certificate and checks it
  with the Lean checker. This adds Canonical as a dependency of the
  package, a decision for the user; a release is published per Lean
  version, and the Rust solver is built from source otherwise.
- A Geb-native solver, after the metalogic's prover in Geb: the algorithm
  of Canonical-min written in Geb, bounded by fuel as every Geb program
  that searches is, and parameterized by a signature, so that each of
  Geb's checkers is searched by one program.
- Programs from examples take the enumerator of
  [Program and proof synthesis](#program-and-proof-synthesis), with the
  suspension of Canonical-min in place of a separate evaluator of partial
  candidates.

### Grammar narrowing and editions

Reserve ``" ' ` , # | [ ] { } \ @ ?`` as characters no atom contains,
except `?` as the initial character of a hole, and restrict atoms to
`[0-9]+` or an identifier beginning with a letter, with `&` kept as a
keyword. No source changes. The syntax then lies in [R7RS] `<datum>`,
[EDN] and `sexplib`, so generic tools for Lisps (paredit, parinfer,
grammars for Scheme) read it correctly, and strings, digest literals with
`#`, symbols quoted with `|`, vectors and holes can each be added as a
widening. Identifiers beyond ASCII, by Unicode's UAX #31 and
normalization form C, are a widening too, no source using one.

Record an edition per program in the manifest, as Racket's `#lang`,
Rust's editions and Go's `go` directive do. An edition fixes the reader,
its rules of resolution included, and the elaborator. An elaborator is a
committed image and the kernel is fixed, so an old edition's image runs
unchanged. Mixing editions in one program needs an interface between the
environments of elaborators, such as declarations of constructors; that
is its cost.

### Namespaces and name uniqueness

`.` separates qualifiers in the sources already (`Label.app`, `Prim.add`,
`Rule.hyp`). Names are annotations and bear no identity, so a namespace
is a matter of the reader: a namespace per entry of the manifest or a
`(namespace X)` form, and resolution in the current namespace, then the
opened ones, then by qualified name. Now: reject duplicates and reserve
`.` for qualification; present names remain valid in the root namespace.
Before the sources grow: the mechanism itself. Prefixes that avoid
collisions, such as `mTypeIn` beside `typeIn`, otherwise accumulate, and
removing them later is renaming by hand.

### Stability of elaboration

Commit, for each program, the elaborated definitions that
`lake exe geb-defs` writes, regenerate them in continuous integration and
compare them. Any change of expansion or resolution that alters existing
code is then detected, before digests exist; `bootstrap/compiler.img` has
that role for the compiler alone. State the encoding of the datatype
language in the manual as part of the first edition. A specification of
the expansion in Lean, as the checkers have, would free its meaning from
one Geb program; that is larger and can follow.

### Proof scripts and certificates

Before many proofs are written in Geb, fix the durable artifact: scripts
are the source; certificates, derivations under the fixed rule set, are
cached artifacts of the build, keyed by the statement and the elaborated
definitions it cites; and a script that fails after a change of the
prover falls back to its cached certificate while it is repaired. The
complete proofs about the compiler's components have from 600000 to
1240000 nodes, so the cache holds the form of shared certificates. The
metalogic has no surface syntax for statements in Geb text yet, and it
will need its own retraction at the level of documents.

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

## A sequence

Before most Geb code is written; these steps change `bootstrap/reader.geb`
and the committed images, so they follow other work on the reader:

1. Adopt the document reader and the formatter. Format `bootstrap/` in one
   mechanical change, the images unchanged as measured above, and add
   `geb-fmt --check` and the test of parinfer's fixed points to continuous
   integration.
2. Narrow the grammar in both readers and reject duplicate names.
3. Add manifests with editions, and the record of elaborated definitions.
4. Fix the markup and conventions of comments.
5. Configure VS Code: the association with Scheme, strict paredit, and
   parinfer on formatted files.

Early in writing: namespaces; `let*` and `cond`; quoted atoms; the report
of holes in programs; diagnostics with locations through efm-langserver;
literate pages generated from documents; and the first integration of
Canonical.

When their consumers exist: digests and the store, the versioned
vocabulary of vertices, `attach` and hover text, a language server,
tree-sitter, holes in proofs, the enumerator, the cache of certificates,
the export to canonical S-expressions, and a Geb-native solver.

## Open decisions

1. The reserved characters: whether `&` stays an atom, and whether
   identifiers beyond ASCII are admitted now.
2. Namespaces: per file, by a form, or by qualified names only.
3. The markup of comments: Verso or Markdown.
4. The route to documentation: literate pages from Geb source, or
   docstrings in the emitted Lean.
5. The layout policy. The retraction holds at every policy; parinfer
   constrains it to continuation lines inside the innermost open
   parenthesis and not beyond a parenthesis closed on the line before;
   whether a list that does not fit may keep its last element on its
   first line, as in `(def pick (lam (…)`, is style.
6. Whether Canonical becomes a dependency of the package, for the first
   integration, or is only ported.

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
- Chase Norman's talks on Canonical
  ([video 1](https://www.youtube.com/watch?v=y6p0hHkabXs),
  [video 2](https://www.youtube.com/watch?v=Me7WFEvoksw)).

Not verified: whether `emeraldwalk.RunOnSave` can run commands of VS Code;
whether clojure-lsp reports errors on `.geb` files; and a statement in the
literature that a derivation with open subgoals is a derivation under the
hypotheses `∀Γ_h. φ_h` in a topos's internal language, which follows from
the rules introducing `⇒` and `∀` but was not located.
