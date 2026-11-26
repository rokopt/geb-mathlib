/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Introduction
public import GebManual.WTypes
public import GebManual.PHOAS
public import GebManual.DecisionProblems
public import GebManual.ValueRepresentation
public import GebManual.QuotientPRA
public import GebManual.Bootstrap
public import GebManual.Authoring
public import GebManual.CheckingCost
import Geb.Prototypes.Kernel.Requests

/-! # Manual root

The root `Part` of the Geb manual. Chapters are included here. The chapters of the shared Geb
library and the program language are written here: the axiom linter admits a document module only
where `GebMeta.classicalAllowedModules` lists it, and `GebMeta` is linked into the executable
whose bytes key the searches of the certificates (`docs/rules/ci-and-workflow.md`
§ Certificates), so that a chapter in a module of its own would run every search again. The
module of the host's protocol is imported for the constants the comments of the library's
module of requests name.
-/

open Verso.Genre Manual
open GebManual.Geb

#doc (Manual) "Geb" =>

{include 0 GebManual.Introduction}

{include 0 GebManual.WTypes}

{include 0 GebManual.PHOAS}

{include 0 GebManual.DecisionProblems}

{include 0 GebManual.ValueRepresentation}

{include 0 GebManual.QuotientPRA}

{include 0 GebManual.Bootstrap}

{include 0 GebManual.Authoring}

{include 0 GebManual.CheckingCost}

# The Geb library
%%%
tag := "library"
%%%

The library under `library/` is written in Geb and shared by the programs
that name its manifest, `library/library.manifest`, as a layer of theirs
({ref "downstream-authoring"}[A Geb library and its downstream
application]). Each section below includes one of its sources, in the order
of the manifest, a module to a source. The comments before a declaration
are its documentation, and a reference in them to a declaration of the
library links to that declaration. As the chapter builds, the library
compiles, the examples in its notes are evaluated and compared with their
expected values, the references of its comments are resolved, and the
theorems of its proof documents are proved by the prover written in Geb.
The last of those documents states its theorems over the library's
datatypes ({ref "typed-statements"}[Statements over the datatype language]).

A declaration with type parameters writes them after its name, and a use
supplies a type for each before its arguments
({ref "polymorphic-definitions"}[Polymorphic definitions]).

## Functions

{gebSource "library/library.manifest" "Functions.geb"}

## Optional values

{gebSource "library/library.manifest" "Optional.geb"}

## Lists

{gebSource "library/library.manifest" "Lists.geb"}

## Byte strings

{gebSource "library/library.manifest" "Bytes.geb"}

## Requests of a program to its host

{gebSource "library/library.manifest" "Requests.geb"}

## Saved values

{gebSource "library/library.manifest" "Saved.geb"}

## Theorems

{gebProofs "library/library.manifest" "Bytes.proofs.geb"}

## Lemmas of trees

{gebProofs "library/library.manifest" "Trees.proofs.geb"}

## Theorems over the datatypes

{gebProofs "library/library.manifest" "Datatypes.proofs.geb"}

# Writing a Geb program
%%%
tag := "program-language"
%%%

An outline is either an item carrying a value or a group of outlines. The program below counts
the items in an outline supplied as a tree. In `examples/language/`, the manifest
`outline.manifest` assembles `Outline.geb` and `Report.geb` in that order. The manual compiles
the program, resolves its entry point and evaluates its examples as it builds. The guide
describes edition `0`, whose compiler is selected by the client's Geb release or checkout.

## The program manifest

{gebListing "examples/language/outline.manifest" "outline.manifest"}

The `program` form gives the program a name. The `edition` selects the language edition, and
`document` selects the syntax of source files, the schema of their notes and the markup of
their prose. In the authoring syntax, parentheses group forms, spaces and newlines separate
atoms, and a semicolon begins a comment that ends with the line.

`sources` lists paths relative to the manifest and in declaration order. Here the second module
imports the first. The names in `entries` select the program's entry points by qualified
name. Other exported definitions remain available to importing modules.

## A datatype and its functions

{gebListing "examples/language/outline.manifest" "Outline.geb"}

A `module` gives its declarations a namespace. Its `export` list names what another module may
use. The `data` declaration introduces a type and its constructors. The parameter `A` in
`(Outline A)` stands for the item type. An `item` holds one value of that type. The final field
marked `&` in `group` holds any number of child outlines, supplied to the constructor as a list.

`def` binds a name to an expression. The `lam` defining `singleton` binds a typed argument,
and its body constructs a group with one item. `nil` takes the list's element type and
`cons` adds a head. A use of a generic definition or constructor
supplies its type arguments first. For instance, `(Outline.singleton T 9)` takes the singleton
function at the tree type `T` and applies it to the leaf labelled 9.

`defn` declares the arguments, result type and body of a function. The `case` in `valueOr`
matches its argument's constructor. The `item` pattern supplies the type parameter and binds
the field to `x`. The final `else` covers the other constructor. Without a default, the
clauses must cover every constructor.

`cata` folds the recursive datatype into a specified result type, here `T`. In its `item`
clause the wildcard `_` ignores the payload and the result is one. In its `group` clause the
pattern repeats the constructor's `&`. The variable `ns` holds the list of counts already
computed for the children. The list fold adds them starting at zero, so an empty group has
no items.

## Calling the module and checking examples

{gebListing "examples/language/outline.manifest" "Report.geb"}

`import Outline` brings the exported names into scope. The type abbreviation `OutlineT`
fixes the parameter at `T`. A tree literal gives its label followed by its children, each
itself a tree. A constructor's label is its zero-based position in the datatype declaration.
Thus `(0 (7))` encodes an item holding 7, and the outer `1` in `sample` encodes a group
containing an item and another group.

`datum` checks a literal tree against a datatype and gives it that type. `rep` takes a
typed value back to its representation in `T`. For a tree supplied at run time, `decode`
takes the expected datatype, the tree, a function for a successful decoding and a result for
failure. The body of `count` therefore applies `size` only to a checked outline.

A `note` attaches to the declaration immediately after it. Each `example` gives two closed
tree-valued expressions with qualified names. Compilation with `geb-author` evaluates them
and checks that their trees agree. The examples check the nested group's count, a singleton,
a malformed item whose required child is absent, and both branches of `valueOr`. `quote`
supplies the malformed tree as raw input to the decoder.

With the three files at the client root and the release unpacked at `geb/`, run
the following from the client root.

```
geb/bin/geb-author compile outline.manifest outline.img
```

The command writes the checked image. For a client of the shared library, see
{ref "library"}[The Geb library]. To state a theorem about a program and replay its
certificate, see {ref "first-authoring"}[Writing a first Geb development].
