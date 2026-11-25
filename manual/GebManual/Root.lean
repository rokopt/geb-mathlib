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

The root `Part` of the Geb manual. Chapters are included here. The chapter of the shared Geb
library is written here, after them: the axiom linter admits a module that holds a document only
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
theorems of its proof document are proved by the prover written in Geb.

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

## Theorems

{gebProofs "library/library.manifest" "Bytes.proofs.geb"}
