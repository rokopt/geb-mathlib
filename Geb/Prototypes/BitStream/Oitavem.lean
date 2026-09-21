/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Sig
public import Geb.Prototypes.BitStream.Oitavem.Bundle
public import Geb.Prototypes.BitStream.Oitavem.Stream
public import Geb.Prototypes.BitStream.Oitavem.Fields
public import Geb.Prototypes.BitStream.Oitavem.Label
public import Geb.Prototypes.BitStream.Oitavem.Edge
public import Geb.Prototypes.BitStream.Oitavem.Recognize
public import Geb.Prototypes.BitStream.Oitavem.Machine
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Bitstreams coded by expressions of Logs

Index for the modules that recognize a word as the code of a bitstream: the
finitary bundle signature, whose root has one child, an expression of Logs
with one normal and no safe argument, in place of the one child per depth
of {name}`Geb.BitStream.WConstruction.bundleSig`; the equivalence of its
admissible trees at the root index with those expressions; the stream an
expression codes, by corecursion on its values at the depths; the numerals
of a label as expressions of the logspace subalgebra; the label and edge
checks of the signature as expressions; the recognizer, as a function and
as an expression, with its specification; and the machine it compiles to.

The infinitely many observations of a stream are the values of one
expression at the depths, so the infinite branching of the M-type's
W-construction is carried by a finite code, and the coded streams are
those an expression of Logs defines. The map from codes to streams is
neither injective nor surjective, as the map from expressions to word
functions is not.
-/
