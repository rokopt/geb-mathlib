module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.DatatypeSoundness

def «Prelude.append» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0

def «Prelude.length» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0

def «Prelude.reverse» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Prelude.replicate» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) => (x1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Prelude.single» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prelude.some» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x0)

def «Prelude.none» := _root_.Geb.Kernel.leaf 0

def «Prelude.isSome» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 1)

def «Prelude.get» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)

def «Prelude.and» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (x0).label ≠ 0 then x1 else _root_.Geb.Kernel.leaf 0

def «Prelude.or» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (x0).label ≠ 0 then _root_.Geb.Kernel.leaf 1 else x1

def «Prelude.at» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.child
      (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0)
      x1

def «Prelude.nth» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.lt
      x1
      (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x0)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x0 x1)
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Prelude.tail» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2)

def «Prelude.drop» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«Prelude.tail»
      x1
      x0

def «Prelude.digitsMsb» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.iter
      (α := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           _root_.List _root_.Geb.Kernel.Tree) =>
        (_root_.Geb.Kernel.Const.div (x3).1 x0,
          ((_root_.Geb.Kernel.Const.mod (x3).1 x0) :: (x3).2)))
      (x1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x2).2

def «Prelude.digitsLsb» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.reverse»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.digitsMsb» x0 x1 x2)

def «Reader.both» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1
    else
      _root_.Geb.Kernel.leaf 0

def «Reader.nonEmpty» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x0
      (_root_.Geb.Kernel.leaf 0)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.leaf 1)

def «Reader.allSome» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        (_root_.GebMirror.DatatypeSoundness.«Reader.both» x1 (x2).1,
          ((_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1) :: (x2).2)))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    if ((x1).1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) (x1).2)
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.lexFail» :=
  (([] : _root_.List _root_.Geb.Kernel.Tree),
    (([] : _root_.List _root_.Geb.Kernel.Tree),
      _root_.Geb.Kernel.leaf 11))

def «Reader.lexIn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    (x0, (x1, x2))

def «Reader.lexIdle» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.leaf 0)

def «Reader.withLen» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node x0 (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1)

def «Reader.inRange» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.lt x0 x1).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      _root_.Geb.Kernel.Const.lt
        x0
        (_root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))

def «Reader.isDigit» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 48)
      (_root_.Geb.Kernel.leaf 57)

def «Reader.isSpace» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 32)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 1
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 1
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
              _root_.Geb.Kernel.leaf 1
            else
              _root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 12)

def «Reader.isTokenStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 65)
      (_root_.Geb.Kernel.leaf 90)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
        x0
        (_root_.Geb.Kernel.leaf 97)
        (_root_.Geb.Kernel.leaf 122)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 1
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 45)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 46)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 1
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 47)).label ≠ 0 then
              _root_.Geb.Kernel.leaf 1
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 95)).label ≠ 0 then
                _root_.Geb.Kernel.leaf 1
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 58)).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 42)).label ≠ 0 then
                    _root_.Geb.Kernel.leaf 1
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 43)).label ≠ 0 then
                      _root_.Geb.Kernel.leaf 1
                    else
                      _root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 61)

def «Reader.isTokenChar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isTokenStart» x0).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x0

def «Reader.isPlainIn» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 32)
      (_root_.Geb.Kernel.leaf 126)).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 92)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 1
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 1
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 127) x0

def «Reader.atomTok» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 3)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x0)

def «Reader.kwHole» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 104,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 101]

def «Reader.holeToks» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    ((_root_.Geb.Kernel.leaf 2) ::
      ((_root_.GebMirror.DatatypeSoundness.«Reader.atomTok» x0) ::
        ((_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 3)
          (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Reader.kwHole»)) ::
          ((_root_.Geb.Kernel.leaf 1) :: x1))))

def «Reader.idleStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x1
      (_root_.Geb.Kernel.leaf 59)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
        x0
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.Geb.Kernel.leaf 4)
    else
      if (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 40)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle» ((_root_.Geb.Kernel.leaf 1) :: x0)
      else
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 41)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle» ((_root_.Geb.Kernel.leaf 2) :: x0)
        else
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
              x0
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                (_root_.Geb.Kernel.leaf 5)
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
          else
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 38)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle»
                ((_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 3)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.Geb.Kernel.leaf 38))) ::
                  x0)
            else
              if (_root_.Geb.Kernel.Const.eq
                x1
                (_root_.Geb.Kernel.leaf 63)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                  x0
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.Geb.Kernel.leaf 3)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                    x0
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                      (_root_.Geb.Kernel.leaf 13)
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x1
                    (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                      x0
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                        (_root_.Geb.Kernel.leaf 14)
                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                  else
                    if (_root_.GebMirror.DatatypeSoundness.«Reader.isSpace» x1).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle» x0
                    else
                      if (_root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x1).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                          x0
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1)
                          (_root_.Geb.Kernel.leaf 2)
                      else
                        if (_root_.GebMirror.DatatypeSoundness.«Reader.isTokenStart» x1).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                            x0
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1)
                            (_root_.Geb.Kernel.leaf 1)
                        else
                          _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»

def «Reader.endAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
      _root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x2)
    else
      _root_.Geb.Kernel.leaf 1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle»
        ((_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 3) x2) :: x0)
    else
      _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»

def «Reader.strStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x3
      (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.endAtom»
        x0
        x2
        (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x1)
    else
      if (_root_.Geb.Kernel.Const.eq
        x3
        (_root_.Geb.Kernel.leaf 92)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
          x0
          x1
          (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 6) x2)
      else
        if (_root_.GebMirror.DatatypeSoundness.«Reader.isPlainIn» x3).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
            x0
            (x3 :: x1)
            (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x2)
        else
          _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»

def «Reader.escChar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 97)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 7)
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 98)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 8)
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 116)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 9)
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 118)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 11)
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 110)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 10)
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 102)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 12)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 114)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 13)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Prelude.some» x0
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Prelude.some» x0
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 63)).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Prelude.some» x0
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 92)).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Prelude.some» x0
                        else
                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.hexVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 48))
    else
      if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
        x0
        (_root_.Geb.Kernel.leaf 65)
        (_root_.Geb.Kernel.leaf 70)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 55))
      else
        if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
          x0
          (_root_.Geb.Kernel.leaf 97)
          (_root_.Geb.Kernel.leaf 102)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 87))
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.decodeHex» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.mod
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x0)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      let x1 : _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
        (fun (x1 : _root_.Geb.Kernel.Tree)
           (x2 : _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.hexVal» x1;
          if (if ((x2).1).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3
          else
            _root_.Geb.Kernel.leaf 0).label ≠ 0 then
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» ((x2).2).2).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (((_root_.Geb.Kernel.Const.add
                  (_root_.Geb.Kernel.Const.mul
                    (_root_.Geb.Kernel.leaf 16)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3))
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» ((x2).2).2)) ::
                  ((x2).2).1),
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
            else
              (_root_.Geb.Kernel.leaf 1,
                (((x2).2).1,
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)))
          else
            (_root_.Geb.Kernel.leaf 0, (x2).2))
        (_root_.Geb.Kernel.leaf 1,
          (([] : _root_.List _root_.Geb.Kernel.Tree),
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
        x0;
      if ((x1).1).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) ((x1).2).1)
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.base64Val» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 65)
      (_root_.Geb.Kernel.leaf 90)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 65))
    else
      if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
        x0
        (_root_.Geb.Kernel.leaf 97)
        (_root_.Geb.Kernel.leaf 122)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 71))
      else
        if (_root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x0).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 4))
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 43)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 62)
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 47)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 63)
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.b64Fail» :=
  (_root_.Geb.Kernel.leaf 0,
    (([] : _root_.List _root_.Geb.Kernel.Tree),
      (_root_.Geb.Kernel.leaf 0,
        (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0))))

def «Reader.base64Step» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    if ((x0).1).label ≠ 0 then
      let x2 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
      let x3 : _root_.Geb.Kernel.Tree := (((x0).2).2).1;
      let x4 : _root_.Geb.Kernel.Tree := ((((x0).2).2).2).1;
      let x5 : _root_.Geb.Kernel.Tree := ((((x0).2).2).2).2;
      if (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 61)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.lt
          x5
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          (_root_.Geb.Kernel.leaf 1,
            (x2,
              (x3,
                (x4, _root_.Geb.Kernel.Const.add x5 (_root_.Geb.Kernel.leaf 1)))))
        else
          _root_.GebMirror.DatatypeSoundness.«Reader.b64Fail»
      else
        if (_root_.Geb.Kernel.Const.eq
          x5
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.base64Val»
            x1;
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x6).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.lt
              (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 6))
              (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  (_root_.Geb.Kernel.Const.add
                    (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 64) x3)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6),
                    (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 6),
                      _root_.Geb.Kernel.leaf 0))))
            else
              let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 64) x3)
                (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6);
              let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 6))
                (_root_.Geb.Kernel.leaf 8);
              let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
                (α := _root_.Geb.Kernel.Tree)
                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                  _root_.Geb.Kernel.Const.mul x9 (_root_.Geb.Kernel.leaf 2))
                (_root_.Geb.Kernel.leaf 1)
                x8;
              (_root_.Geb.Kernel.leaf 1,
                (((_root_.Geb.Kernel.Const.div x7 x9) :: x2),
                  (_root_.Geb.Kernel.Const.mod x7 x9, (x8, _root_.Geb.Kernel.leaf 0))))
          else
            _root_.GebMirror.DatatypeSoundness.«Reader.b64Fail»
        else
          _root_.GebMirror.DatatypeSoundness.«Reader.b64Fail»
    else
      x0

def «Reader.decodeBase64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            _root_.Geb.Kernel.Tree))) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)))) →
        _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree ×
              (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))))
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : (_root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)))) →
           _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree ×
                 (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))))
         (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)))) =>
        x2 (_root_.GebMirror.DatatypeSoundness.«Reader.base64Step» x3 x1))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)))) =>
        x1)
      x0
      (_root_.Geb.Kernel.leaf 1,
        (([] : _root_.List _root_.Geb.Kernel.Tree),
          (_root_.Geb.Kernel.leaf 0,
            (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0))));
    if (if ((x1).1).label ≠ 0 then
      _root_.Geb.Kernel.Const.lt
        ((((x1).2).2).2).1
        (_root_.Geb.Kernel.leaf 6)
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» ((x1).2).1))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.lengthStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x1;
    if (if (_root_.Geb.Kernel.Const.lt
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x3)).label ≠ 0 then
      _root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.leaf 48)
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
    else
      let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x4 : _root_.Geb.Kernel.Tree) (x5 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.add
            (_root_.Geb.Kernel.Const.sub x4 (_root_.Geb.Kernel.leaf 48))
            (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 10) x5))
        (_root_.Geb.Kernel.leaf 0)
        x1;
      if (_root_.Geb.Kernel.Const.eq
        x2
        (_root_.Geb.Kernel.leaf 58)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle»
            ((_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 3)
              ([] : _root_.List _root_.Geb.Kernel.Tree)) ::
              x0)
        else
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
            x0
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 12)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x4))
      else
        if (_root_.Geb.Kernel.Const.eq
          x2
          (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
            x0
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
              (_root_.Geb.Kernel.leaf 5)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.some» x4))
        else
          if (_root_.Geb.Kernel.Const.eq
            x2
            (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
              x0
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                (_root_.Geb.Kernel.leaf 13)
                (_root_.GebMirror.DatatypeSoundness.«Prelude.some» x4))
          else
            if (_root_.Geb.Kernel.Const.eq
              x2
              (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                x0
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                  (_root_.Geb.Kernel.leaf 14)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.some» x4))
            else
              _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»

def «Reader.lexStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree := (x0).1;
    let x3 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
    let x4 : _root_.Geb.Kernel.Tree := ((x0).2).2;
    let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x4;
    if (_root_.Geb.Kernel.Const.eq
      x5
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.idleStep» x2 x1
    else
      if (_root_.Geb.Kernel.Const.eq
        x5
        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle» x2
        else
          x0
      else
        if (_root_.Geb.Kernel.Const.eq
          x5
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          if (_root_.GebMirror.DatatypeSoundness.«Reader.isTokenChar» x1).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Reader.lexIn» x2 (x1 :: x3) x4
          else
            _root_.GebMirror.DatatypeSoundness.«Reader.idleStep»
              ((_root_.GebMirror.DatatypeSoundness.«Reader.atomTok» x3) :: x2)
              x1
        else
          if (_root_.Geb.Kernel.Const.eq
            x5
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            if (_root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x1).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Reader.lexIn» x2 (x1 :: x3) x4
            else
              if (if (_root_.GebMirror.DatatypeSoundness.«Reader.isTokenChar» x1).label ≠ 0 then
                _root_.Geb.Kernel.leaf 1
              else
                if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x1
                    (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
                    _root_.Geb.Kernel.leaf 1
                  else
                    _root_.Geb.Kernel.Const.eq
                      x1
                      (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.lengthStep» x2 x3 x1
              else
                _root_.GebMirror.DatatypeSoundness.«Reader.idleStep»
                  ((_root_.GebMirror.DatatypeSoundness.«Reader.atomTok» x3) :: x2)
                  x1
          else
            if (_root_.Geb.Kernel.Const.eq
              x5
              (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
              if (if (_root_.GebMirror.DatatypeSoundness.«Reader.isTokenChar» x1).label ≠ 0 then
                if (_root_.GebMirror.DatatypeSoundness.«Reader.nonEmpty» x3).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Reader.isDigit» x1).label ≠ 0 then
                    _root_.Geb.Kernel.leaf 0
                  else
                    _root_.Geb.Kernel.leaf 1
              else
                _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.lexIn» x2 (x1 :: x3) x4
              else
                if (_root_.GebMirror.DatatypeSoundness.«Reader.nonEmpty» x3).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Reader.idleStep»
                    (_root_.GebMirror.DatatypeSoundness.«Reader.holeToks» x3 x2)
                    x1
                else
                  _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
            else
              if (_root_.Geb.Kernel.Const.eq
                x5
                (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                x0
              else
                if (_root_.Geb.Kernel.Const.eq
                  x5
                  (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.lt
                    (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 0))
                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIdle»
                      ((_root_.GebMirror.DatatypeSoundness.«Reader.atomTok» (x1 :: x3)) :: x2)
                  else
                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                      x2
                      (x1 :: x3)
                      (_root_.Geb.Kernel.Const.node
                        (_root_.Geb.Kernel.leaf 12)
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                          (_root_.Geb.Kernel.Const.sub
                            (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 0))
                            (_root_.Geb.Kernel.leaf 1))))
                else
                  let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                    x4
                    (_root_.Geb.Kernel.leaf 0);
                  if (_root_.Geb.Kernel.Const.eq
                    x5
                    (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Reader.strStep» x2 x3 x6 x1
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x5
                      (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.escChar» x1;
                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                          x2
                          ((_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7) :: x3)
                          (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x1
                          (_root_.Geb.Kernel.leaf 120)).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                            x2
                            x3
                            (_root_.Geb.Kernel.Const.node
                              (_root_.Geb.Kernel.leaf 9)
                              (x6 ::
                                ((_root_.Geb.Kernel.leaf 0) ::
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.Geb.Kernel.leaf 0)))))
                        else
                          if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
                            x1
                            (_root_.Geb.Kernel.leaf 48)
                            (_root_.Geb.Kernel.leaf 55)).label ≠ 0 then
                            _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                              x2
                              x3
                              (_root_.Geb.Kernel.Const.node
                                (_root_.Geb.Kernel.leaf 10)
                                (x6 ::
                                  ((_root_.Geb.Kernel.leaf 1) ::
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                      (_root_.Geb.Kernel.Const.sub
                                        x1
                                        (_root_.Geb.Kernel.leaf 48))))))
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x1
                              (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                              _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                x2
                                x3
                                (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 7) x6)
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x1
                                (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                  x2
                                  x3
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 8) x6)
                              else
                                _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x5
                        (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                        if (_root_.Geb.Kernel.Const.eq
                          x1
                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                            x2
                            x3
                            (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                        else
                          _root_.GebMirror.DatatypeSoundness.«Reader.strStep» x2 x3 x6 x1
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x5
                          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.eq
                            x1
                            (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                            _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                              x2
                              x3
                              (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                          else
                            _root_.GebMirror.DatatypeSoundness.«Reader.strStep» x2 x3 x6 x1
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x5
                            (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.hexVal» x1;
                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                              if (_root_.Geb.Kernel.Const.eq
                                (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 1))
                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                  x2
                                  ((_root_.Geb.Kernel.Const.add
                                    (_root_.Geb.Kernel.Const.mul
                                      (_root_.Geb.Kernel.leaf 16)
                                      (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 2)))
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)) ::
                                    x3)
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                              else
                                _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                  x2
                                  x3
                                  (_root_.Geb.Kernel.Const.node
                                    (_root_.Geb.Kernel.leaf 9)
                                    (x6 ::
                                      ((_root_.Geb.Kernel.leaf 1) ::
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)))))
                            else
                              _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x5
                              (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                              if (_root_.GebMirror.DatatypeSoundness.«Reader.inRange»
                                x1
                                (_root_.Geb.Kernel.leaf 48)
                                (_root_.Geb.Kernel.leaf 55)).label ≠ 0 then
                                let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                                  (_root_.Geb.Kernel.Const.mul
                                    (_root_.Geb.Kernel.leaf 8)
                                    (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 2)))
                                  (_root_.Geb.Kernel.Const.sub x1 (_root_.Geb.Kernel.leaf 48));
                                if (_root_.Geb.Kernel.Const.eq
                                  (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 1))
                                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                  if (_root_.Geb.Kernel.Const.lt
                                    x7
                                    (_root_.Geb.Kernel.leaf 256)).label ≠ 0 then
                                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                      x2
                                      (x7 :: x3)
                                      (_root_.GebMirror.DatatypeSoundness.«Reader.withLen»
                                        (_root_.Geb.Kernel.leaf 5)
                                        x6)
                                  else
                                    _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                                else
                                  _root_.GebMirror.DatatypeSoundness.«Reader.lexIn»
                                    x2
                                    x3
                                    (_root_.Geb.Kernel.Const.node
                                      (_root_.Geb.Kernel.leaf 10)
                                      (x6 ::
                                        ((_root_.Geb.Kernel.Const.add
                                          (_root_.Geb.Kernel.Const.child
                                            x4
                                            (_root_.Geb.Kernel.leaf 1))
                                          (_root_.Geb.Kernel.leaf 1)) ::
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x7))))
                              else
                                _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x5
                                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                if (_root_.GebMirror.DatatypeSoundness.«Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.hexVal» x1)).label ≠ 0 then
                                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
                                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.decodeHex»
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x3);
                                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                                        _root_.GebMirror.DatatypeSoundness.«Reader.endAtom»
                                          x2
                                          x6
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                              else
                                if (_root_.GebMirror.DatatypeSoundness.«Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.base64Val» x1)).label ≠ 0 then
                                    _root_.Geb.Kernel.leaf 1
                                  else
                                    _root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 61)).label ≠ 0 then
                                    _root_.GebMirror.DatatypeSoundness.«Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
                                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.decodeBase64»
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x3);
                                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                                        _root_.GebMirror.DatatypeSoundness.«Reader.endAtom»
                                          x2
                                          x6
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Reader.lexFail»

def «Reader.lexEnd» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := (x0).1;
    let x2 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
      ((x0).2).2;
    if (if (_root_.Geb.Kernel.Const.eq
      x3
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.Geb.Kernel.Const.eq
        x3
        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x1))
    else
      if (if (_root_.Geb.Kernel.Const.eq
        x3
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 1
      else
        _root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse»
              ((_root_.GebMirror.DatatypeSoundness.«Reader.atomTok» x2) :: x1)))
      else
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
          if (_root_.GebMirror.DatatypeSoundness.«Reader.nonEmpty» x2).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse»
                  (_root_.GebMirror.DatatypeSoundness.«Reader.holeToks» x2 x1)))
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.tokenize» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.lt
          x1
          (_root_.Geb.Kernel.leaf 256)).label ≠ 0 then
          x2
        else
          _root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      x0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.lexEnd»
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) →
            _root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
          (fun (x1 : _root_.Geb.Kernel.Tree)
             (x2 : (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) →
               _root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
             (x3 : _root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
            x2 (_root_.GebMirror.DatatypeSoundness.«Reader.lexStep» x3 x1))
          (fun (x1 : _root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
            x1)
          x0
          (_root_.GebMirror.DatatypeSoundness.«Reader.lexIdle»
            ([] : _root_.List _root_.Geb.Kernel.Tree)))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.fail» :=
  (_root_.Geb.Kernel.leaf 0,
    ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree)))

def «Reader.parseStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree) =>
    if ((x0).1).label ≠ 0 then
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree ×
          _root_.List (_root_.List _root_.Geb.Kernel.Tree))
        (x0).2
        _root_.GebMirror.DatatypeSoundness.«Reader.fail»
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree)
           (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            (_root_.Geb.Kernel.leaf 1,
              (([] : _root_.List _root_.Geb.Kernel.Tree) :: (x2 :: x3)))
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x1)
              (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (((_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 1)
                  (_root_.Geb.Kernel.Const.children x1)) ::
                  x2) ::
                  x3))
            else
              _root_.Geb.Kernel.Const.lcase
                (α := _root_.List _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree ×
                  _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                x3
                _root_.GebMirror.DatatypeSoundness.«Reader.fail»
                (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
                   (x5 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                  (_root_.Geb.Kernel.leaf 1,
                    (((_root_.Geb.Kernel.Const.node
                      (_root_.Geb.Kernel.leaf 2)
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x2)) ::
                      x4) ::
                      x5))))
    else
      x0

def «Reader.readSExps» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.tokenize»
      x0;
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree ×
        _root_.List
          (_root_.List
            _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := (_root_.Geb.Kernel.Tree ×
          _root_.List (_root_.List _root_.Geb.Kernel.Tree)) →
          _root_.Geb.Kernel.Tree ×
            _root_.List (_root_.List _root_.Geb.Kernel.Tree))
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : (_root_.Geb.Kernel.Tree ×
             _root_.List (_root_.List _root_.Geb.Kernel.Tree)) →
             _root_.Geb.Kernel.Tree ×
               _root_.List (_root_.List _root_.Geb.Kernel.Tree))
           (x4 : _root_.Geb.Kernel.Tree ×
             _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          x3 (_root_.GebMirror.DatatypeSoundness.«Reader.parseStep» x4 x2))
        (fun (x2 : _root_.Geb.Kernel.Tree ×
             _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          x2)
        (_root_.Geb.Kernel.Const.children (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1))
        (_root_.Geb.Kernel.leaf 1,
          (([] : _root_.List _root_.Geb.Kernel.Tree) ::
            ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))));
      if ((x2).1).label ≠ 0 then
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.List _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          (x2).2
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
             (x4 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.List _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x4
              (_root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x3)))
              (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
                 (_ : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.isAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 1)

def «Reader.isList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 2)

def «Reader.nameOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.Const.children x0)

def «Reader.named» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x0).label ≠ 0 then
      _root_.Geb.Kernel.Const.equal (_root_.GebMirror.DatatypeSoundness.«Reader.nameOf» x0) x1
    else
      _root_.Geb.Kernel.leaf 0

def «Reader.kwT» := _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 84]

def «Reader.kwUnit» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 85,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116]

def «Reader.kwProd» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 80,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100]

def «Reader.kwArrow» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 65,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 119]

def «Reader.kwList» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 76,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Reader.kwLam» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 109]

def «Reader.kwLet» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 116]

def «Reader.kwPair» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 114]

def «Reader.kwFst» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Reader.kwSnd» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 100]

def «Reader.kwIf» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 102]

def «Reader.kwQuote» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 113,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101]

def «Reader.kwCons» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 115]

def «Reader.kwNil» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 108]

def «Reader.kwFold» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100]

def «Reader.kwPara» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 97]

def «Reader.kwIter» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 114]

def «Reader.kwFoldr» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 114]

def «Reader.kwLcase» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 101]

def «Reader.kwUnitValue» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116]

def «Reader.kwDef» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102]

def «Reader.kwDeftype» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 121,
    _root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 101]

def «Reader.kwDefnum» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 109]

def «Reader.primNames» :=
  _root_.Geb.Kernel.Const.children
    (_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
        _root_.Geb.Kernel.leaf 97,
        _root_.Geb.Kernel.leaf 98,
        _root_.Geb.Kernel.leaf 101,
        _root_.Geb.Kernel.leaf 108],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 97,
        _root_.Geb.Kernel.leaf 114,
        _root_.Geb.Kernel.leaf 105,
        _root_.Geb.Kernel.leaf 116,
        _root_.Geb.Kernel.leaf 121],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 99,
        _root_.Geb.Kernel.leaf 104,
        _root_.Geb.Kernel.leaf 105,
        _root_.Geb.Kernel.leaf 108,
        _root_.Geb.Kernel.leaf 100],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 110,
        _root_.Geb.Kernel.leaf 111,
        _root_.Geb.Kernel.leaf 100,
        _root_.Geb.Kernel.leaf 101],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 99,
        _root_.Geb.Kernel.leaf 104,
        _root_.Geb.Kernel.leaf 105,
        _root_.Geb.Kernel.leaf 108,
        _root_.Geb.Kernel.leaf 100,
        _root_.Geb.Kernel.leaf 114,
        _root_.Geb.Kernel.leaf 101,
        _root_.Geb.Kernel.leaf 110],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 97,
        _root_.Geb.Kernel.leaf 100,
        _root_.Geb.Kernel.leaf 100],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 115,
        _root_.Geb.Kernel.leaf 117,
        _root_.Geb.Kernel.leaf 98],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 109,
        _root_.Geb.Kernel.leaf 117,
        _root_.Geb.Kernel.leaf 108],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
        _root_.Geb.Kernel.leaf 105,
        _root_.Geb.Kernel.leaf 118],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 109,
        _root_.Geb.Kernel.leaf 111,
        _root_.Geb.Kernel.leaf 100],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 101,
        _root_.Geb.Kernel.leaf 113],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
        _root_.Geb.Kernel.leaf 116],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 101,
        _root_.Geb.Kernel.leaf 113,
        _root_.Geb.Kernel.leaf 117,
        _root_.Geb.Kernel.leaf 97,
        _root_.Geb.Kernel.leaf 108],
      _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 108,
        _root_.Geb.Kernel.leaf 111,
        _root_.Geb.Kernel.leaf 103,
        _root_.Geb.Kernel.leaf 50]])

def «Reader.indexOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal x0 x2).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
        else
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
              (_root_.Geb.Kernel.Const.add
                (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)
                (_root_.Geb.Kernel.leaf 1))
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      x1

def «Reader.lookupAbbrev» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal
          x0
          (_root_.Geb.Kernel.Const.child
            x2
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1))
        else
          x3)
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      x1

def «Reader.numeral» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        if (_root_.Geb.Kernel.Const.lt
          x1
          (_root_.Geb.Kernel.leaf 48)).label ≠ 0 then
          (_root_.Geb.Kernel.leaf 0, (x2).2)
        else
          if (_root_.Geb.Kernel.Const.lt
            (_root_.Geb.Kernel.leaf 57)
            x1).label ≠ 0 then
            (_root_.Geb.Kernel.leaf 0, (x2).2)
          else
            ((x2).1,
              (_root_.Geb.Kernel.Const.add
                ((x2).2).1
                (_root_.Geb.Kernel.Const.mul
                  (_root_.Geb.Kernel.Const.sub x1 (_root_.Geb.Kernel.leaf 48))
                  ((x2).2).2),
                _root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 10) ((x2).2).2)))
      (_root_.Geb.Kernel.leaf 1,
        (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 1))
      x0;
    if (_root_.GebMirror.DatatypeSoundness.«Reader.nonEmpty» x0).label ≠ 0 then
      if ((x1).1).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some» ((x1).2).1
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.expandNums» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node x2 x3;
        if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x4).label ≠ 0 then
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.lookupAbbrev»
            (_root_.GebMirror.DatatypeSoundness.«Reader.nameOf» x4)
            x0;
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x5).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.get» x5
          else
            x4
        else
          x4)
      x1

def «Reader.numOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.expandNums»
      x0
      x1;
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x2).label ≠ 0 then
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
        (_root_.GebMirror.DatatypeSoundness.«Reader.numeral»
          (_root_.Geb.Kernel.Const.children x2))).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some» x2
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.rtTrees» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Reader.rtValues» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).2 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Reader.node2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      x0
      (x1 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2))

def «Reader.some2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x1 x2).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.GebMirror.DatatypeSoundness.«Reader.node2»
          x0
          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x2))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.readType» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          x2
          (_root_.GebMirror.DatatypeSoundness.«Reader.rtTrees» x3);
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rtValues» x3;
        (x4,
          if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x4).label ≠ 0 then
            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.nameOf» x4;
            if (_root_.Geb.Kernel.Const.equal
              x6
              _root_.GebMirror.DatatypeSoundness.«Reader.kwT»).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
            else
              if (_root_.Geb.Kernel.Const.equal
                x6
                _root_.GebMirror.DatatypeSoundness.«Reader.kwUnit»).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 1)
              else
                _root_.GebMirror.DatatypeSoundness.«Reader.lookupAbbrev» x6 x0
          else
            if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x4).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                (_root_.Geb.Kernel.Const.children x4)
                (_root_.Geb.Kernel.leaf 0);
              let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x4;
              if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                x6
                _root_.GebMirror.DatatypeSoundness.«Reader.kwProd»).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.eq
                  x7
                  (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Reader.some2»
                    (_root_.Geb.Kernel.leaf 2)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1))
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 2))
                else
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
              else
                if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                  x6
                  _root_.GebMirror.DatatypeSoundness.«Reader.kwArrow»).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.eq
                    x7
                    (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Reader.some2»
                      (_root_.Geb.Kernel.leaf 3)
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1))
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 2))
                  else
                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                    x6
                    _root_.GebMirror.DatatypeSoundness.«Reader.kwList»).label ≠ 0 then
                    if (_root_.Geb.Kernel.Const.eq
                      x7
                      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                          x5
                          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 4)
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get»
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))))
                      else
                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                  else
                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
      x1).2

def «Reader.readDatum» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x0).label ≠ 0 then
      let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.numeral»
        (_root_.Geb.Kernel.Const.children x0);
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)
            ([] : _root_.List _root_.Geb.Kernel.Tree))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      let x1 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.fold
        (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
        (fun (x1 : _root_.Geb.Kernel.Tree)
           (x2 : _root_.List
             (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
          let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
            x1
            (_root_.GebMirror.DatatypeSoundness.«Reader.rtTrees» x2);
          (x3,
            if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x3).label ≠ 0 then
              let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.numeral»
                (_root_.Geb.Kernel.Const.children x3);
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x4).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                      (_root_.Geb.Kernel.Const.node
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x4)
                        ([] : _root_.List _root_.Geb.Kernel.Tree))))
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.Geb.Kernel.Const.children x3))
            else
              if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x3).label ≠ 0 then
                _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.Geb.Kernel.Tree)
                  (_root_.Geb.Kernel.Const.children x3)
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                  (fun (x4 : _root_.Geb.Kernel.Tree)
                     (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom»
                      x4).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Reader.numeral» (_root_.Geb.Kernel.Const.children x4)
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
                    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.tail» (_root_.GebMirror.DatatypeSoundness.«Reader.rtValues» x2));
                    if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x6 x7).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                        (_root_.Geb.Kernel.Const.node
                          (_root_.Geb.Kernel.leaf 0)
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                            (_root_.Geb.Kernel.Const.node
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)
                              (_root_.Geb.Kernel.Const.foldr
                                (α := _root_.Geb.Kernel.Tree)
                                (β := _root_.List _root_.Geb.Kernel.Tree)
                                (fun (x8 : _root_.Geb.Kernel.Tree)
                                   (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                                    (_root_.Geb.Kernel.Const.children x8)
                                    x9)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.Geb.Kernel.Const.children
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))))))
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
        x0).2;
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.child
            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)
            (_root_.Geb.Kernel.leaf 0))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.rrTrees» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Reader.rrApply» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (((x2).2 x1) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «$5265616465722f5252732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2)

def «Reader.rrAt» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List
          (_root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
        _root_.GebMirror.DatatypeSoundness.«$5265616465722f5252732e7461696c»
        x0
        x1)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (_ : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        (x3).2)
      x2

def «Reader.app» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.node2» (_root_.Geb.Kernel.leaf 10) x0 x1

def «Reader.apps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Reader.app» x3 x2)
      x0
      (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x1)

def «Reader.some1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          x0
          (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.argsOf» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
      (_root_.GebMirror.DatatypeSoundness.«Reader.rrApply»
        (_root_.Geb.Kernel.Const.iter
          (α := _root_.List
            (_root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
          _root_.GebMirror.DatatypeSoundness.«$5265616465722f5252732e7461696c»
          x0
          x1)
        x2)

def «Reader.mkArgs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          x0
          (_root_.Geb.Kernel.Const.children (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.appsOpt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x0 x1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.GebMirror.DatatypeSoundness.«Reader.apps»
          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x0)
          (_root_.Geb.Kernel.Const.children (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1)))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.binders» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x0).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
        if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom»
          (_root_.Geb.Kernel.Const.child
            x0
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.single» x0
        else
          _root_.Geb.Kernel.Const.children x0
      else
        _root_.Geb.Kernel.Const.children x0
    else
      ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Reader.readBinders» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x2).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.arity x2)
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom»
                (_root_.Geb.Kernel.Const.child
                  x2
                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
                  x0
                  (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1));
                if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x4).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                    (_root_.GebMirror.DatatypeSoundness.«Reader.node2»
                      (_root_.Geb.Kernel.leaf 0)
                      (_root_.GebMirror.DatatypeSoundness.«Reader.nameOf»
                        (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0)))
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x4))
                else
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none») ::
            x3))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x1)

def «Reader.resolveAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.numeral»
      (_root_.Geb.Kernel.Const.children x1);
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)))
    else
      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.nameOf» x1;
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
        x4
        x2;
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x5).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 8)
            (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x5)))
      else
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
          x4
          x0;
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x6).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 23)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)))
        else
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
            x4
            _root_.GebMirror.DatatypeSoundness.«Reader.primNames»;
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 22)
                (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)))
          else
            if (_root_.Geb.Kernel.Const.equal
              x4
              _root_.GebMirror.DatatypeSoundness.«Reader.kwUnitValue»).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 11)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Reader.resolveList» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
    let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x1;
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
      x4
      (_root_.Geb.Kernel.leaf 0);
    if (_root_.Geb.Kernel.Const.eq
      x5
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
        x6
        _root_.GebMirror.DatatypeSoundness.«Reader.kwLam»).label ≠ 0 then
        _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 3)
      else
        _root_.Geb.Kernel.leaf 0).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readBinders»
          x0
          (_root_.GebMirror.DatatypeSoundness.«Reader.binders»
            (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)));
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
          let x8 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7);
          if (_root_.GebMirror.DatatypeSoundness.«Reader.nonEmpty» x8).label ≠ 0 then
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 2)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
                (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse»
                  (_root_.Geb.Kernel.Const.foldr
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.List _root_.Geb.Kernel.Tree)
                    (fun (x9 : _root_.Geb.Kernel.Tree)
                       (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                      ((_root_.Geb.Kernel.Const.child x9 (_root_.Geb.Kernel.leaf 0)) ::
                        x10))
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    x8))
                x3);
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x9).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.Geb.Kernel.Const.foldr
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.Geb.Kernel.Tree)
                  (fun (x10 : _root_.Geb.Kernel.Tree) (x11 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.DatatypeSoundness.«Reader.node2»
                      (_root_.Geb.Kernel.leaf 9)
                      (_root_.Geb.Kernel.Const.child x10 (_root_.Geb.Kernel.leaf 1))
                      x11)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x9)
                  x8)
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      else
        if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
          x6
          _root_.GebMirror.DatatypeSoundness.«Reader.kwLet»).label ≠ 0 then
          _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 5)
        else
          _root_.Geb.Kernel.leaf 0).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
            x4
            (_root_.Geb.Kernel.leaf 1);
          if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x7).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
              x0
              (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2));
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 4)
              ((_root_.GebMirror.DatatypeSoundness.«Reader.nameOf» x7) :: x3);
            let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 3)
              x3;
            if (_root_.GebMirror.DatatypeSoundness.«Reader.both»
              x8
              (_root_.GebMirror.DatatypeSoundness.«Reader.both» x9 x10)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.GebMirror.DatatypeSoundness.«Reader.app»
                  (_root_.GebMirror.DatatypeSoundness.«Reader.node2»
                    (_root_.Geb.Kernel.leaf 9)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x9))
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x10))
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
            x6
            _root_.GebMirror.DatatypeSoundness.«Reader.kwPair»).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Reader.mkArgs»
              (_root_.Geb.Kernel.leaf 12)
              (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
          else
            if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
              x6
              _root_.GebMirror.DatatypeSoundness.«Reader.kwFst»).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Reader.mkArgs»
                (_root_.Geb.Kernel.leaf 13)
                (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
            else
              if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                x6
                _root_.GebMirror.DatatypeSoundness.«Reader.kwSnd»).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.mkArgs»
                  (_root_.Geb.Kernel.leaf 14)
                  (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
              else
                if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                  x6
                  _root_.GebMirror.DatatypeSoundness.«Reader.kwIf»).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Reader.mkArgs»
                    (_root_.Geb.Kernel.leaf 16)
                    (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                    x6
                    _root_.GebMirror.DatatypeSoundness.«Reader.kwCons»).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Reader.mkArgs»
                      (_root_.Geb.Kernel.leaf 20)
                      (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
                  else
                    if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                      x6
                      _root_.GebMirror.DatatypeSoundness.«Reader.kwQuote»).label ≠ 0 then
                      _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 2)
                    else
                      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Reader.some1»
                        (_root_.Geb.Kernel.leaf 15)
                        (_root_.GebMirror.DatatypeSoundness.«Reader.readDatum»
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                    else
                      if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                        x6
                        _root_.GebMirror.DatatypeSoundness.«Reader.kwNil»).label ≠ 0 then
                        _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 2)
                      else
                        _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Reader.some1»
                          (_root_.Geb.Kernel.leaf 19)
                          (_root_.GebMirror.DatatypeSoundness.«Reader.readType»
                            x0
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                      else
                        if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                          x6
                          _root_.GebMirror.DatatypeSoundness.«Reader.kwFold»).label ≠ 0 then
                          _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                        else
                          _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
                            x0
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                            _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                (_root_.Geb.Kernel.Const.node
                                  (_root_.Geb.Kernel.leaf 17)
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))))
                              (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                          else
                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                        else
                          if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                            x6
                            _root_.GebMirror.DatatypeSoundness.«Reader.kwPara»).label ≠ 0 then
                            _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                          else
                            _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
                              x0
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                              _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                  (_root_.Geb.Kernel.Const.node
                                    (_root_.Geb.Kernel.leaf 25)
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))))
                                (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                            else
                              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                          else
                            if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                              x6
                              _root_.GebMirror.DatatypeSoundness.«Reader.kwIter»).label ≠ 0 then
                              _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                            else
                              _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                              let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
                                x0
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                                _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                    (_root_.Geb.Kernel.Const.node
                                      (_root_.Geb.Kernel.leaf 18)
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))))
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                              else
                                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                            else
                              if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                                x6
                                _root_.GebMirror.DatatypeSoundness.«Reader.kwFoldr»).label ≠ 0 then
                                _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 2) x5
                              else
                                _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                                let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.some2»
                                  (_root_.Geb.Kernel.leaf 21)
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.readType»
                                    x0
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.readType»
                                    x0
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2)));
                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                                  _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                                    x7
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf»
                                      x2
                                      (_root_.Geb.Kernel.leaf 3)
                                      x3)
                                else
                                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                              else
                                if (if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
                                  x6
                                  _root_.GebMirror.DatatypeSoundness.«Reader.kwLcase»).label ≠ 0 then
                                  _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 2) x5
                                else
                                  _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.some2»
                                    (_root_.Geb.Kernel.leaf 24)
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.readType»
                                      x0
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.readType»
                                      x0
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2)));
                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                                    _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                                      x7
                                      (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf»
                                        x2
                                        (_root_.Geb.Kernel.leaf 3)
                                        x3)
                                  else
                                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                else
                                  _root_.GebMirror.DatatypeSoundness.«Reader.appsOpt»
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 0) x3)
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.argsOf»
                                      x2
                                      (_root_.Geb.Kernel.leaf 1)
                                      x3)

def «Reader.resolve» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          x4
          (_root_.GebMirror.DatatypeSoundness.«Reader.rrTrees» x5);
        (x6,
          fun (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom» x6).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Reader.resolveAtom» x1 x6 x7
            else
              if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x6).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.resolveList» x0 x6 x5 x7
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»))
      x2).2
      x3

def «Reader.reservedNames» :=
  _root_.GebMirror.DatatypeSoundness.«Prelude.append»
    (_root_.GebMirror.DatatypeSoundness.«Reader.kwLam» ::
      (_root_.GebMirror.DatatypeSoundness.«Reader.kwLet» ::
        (_root_.GebMirror.DatatypeSoundness.«Reader.kwPair» ::
          (_root_.GebMirror.DatatypeSoundness.«Reader.kwFst» ::
            (_root_.GebMirror.DatatypeSoundness.«Reader.kwSnd» ::
              (_root_.GebMirror.DatatypeSoundness.«Reader.kwIf» ::
                (_root_.GebMirror.DatatypeSoundness.«Reader.kwQuote» ::
                  (_root_.GebMirror.DatatypeSoundness.«Reader.kwCons» ::
                    (_root_.GebMirror.DatatypeSoundness.«Reader.kwNil» ::
                      (_root_.GebMirror.DatatypeSoundness.«Reader.kwFold» ::
                        (_root_.GebMirror.DatatypeSoundness.«Reader.kwPara» ::
                          (_root_.GebMirror.DatatypeSoundness.«Reader.kwIter» ::
                            (_root_.GebMirror.DatatypeSoundness.«Reader.kwFoldr» ::
                              (_root_.GebMirror.DatatypeSoundness.«Reader.kwLcase» ::
                                (_root_.GebMirror.DatatypeSoundness.«Reader.kwUnitValue» ::
                                  (_root_.GebMirror.DatatypeSoundness.«Reader.kwDef» ::
                                    (_root_.GebMirror.DatatypeSoundness.«Reader.kwDeftype» ::
                                      (_root_.GebMirror.DatatypeSoundness.«Reader.kwDefnum» ::
                                        (_root_.GebMirror.DatatypeSoundness.«Reader.kwHole» ::
                                          ((_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 42,
                                            _root_.Geb.Kernel.leaf 97,
                                            _root_.Geb.Kernel.leaf 110,
                                            _root_.Geb.Kernel.leaf 110]) ::
                                            ((_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 42,
                                              _root_.Geb.Kernel.leaf 100,
                                              _root_.Geb.Kernel.leaf 111,
                                              _root_.Geb.Kernel.leaf 99]) ::
                                              (_root_.GebMirror.DatatypeSoundness.«Reader.kwT» ::
                                                (_root_.GebMirror.DatatypeSoundness.«Reader.kwUnit» ::
                                                  (_root_.GebMirror.DatatypeSoundness.«Reader.kwProd» ::
                                                    (_root_.GebMirror.DatatypeSoundness.«Reader.kwArrow» ::
                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwList»))))))))))))))))))))))))))
    _root_.GebMirror.DatatypeSoundness.«Reader.primNames»

def «Reader.isFresh» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
      (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
        x3
        _root_.GebMirror.DatatypeSoundness.«Reader.reservedNames»)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
        (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf» x3 x2)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
          (_root_.GebMirror.DatatypeSoundness.«Reader.lookupAbbrev» x3 x0)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 0
        else
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
            (_root_.GebMirror.DatatypeSoundness.«Reader.lookupAbbrev» x3 x1)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 0
          else
            _root_.Geb.Kernel.leaf 1

def «Reader.progStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            _root_.List _root_.Geb.Kernel.Tree))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
    let x3 : _root_.List _root_.Geb.Kernel.Tree := (((x0).2).2).1;
    let x4 : _root_.List _root_.Geb.Kernel.Tree := ((((x0).2).2).2).1;
    let x5 : _root_.List _root_.Geb.Kernel.Tree := ((((x0).2).2).2).2;
    if (if ((x0).1).label ≠ 0 then
      if (_root_.GebMirror.DatatypeSoundness.«Reader.isList» x1).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.arity x1)
          (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
          if (_root_.GebMirror.DatatypeSoundness.«Reader.isAtom»
            (_root_.Geb.Kernel.Const.child
              x1
              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Reader.isFresh»
              x2
              x3
              x4
              (_root_.GebMirror.DatatypeSoundness.«Reader.nameOf»
                (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))
          else
            _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 0
      else
        _root_.Geb.Kernel.leaf 0
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.nameOf»
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1));
      if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
        _root_.GebMirror.DatatypeSoundness.«Reader.kwDef»).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.resolve»
          x2
          x4
          (_root_.GebMirror.DatatypeSoundness.«Reader.expandNums»
            x3
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2)))
          ([] : _root_.List _root_.Geb.Kernel.Tree);
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
          (_root_.Geb.Kernel.leaf 1,
            (x2,
              (x3,
                (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
                  x4
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x6),
                  _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                    x5
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))))))
        else
          (_root_.Geb.Kernel.leaf 0, (x0).2)
      else
        if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
          (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.DatatypeSoundness.«Reader.kwDeftype»).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readType»
            x2
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2));
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
            (_root_.Geb.Kernel.leaf 1,
              (((_root_.GebMirror.DatatypeSoundness.«Reader.node2»
                (_root_.Geb.Kernel.leaf 0)
                x6
                (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)) ::
                x2),
                ((x0).2).2))
          else
            (_root_.Geb.Kernel.leaf 0, (x0).2)
        else
          if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.DatatypeSoundness.«Reader.kwDefnum»).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.numOf»
              x3
              (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2));
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  (((_root_.GebMirror.DatatypeSoundness.«Reader.node2»
                    (_root_.Geb.Kernel.leaf 0)
                    x6
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)) ::
                    x3),
                    (((x0).2).2).2)))
            else
              (_root_.Geb.Kernel.leaf 0, (x0).2)
          else
            (_root_.Geb.Kernel.leaf 0, (x0).2)
    else
      (_root_.Geb.Kernel.leaf 0, (x0).2)

def «Reader.readProgram» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            _root_.List
              _root_.Geb.Kernel.Tree))) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))) →
        _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree ×
                _root_.List _root_.Geb.Kernel.Tree))))
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : (_root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 _root_.List _root_.Geb.Kernel.Tree)))) →
           _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))
         (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 _root_.List _root_.Geb.Kernel.Tree)))) =>
        x2 (_root_.GebMirror.DatatypeSoundness.«Reader.progStep» x3 x1))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 _root_.List _root_.Geb.Kernel.Tree)))) =>
        x1)
      x0
      (_root_.Geb.Kernel.leaf 1,
        (([] : _root_.List _root_.Geb.Kernel.Tree),
          (([] : _root_.List _root_.Geb.Kernel.Tree),
            (([] : _root_.List _root_.Geb.Kernel.Tree),
              ([] : _root_.List _root_.Geb.Kernel.Tree)))));
    if ((x1).1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.GebMirror.DatatypeSoundness.«Reader.node2»
          (_root_.Geb.Kernel.leaf 100)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 101)
            ((((x1).2).2).2).2)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 102)
            ((((x1).2).2).2).1))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Check.tyArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Reader.node2» (_root_.Geb.Kernel.leaf 3) x0 x1

def «Check.tyList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x0)

def «Check.isTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.length» x2;
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 1
          else
            _root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 1)
        else
          if (_root_.Geb.Kernel.Const.eq
            x3
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.and»
              (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 4))
              (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
          else
            if (_root_.Geb.Kernel.Const.eq
              x3
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  _root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 3))
                (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)))
            else
              _root_.Geb.Kernel.leaf 0)
      x0

def «Check.isProd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))

def «Check.isArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 3))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))

def «Check.isListTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 4))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 1))

def «Check.foldTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Check.tyList» x0)
          x0))
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow» (_root_.Geb.Kernel.leaf 0) x0)

def «Check.iterTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow» x0 x0)
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow» (_root_.Geb.Kernel.leaf 0) x0))

def «Check.foldrTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow» x1 x1))
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
        x1
        (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Check.tyList» x0)
          x1))

def «Check.lcaseTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Check.tyList» x0)
      (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
        x1
        (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
            x0
            (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
              (_root_.GebMirror.DatatypeSoundness.«Check.tyList» x0)
              x1))
          x1))

def «Check.primTypes» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0);
  let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
    (_root_.Geb.Kernel.leaf 0)
    x0;
  _root_.GebMirror.DatatypeSoundness.«Prelude.append»
    (x0 ::
      (x0 ::
        (x1 ::
          ((_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
            (_root_.Geb.Kernel.leaf 0)
            (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
              (_root_.GebMirror.DatatypeSoundness.«Check.tyList» (_root_.Geb.Kernel.leaf 0))
              (_root_.Geb.Kernel.leaf 0))) ::
            ((_root_.GebMirror.DatatypeSoundness.«Check.tyArrow»
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.DatatypeSoundness.«Check.tyList» (_root_.Geb.Kernel.leaf 0))) ::
              ([] : _root_.List _root_.Geb.Kernel.Tree))))))
    (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.replicate» (_root_.Geb.Kernel.leaf 8) x1)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x0))

def «Check.checkNode» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x1;
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
    let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x1;
    if (_root_.Geb.Kernel.Const.eq
      x4
      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.eq
        x6
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
          x3
          (_root_.Geb.Kernel.Const.label
            (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      if (_root_.Geb.Kernel.Const.eq
        x4
        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x6
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
            x5
            (_root_.Geb.Kernel.leaf 0);
          if (_root_.GebMirror.DatatypeSoundness.«Check.isTy» x7).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 1)
              (x7 :: x3);
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x8).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.GebMirror.DatatypeSoundness.«Check.tyArrow» x7 (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8))
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      else
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x6
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 0)
              x3;
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 1)
              x3;
            if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x7 x8).label ≠ 0 then
              if (_root_.GebMirror.DatatypeSoundness.«Check.isArrow»
                (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8)
                  (_root_.Geb.Kernel.Const.child
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                    (_root_.Geb.Kernel.Const.child
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                      (_root_.Geb.Kernel.leaf 1))
                else
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 1)
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            if (_root_.Geb.Kernel.Const.eq
              x4
              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
              if (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.some2»
                  (_root_.Geb.Kernel.leaf 2)
                  (_root_.GebMirror.DatatypeSoundness.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 0) x3)
                  (_root_.GebMirror.DatatypeSoundness.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 1) x3)
              else
                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
            else
              if (_root_.Geb.Kernel.Const.eq
                x4
                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                    x2
                    (_root_.Geb.Kernel.leaf 0)
                    x3;
                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                    if (_root_.GebMirror.DatatypeSoundness.«Check.isProd»
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                        (_root_.Geb.Kernel.Const.child
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                          (_root_.Geb.Kernel.leaf 0))
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                  else
                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                else
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
              else
                if (_root_.Geb.Kernel.Const.eq
                  x4
                  (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.eq
                    x6
                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                      x2
                      (_root_.Geb.Kernel.leaf 0)
                      x3;
                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x7).label ≠ 0 then
                      if (_root_.GebMirror.DatatypeSoundness.«Check.isProd»
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                          (_root_.Geb.Kernel.Const.child
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                            (_root_.Geb.Kernel.leaf 1))
                      else
                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                  else
                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x4
                    (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                    if (_root_.Geb.Kernel.Const.eq
                      x6
                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
                    else
                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x4
                      (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                      if (_root_.Geb.Kernel.Const.eq
                        x6
                        (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 0)
                          x3;
                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 1)
                          x3;
                        let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 2)
                          x3;
                        if (_root_.GebMirror.DatatypeSoundness.«Reader.both»
                          x7
                          (_root_.GebMirror.DatatypeSoundness.«Reader.both» x8 x9)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.equal
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                            if (_root_.Geb.Kernel.Const.equal
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x9)
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8)).label ≠ 0 then
                              x8
                            else
                              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                          else
                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                        else
                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                      else
                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x4
                        (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                        if (_root_.Geb.Kernel.Const.eq
                          x6
                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                          if (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                              x5
                              (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                              (_root_.GebMirror.DatatypeSoundness.«Check.foldTy»
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                          else
                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                        else
                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x4
                          (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.eq
                            x6
                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                            if (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                x5
                                (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                (_root_.GebMirror.DatatypeSoundness.«Check.foldTy»
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                            else
                              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                          else
                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x4
                            (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                            if (_root_.Geb.Kernel.Const.eq
                              x6
                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                              if (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                  x5
                                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                  (_root_.GebMirror.DatatypeSoundness.«Check.iterTy»
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                              else
                                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                            else
                              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x4
                              (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                              if (_root_.Geb.Kernel.Const.eq
                                x6
                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                if (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                    x5
                                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                    (_root_.GebMirror.DatatypeSoundness.«Check.tyList»
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                                else
                                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                              else
                                _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x4
                                (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                                if (_root_.Geb.Kernel.Const.eq
                                  x6
                                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                                    x2
                                    (_root_.Geb.Kernel.leaf 0)
                                    x3;
                                  let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.rrAt»
                                    x2
                                    (_root_.Geb.Kernel.leaf 1)
                                    x3;
                                  if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x7 x8).label ≠ 0 then
                                    if (_root_.GebMirror.DatatypeSoundness.«Check.isListTy»
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.equal
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7)
                                        (_root_.Geb.Kernel.Const.child
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8)
                                          (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                          (_root_.GebMirror.DatatypeSoundness.«Check.tyList»
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                  else
                                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                else
                                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                              else
                                if (_root_.Geb.Kernel.Const.eq
                                  x4
                                  (_root_.Geb.Kernel.leaf 21)).label ≠ 0 then
                                  if (_root_.Geb.Kernel.Const.eq
                                    x6
                                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                      (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                                      (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                          x5
                                          (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                        (_root_.GebMirror.DatatypeSoundness.«Check.foldrTy»
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 0))
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 1)))
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                  else
                                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                else
                                  if (_root_.Geb.Kernel.Const.eq
                                    x4
                                    (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                    if (_root_.Geb.Kernel.Const.eq
                                      x6
                                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                      _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
                                        _root_.GebMirror.DatatypeSoundness.«Check.primTypes»
                                        (_root_.Geb.Kernel.Const.label
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)))
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x4
                                      (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.eq
                                        x6
                                        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                        _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
                                          x0
                                          (_root_.Geb.Kernel.Const.label
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                              x5
                                              (_root_.Geb.Kernel.leaf 0)))
                                      else
                                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                    else
                                      if (_root_.Geb.Kernel.Const.eq
                                        x4
                                        (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                                        if (_root_.Geb.Kernel.Const.eq
                                          x6
                                          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                                x5
                                                (_root_.Geb.Kernel.leaf 0)))
                                            (_root_.GebMirror.DatatypeSoundness.«Check.isTy»
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                                x5
                                                (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                              (_root_.GebMirror.DatatypeSoundness.«Check.lcaseTy»
                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 1)))
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                      else
                                        _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Check.typeIn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          x3
          (_root_.GebMirror.DatatypeSoundness.«Reader.rrTrees» x4);
        (x5,
          fun (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.DatatypeSoundness.«Check.checkNode» x0 x5 x4 x6))
      x2).2
      x1

def «Check.typeOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.typeIn»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1

def «Check.checkProgram» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) →
           _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        x2
          (if ((x3).1).label ≠ 0 then
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Check.typeOf»
              (x3).2
              x1;
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x4).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                  (x3).2
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x4)))
            else
              (_root_.Geb.Kernel.leaf 0, (x3).2)
          else
            x3))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           _root_.List _root_.Geb.Kernel.Tree) =>
        x1)
      x0
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree));
    if ((x1).1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) (x1).2)
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Typing.name» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Typing.sameName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.equal
      x0
      x1;
    x2

def «Typing.tx0» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 1) x0

def «Typing.tList» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 2) x0

def «Typing.tx3» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 3)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tx4» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 4)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tx5» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 5)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tx6» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 6)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tx7» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 7)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tx8» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 8)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tMarker» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 9) x0

def «Typing.tData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 10)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Typing.tAs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 11)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Typing.tOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 12)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Typing.tCase» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 13) x0

def «Typing.tCata» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 14) x0

def «Typing.tGeneric» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 15) x0

def «Typing.Tx.member» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.child
      (_root_.Geb.Kernel.Const.fold
        (α := _root_.Geb.Kernel.Tree)
        (fun (x1 : _root_.Geb.Kernel.Tree)
           (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            x2;
          _root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ((if (if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.arity x3)
                (_root_.Geb.Kernel.leaf 0)
            else
              if (_root_.Geb.Kernel.Const.eq
                x1
                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                _root_.Geb.Kernel.Const.lt
                  (_root_.Geb.Kernel.leaf 0)
                  (_root_.Geb.Kernel.Const.add
                    (_root_.Geb.Kernel.Const.arity x3)
                    (_root_.Geb.Kernel.leaf 1))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.lt
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.Geb.Kernel.Const.add
                      (_root_.Geb.Kernel.Const.arity x3)
                      (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                    _root_.Geb.Kernel.Const.foldr
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.Geb.Kernel.Tree)
                      (fun (x4 : _root_.Geb.Kernel.Tree) (x5 : _root_.Geb.Kernel.Tree) =>
                        if (_root_.Geb.Kernel.Const.child
                          x4
                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                          x5
                        else
                          _root_.Geb.Kernel.leaf 0)
                      (_root_.Geb.Kernel.leaf 1)
                      (_root_.Geb.Kernel.Const.iter
                        (α := _root_.List _root_.Geb.Kernel.Tree)
                        (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                          _root_.Geb.Kernel.Const.lcase
                            (α := _root_.Geb.Kernel.Tree)
                            (β := _root_.List _root_.Geb.Kernel.Tree)
                            x4
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (fun (_ : _root_.Geb.Kernel.Tree)
                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                              x6))
                        x2
                        (_root_.Geb.Kernel.leaf 0))
                  else
                    _root_.Geb.Kernel.leaf 0
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x1
                    (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                    _root_.Geb.Kernel.Const.eq
                      (_root_.Geb.Kernel.Const.arity x3)
                      (_root_.Geb.Kernel.leaf 0)
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x1
                      (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                      _root_.Geb.Kernel.Const.eq
                        (_root_.Geb.Kernel.Const.arity x3)
                        (_root_.Geb.Kernel.leaf 0)
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x1
                        (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                        _root_.Geb.Kernel.Const.eq
                          (_root_.Geb.Kernel.Const.arity x3)
                          (_root_.Geb.Kernel.leaf 0)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x1
                          (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                          _root_.Geb.Kernel.Const.eq
                            (_root_.Geb.Kernel.Const.arity x3)
                            (_root_.Geb.Kernel.leaf 0)
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x1
                            (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                            _root_.Geb.Kernel.Const.eq
                              (_root_.Geb.Kernel.Const.arity x3)
                              (_root_.Geb.Kernel.leaf 0)
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x1
                              (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                              _root_.Geb.Kernel.Const.eq
                                (_root_.Geb.Kernel.Const.arity x3)
                                (_root_.Geb.Kernel.leaf 0)
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x1
                                (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                _root_.Geb.Kernel.Const.lt
                                  (_root_.Geb.Kernel.leaf 0)
                                  (_root_.Geb.Kernel.Const.add
                                    (_root_.Geb.Kernel.Const.arity x3)
                                    (_root_.Geb.Kernel.leaf 1))
                              else
                                if (_root_.Geb.Kernel.Const.eq
                                  x1
                                  (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                  if (_root_.Geb.Kernel.Const.eq
                                    (_root_.Geb.Kernel.Const.arity x3)
                                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                    _root_.Geb.Kernel.Const.child
                                      (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
                                      (_root_.Geb.Kernel.leaf 0)
                                  else
                                    _root_.Geb.Kernel.leaf 0
                                else
                                  if (_root_.Geb.Kernel.Const.eq
                                    x1
                                    (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                    if (_root_.Geb.Kernel.Const.eq
                                      (_root_.Geb.Kernel.Const.arity x3)
                                      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.child
                                        (_root_.Geb.Kernel.Const.child
                                          x3
                                          (_root_.Geb.Kernel.leaf 0))
                                        (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                        _root_.Geb.Kernel.Const.child
                                          (_root_.Geb.Kernel.Const.child
                                            x3
                                            (_root_.Geb.Kernel.leaf 1))
                                          (_root_.Geb.Kernel.leaf 0)
                                      else
                                        _root_.Geb.Kernel.leaf 0
                                    else
                                      _root_.Geb.Kernel.leaf 0
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.eq
                                        (_root_.Geb.Kernel.Const.arity x3)
                                        (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                        if (_root_.Geb.Kernel.Const.child
                                          (_root_.Geb.Kernel.Const.child
                                            x3
                                            (_root_.Geb.Kernel.leaf 0))
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.child
                                            (_root_.Geb.Kernel.Const.child
                                              x3
                                              (_root_.Geb.Kernel.leaf 1))
                                            (_root_.Geb.Kernel.leaf 0)
                                        else
                                          _root_.Geb.Kernel.leaf 0
                                      else
                                        _root_.Geb.Kernel.leaf 0
                                    else
                                      if (_root_.Geb.Kernel.Const.eq
                                        x1
                                        (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                        if (_root_.Geb.Kernel.Const.lt
                                          (_root_.Geb.Kernel.leaf 0)
                                          (_root_.Geb.Kernel.Const.add
                                            (_root_.Geb.Kernel.Const.arity x3)
                                            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.Geb.Kernel.Tree) =>
                                              if (_root_.Geb.Kernel.Const.child
                                                x4
                                                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                x5
                                              else
                                                _root_.Geb.Kernel.leaf 0)
                                            (_root_.Geb.Kernel.leaf 1)
                                            (_root_.Geb.Kernel.Const.iter
                                              (α := _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x4
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x6))
                                              x2
                                              (_root_.Geb.Kernel.leaf 0))
                                        else
                                          _root_.Geb.Kernel.leaf 0
                                      else
                                        if (_root_.Geb.Kernel.Const.eq
                                          x1
                                          (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                                          if (_root_.Geb.Kernel.Const.lt
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.Geb.Kernel.Const.add
                                              (_root_.Geb.Kernel.Const.arity x3)
                                              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                            _root_.Geb.Kernel.Const.foldr
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              (fun (x4 : _root_.Geb.Kernel.Tree)
                                                 (x5 : _root_.Geb.Kernel.Tree) =>
                                                if (_root_.Geb.Kernel.Const.child
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                  x5
                                                else
                                                  _root_.Geb.Kernel.leaf 0)
                                              (_root_.Geb.Kernel.leaf 1)
                                              (_root_.Geb.Kernel.Const.iter
                                                (α := _root_.List _root_.Geb.Kernel.Tree)
                                                (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                  _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.List _root_.Geb.Kernel.Tree)
                                                    x4
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (fun (_ : _root_.Geb.Kernel.Tree)
                                                       (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x6))
                                                x2
                                                (_root_.Geb.Kernel.leaf 0))
                                          else
                                            _root_.Geb.Kernel.leaf 0
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x1
                                            (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                                            if (_root_.Geb.Kernel.Const.lt
                                              (_root_.Geb.Kernel.leaf 0)
                                              (_root_.Geb.Kernel.Const.add
                                                (_root_.Geb.Kernel.Const.arity x3)
                                                (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                              _root_.Geb.Kernel.Const.foldr
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.Geb.Kernel.Tree)
                                                (fun (x4 : _root_.Geb.Kernel.Tree)
                                                   (x5 : _root_.Geb.Kernel.Tree) =>
                                                  if (_root_.Geb.Kernel.Const.child
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                    x5
                                                  else
                                                    _root_.Geb.Kernel.leaf 0)
                                                (_root_.Geb.Kernel.leaf 1)
                                                (_root_.Geb.Kernel.Const.iter
                                                  (α := _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.List _root_.Geb.Kernel.Tree)
                                                      x4
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (fun (_ : _root_.Geb.Kernel.Tree)
                                                         (x6 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x6))
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 0))
                                            else
                                              _root_.Geb.Kernel.leaf 0
                                          else
                                            _root_.Geb.Kernel.leaf 0).label ≠ 0 then
              _root_.Geb.Kernel.leaf 1
            else
              _root_.Geb.Kernel.leaf 0) ::
              ([] : _root_.List _root_.Geb.Kernel.Tree)))
        x0)
      (_root_.Geb.Kernel.leaf 0)

def «$547970696e672f5478732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f5478732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f5478732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f5478732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$547970696e672f5478732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$547970696e672f5478732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f5478732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Typing.tyT» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tyUnit» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 1)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.tyProd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Typing.tyArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 3)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Typing.tyList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Typing.tyData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 5)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Typing.tySort» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 6)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Typing.sameTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.equal
      x0
      x1;
    x2

def «$547970696e672f5479732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f5479732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f5479732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f5479732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$547970696e672f5479732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$547970696e672f5479732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f5479732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f5479732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5479732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$547970696e672f4f54792e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$547970696e672f4f54792e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$547970696e672f4f54792e69734a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$547970696e672f4f54792e66726f6d4d61796265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$547970696e672f4f54792e6e74684f66» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x2);
    x2

def «$547970696e672f4f54792e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «$547970696e672f4d5479732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f4d5479732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f4d5479732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f4d5479732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$547970696e672f4d5479732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$547970696e672f4d5479732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4d5479732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f4d5479732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4d5479732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Typing.eraseTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            _root_.Geb.Kernel.leaf 0,
            x2);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
          _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              _root_.Geb.Kernel.leaf 0,
              x2);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
            _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit»
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x1)
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                _root_.Geb.Kernel.leaf 0,
                x2);
              let x5 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
              let x6 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                (x4).2
                (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                  ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                   (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                  (x6, x7));
              let x7 : _root_.Geb.Kernel.Tree := (x6).1 ();
              let x8 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x5
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x9);
              let x9 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                (x6).2
                (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                  ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                (fun (x9 : _root_.Unit → _root_.Geb.Kernel.Tree)
                   (x10 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                  (x9, x10));
              let x10 : _root_.Geb.Kernel.Tree := (x9).1 ();
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x8
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x12);
              _root_.GebMirror.DatatypeSoundness.«Typing.tyProd» x7 x10
            else
              if (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.label x1)
                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                  _root_.Geb.Kernel.leaf 0,
                  x2);
                let x5 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                let x6 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                  (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                    _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                  (x4).2
                  (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                    ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                  (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                     (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                    (x6, x7));
                let x7 : _root_.Geb.Kernel.Tree := (x6).1 ();
                let x8 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.List _root_.Geb.Kernel.Tree)
                  x5
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (fun (_ : _root_.Geb.Kernel.Tree)
                     (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                    x9);
                let x9 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                  (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                    _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                  (x6).2
                  (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                    ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                  (fun (x9 : _root_.Unit → _root_.Geb.Kernel.Tree)
                     (x10 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                    (x9, x10));
                let x10 : _root_.Geb.Kernel.Tree := (x9).1 ();
                let _ : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.List _root_.Geb.Kernel.Tree)
                  x8
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (fun (_ : _root_.Geb.Kernel.Tree)
                     (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                    x12);
                _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» x7 x10
              else
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                  let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                    _root_.Geb.Kernel.leaf 0,
                    x2);
                  let x5 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                  let x6 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                    (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                    (x4).2
                    (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                      ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                    (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                       (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                      (x6, x7));
                  let x7 : _root_.Geb.Kernel.Tree := (x6).1 ();
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.List _root_.Geb.Kernel.Tree)
                    x5
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (fun (_ : _root_.Geb.Kernel.Tree)
                       (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                      x9);
                  _root_.GebMirror.DatatypeSoundness.«Typing.tyList» x7
                else
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x1)
                    (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                    let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                      _root_.Geb.Kernel.leaf 0,
                      x2);
                    let x5 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                    let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                      (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                        _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                      (x4).2
                      (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                        ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                      (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                         (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                        (x6, x7));
                    let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.Geb.Kernel.Tree)
                      x5
                      (_root_.Geb.Kernel.leaf 0)
                      (fun (x7 : _root_.Geb.Kernel.Tree)
                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        x7);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      x5
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (fun (_ : _root_.Geb.Kernel.Tree)
                         (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                        x9);
                    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
                  else
                    let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                      _root_.Geb.Kernel.leaf 0,
                      x2);
                    let x5 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                    let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                      (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                        _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
                      (x4).2
                      (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                        ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
                      (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                         (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                        (x6, x7));
                    let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.Geb.Kernel.Tree)
                      x5
                      (_root_.Geb.Kernel.leaf 0)
                      (fun (x7 : _root_.Geb.Kernel.Tree)
                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        x7);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      x5
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (fun (_ : _root_.Geb.Kernel.Tree)
                         (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                        x9);
                    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)
      x0
      ();
    x1

def «Typing.isData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «Typing.foldTyOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
        _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x0)
          x0))
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» _root_.GebMirror.DatatypeSoundness.«Typing.tyT» x0);
    x1

def «Typing.iterTyOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» x0 x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» _root_.GebMirror.DatatypeSoundness.«Typing.tyT» x0));
    x1

def «Typing.foldrTyOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» x1 x1))
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
        x1
        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x0)
          x1));
    x2

def «Typing.lcaseTyOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
        x1
        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
          (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
            x0
            (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
              (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x0)
              x1))
          x1));
    x2

def «Typing.tt» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»

def «Typing.ttt» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
    _root_.GebMirror.DatatypeSoundness.«Typing.tt»

def «Typing.primTys» :=
  (_root_.GebMirror.DatatypeSoundness.«Typing.tt» ::
    (_root_.GebMirror.DatatypeSoundness.«Typing.tt» ::
      (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
        ((_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
          _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
          (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
            (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)
            _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)) ::
          ((_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
            _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
            (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)) ::
            (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
              (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                  (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                    (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                      (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                        (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                          (_root_.GebMirror.DatatypeSoundness.«Typing.ttt» ::
                            (_root_.GebMirror.DatatypeSoundness.«Typing.tt» ::
                              ([] : _root_.List _root_.Geb.Kernel.Tree)))))))))))))))

def «Typing.abbr» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$547970696e672f41626272732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f41626272732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f41626272732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f41626272732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$547970696e672f41626272732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$547970696e672f41626272732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f41626272732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$547970696e672f4e616d65732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f4e616d65732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f4e616d65732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f4e616d65732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$547970696e672f4e616d65732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$547970696e672f4e616d65732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f4e616d65732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Typing.mkEnv» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := (x0,
      (x1, (x2, (x3, (x4, x5)))));
    x6

def «Typing.envAl» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := (x0).1; x1

def «Typing.envDefs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1; x1

def «Typing.envNoms» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := (((x0).2).2).1; x1

def «Typing.envSorts» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := ((((x0).2).2).2).1; x1

def «Typing.envNums» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := (((((x0).2).2).2).2).1;
    x1

def «Typing.envMs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) =>
    let x1 : _root_.List _root_.Geb.Kernel.Tree := (((((x0).2).2).2).2).2;
    x1

def «Typing.env0» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Typing.lookupName» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x5
          (_root_.Geb.Kernel.leaf 0)
          (fun (x6 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x6);
        let x7 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x5
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x7
          (_root_.Geb.Kernel.leaf 0)
          (fun (x8 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x7
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
            x10);
        if (_root_.GebMirror.DatatypeSoundness.«Typing.sameName» x6 x0).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x8
        else
          x3)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
      x1;
    x2

def «Typing.hasName» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.GebMirror.DatatypeSoundness.«Typing.sameName» x2 x0)
          x3)
      (_root_.Geb.Kernel.leaf 0)
      x1;
    x2

def «Typing.atomName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let x3 : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.GebMirror.DatatypeSoundness.«Typing.name» x3
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                            ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Typing.isAtomTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «Typing.recognizerName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.name»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 46,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 98,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 114])));
    x1

def «Typing.readAsName» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
        (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
          x1
          _root_.GebMirror.DatatypeSoundness.«Reader.reservedNames»))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x1)
            (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.leaf 37))
        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
            (_root_.GebMirror.DatatypeSoundness.«Reader.numeral»
              (_root_.Geb.Kernel.Const.children x1)))
          (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
            x1
            (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0))))).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      _root_.Geb.Kernel.leaf 1);
    x2

def «Typing.namesData» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x3)
                                          (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                          let x4 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x3;
                                          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x4
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x5 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x4
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
                                              x5
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0))
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.isAtomTx» x2)
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.sameName»
                                                  x5
                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.atomName» x2))
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.readAsName»
                                                  x0
                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.recognizerName» x5))))
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x3

def «Typing.datumAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
      (_root_.GebMirror.DatatypeSoundness.«Typing.name» x1)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
        (_root_.GebMirror.DatatypeSoundness.«Reader.numeral» x1)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 2
      else
        _root_.Geb.Kernel.leaf 1);
    x2

def «Typing.datumKids» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.and» x1 x2)
      (_root_.Geb.Kernel.leaf 1)
      x0;
    x1

def «Typing.datumList» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.leaf 2))
      (_root_.GebMirror.DatatypeSoundness.«Typing.datumKids» x0)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.Geb.Kernel.leaf 0);
    x1

def «Typing.plainDatum» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            _root_.Geb.Kernel.leaf 0,
            x3);
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
          let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
          _root_.GebMirror.DatatypeSoundness.«Typing.datumAtom» x0 x7
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x5 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              _root_.Geb.Kernel.leaf 0,
              x3);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
            let x7 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit → _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              (fun (x7 : _root_.Unit → _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                ((x7 ()) :: x8))
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (x5).2;
            _root_.GebMirror.DatatypeSoundness.«Typing.datumList» x7
          else
            _root_.Geb.Kernel.leaf 0)
      x1
      ();
    x2

def «Typing.namedTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.named»
      x0
      x1;
    x2

def «Typing.kwRep» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 112]

def «Typing.kwDecode» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101]

def «Typing.kwDatum» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 109]

def «Typing.kwSort» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 116]

def «Typing.kwPostulate» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101]

def «Typing.keywordTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwLam»)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
        (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwLet»)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwPair»)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwFst»)
            (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
              (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwSnd»)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwIf»)
                (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                  (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwCons»)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwNil»)
                    (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwQuote»)
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Typing.kwDatum»)
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                          (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Typing.kwRep»)
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                            (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Typing.kwDecode»)
                            (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                              (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwFold»)
                              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x0 _root_.GebMirror.DatatypeSoundness.«Reader.kwPara»)
                                (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                  (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                    x0
                                    _root_.GebMirror.DatatypeSoundness.«Reader.kwIter»)
                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                      x0
                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwFoldr»)
                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                      x0
                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwLcase»))))))))))))))));
    x1

def «$547970696e672f525431732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := (x0 ::
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)));
    x1

def «$547970696e672f525431732e6c656e677468» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f525431732e617070656e64» :=
  fun (x0 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f525431732e72657665727365» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) →
        _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) →
           _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x1)
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f525431732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$547970696e672f525431732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f525431732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f525431732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f525431732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (_ : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x3);
    x3

def «Typing.rtForms» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Typing.readTy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit →
            _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0),
            x3);
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
          let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
          (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7,
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.name» x7;
            if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
              (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7)
              _root_.GebMirror.DatatypeSoundness.«Reader.kwT»).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
            else
              if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7)
                _root_.GebMirror.DatatypeSoundness.«Reader.kwUnit»).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                  _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit»
              else
                let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.lookupName»
                  x8
                  (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0);
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x9)
                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                  let x10 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x9;
                  let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.Geb.Kernel.Tree)
                    x10
                    (_root_.Geb.Kernel.leaf 0)
                    (fun (x11 : _root_.Geb.Kernel.Tree)
                       (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                      x11);
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.List _root_.Geb.Kernel.Tree)
                    x10
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (fun (_ : _root_.Geb.Kernel.Tree)
                       (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                      x13);
                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x11
                else
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x9;
                  if (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
                    x8
                    (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                      (_root_.GebMirror.DatatypeSoundness.«Typing.tyData» x8)
                  else
                    if (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
                      x8
                      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.tySort» x8)
                    else
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x5 : (_root_.Unit →
              _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0),
              x3);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
            let x7 : _root_.List
              (_root_.Geb.Kernel.Tree ×
                _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
              (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
              (fun (x7 : _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List
                   (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
                ((x7 ()) :: x8))
              ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
              (x5).2;
            let x8 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.rtForms» x7;
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f525431732e6c656e677468»
              x7;
            let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
              _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
              x8
              (_root_.Geb.Kernel.leaf 0);
            let x11 : _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x11 : _root_.Geb.Kernel.Tree) =>
              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f525431732e61744f72»
                (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
                x7
                x11).2);
            (_root_.GebMirror.DatatypeSoundness.«Typing.tList» x8,
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x10 _root_.GebMirror.DatatypeSoundness.«Reader.kwProd»)
                (_root_.Geb.Kernel.Const.eq
                  x9
                  (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                let x12 : _root_.Geb.Kernel.Tree := x11 (_root_.Geb.Kernel.leaf 1);
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x12)
                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                  let x13 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                  let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.Geb.Kernel.Tree)
                    x13
                    (_root_.Geb.Kernel.leaf 0)
                    (fun (x14 : _root_.Geb.Kernel.Tree)
                       (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                      x14);
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                    (α := _root_.Geb.Kernel.Tree)
                    (β := _root_.List _root_.Geb.Kernel.Tree)
                    x13
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (fun (_ : _root_.Geb.Kernel.Tree)
                       (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                      x16);
                  let x16 : _root_.Geb.Kernel.Tree := x11 (_root_.Geb.Kernel.leaf 2);
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x16)
                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                    let x17 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                    let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.Geb.Kernel.Tree)
                      x17
                      (_root_.Geb.Kernel.leaf 0)
                      (fun (x18 : _root_.Geb.Kernel.Tree)
                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        x18);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      x17
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (fun (_ : _root_.Geb.Kernel.Tree)
                         (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                        x20);
                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                      (_root_.GebMirror.DatatypeSoundness.«Typing.tyProd» x14 x18)
                  else
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                else
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
              else
                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                  (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x10 _root_.GebMirror.DatatypeSoundness.«Reader.kwArrow»)
                  (_root_.Geb.Kernel.Const.eq
                    x9
                    (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                  let x12 : _root_.Geb.Kernel.Tree := x11 (_root_.Geb.Kernel.leaf 1);
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x12)
                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                    let x13 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                    let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.Geb.Kernel.Tree)
                      x13
                      (_root_.Geb.Kernel.leaf 0)
                      (fun (x14 : _root_.Geb.Kernel.Tree)
                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        x14);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      x13
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (fun (_ : _root_.Geb.Kernel.Tree)
                         (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                        x16);
                    let x16 : _root_.Geb.Kernel.Tree := x11 (_root_.Geb.Kernel.leaf 2);
                    if (_root_.Geb.Kernel.Const.eq
                      (_root_.Geb.Kernel.Const.label x16)
                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                      let x17 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                      let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        x17
                        (_root_.Geb.Kernel.leaf 0)
                        (fun (x18 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          x18);
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.List _root_.Geb.Kernel.Tree)
                        x17
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (fun (_ : _root_.Geb.Kernel.Tree)
                           (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                          x20);
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» x14 x18)
                    else
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                  else
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx» x10 _root_.GebMirror.DatatypeSoundness.«Reader.kwList»)
                    (_root_.Geb.Kernel.Const.eq
                      x9
                      (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                    let x12 : _root_.Geb.Kernel.Tree := x11 (_root_.Geb.Kernel.leaf 1);
                    if (_root_.Geb.Kernel.Const.eq
                      (_root_.Geb.Kernel.Const.label x12)
                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                      let x13 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                      let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        x13
                        (_root_.Geb.Kernel.leaf 0)
                        (fun (x14 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          x14);
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.List _root_.Geb.Kernel.Tree)
                        x13
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (fun (_ : _root_.Geb.Kernel.Tree)
                           (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                          x16);
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x14)
                    else
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                  else
                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
          else
            (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))
      x1
      ()).2;
    x2

def «$547970696e672f5473732e73696e676c65» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := (x0 ::
      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree)));
    x1

def «$547970696e672f5473732e6c656e677468» :=
  fun (x0 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f5473732e617070656e64» :=
  fun (x0 : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f5473732e72657665727365» :=
  fun (x0 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
        _root_.List (_root_.List _root_.Geb.Kernel.Tree))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
           _root_.List (_root_.List _root_.Geb.Kernel.Tree))
         (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) => x1)
      x0
      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree));
    x1

def «$547970696e672f5473732e7461696c» :=
  fun (x0 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$547970696e672f5473732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f5473732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f5473732e61744f72» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5473732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
         (_ : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        x3);
    x3

def «Typing.markerNames» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)) :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Typing.fieldOk» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                          x1
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.markerNames» x0);
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                            x2
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)
                                        else
                                          _root_.Geb.Kernel.leaf 1);
    x3

def «Typing.ctorOk» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
        x2)
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
          _root_.Geb.Kernel.Tree)
        (fun (x4 : _root_.Geb.Kernel.Tree)
           (x5 : _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
             _root_.Geb.Kernel.Tree)
           (x6 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.List _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x6
            (_root_.Geb.Kernel.leaf 0)
            (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
               (x8 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
              _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (_root_.GebMirror.DatatypeSoundness.«Typing.fieldOk» x0 x4 x7)
                (x5 x8)))
        (fun (x4 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          if (_root_.Geb.Kernel.Const.child
            x1
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            _root_.Geb.Kernel.Const.foldr
              (α := _root_.List _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                 (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                  (_root_.GebMirror.DatatypeSoundness.«Typing.fieldOk»
                    x0
                    (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 3))
                    x5)
                  x6)
              (_root_.Geb.Kernel.leaf 1)
              x4
          else
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.List _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x4
              (_root_.Geb.Kernel.leaf 1)
              (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
                 (_ : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                _root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))
        x3);
    x4

def «Typing.memberships» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x4 : _root_.Geb.Kernel.Tree)
             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
            ((_root_.Geb.Kernel.Const.foldr
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              (fun (x6 : _root_.Geb.Kernel.Tree) (x7 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Prelude.or»
                  (_root_.GebMirror.DatatypeSoundness.«Typing.ctorOk» x0 x6 x2 x3)
                  x7)
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.tail»
                (_root_.Geb.Kernel.Const.children x4))) ::
              x5))
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x0)
      x1;
    x2

def «Typing.memberOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                          x1
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.markerNames» x0);
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.memberships» x0 x2)
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x3

def «$547970696e672f5352732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := (x0 ::
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))));
    x1

def «$547970696e672f5352732e6c656e677468» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$547970696e672f5352732e617070656e64» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$547970696e672f5352732e72657665727365» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
        _root_.List
          (_root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
           _root_.List
             (_root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x1)
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)));
    x1

def «$547970696e672f5352732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2);
    x1

def «$547970696e672f5352732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e7461696c»
      x1
      x0;
    x2

def «$547970696e672f5352732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (_ : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x3);
    x3

def «Typing.srForms» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Typing.srAt» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e61744f72»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
        fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
      x0
      x1).2
      x2;
    x3

def «Typing.srFrom» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        (((x3).2 x2) :: x4))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e64726f70» x1 x0);
    x3

def «Typing.applyTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x3;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x4)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x5
            (_root_.Geb.Kernel.leaf 0)
            (fun (x6 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x6);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let x8 : _root_.Geb.Kernel.Tree := x6;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x8)
            (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
            let x9 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
            let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x9
              (_root_.Geb.Kernel.leaf 0)
              (fun (x10 : _root_.Geb.Kernel.Tree)
                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                x10);
            let x11 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x9
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                x12);
            let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x11
              (_root_.Geb.Kernel.leaf 0)
              (fun (x12 : _root_.Geb.Kernel.Tree)
                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                x12);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x11
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                x14);
            let x14 : _root_.Geb.Kernel.Tree := x2;
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x14)
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              let x15 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x14;
              let x16 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x15
                (_root_.Geb.Kernel.leaf 0)
                (fun (x16 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x16);
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x15
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x18 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x18);
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.arity x6)
                  (_root_.Geb.Kernel.leaf 2))
                (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy» x10 x16)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x12
              else
                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
            else
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x14;
              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
          else
            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
      x0
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4d5479732e72657665727365» x1);
    x2

def «Typing.isRecognizer» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.GebMirror.DatatypeSoundness.«Typing.sameName»
            x1
            (_root_.GebMirror.DatatypeSoundness.«Typing.recognizerName» x2))
          x3)
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x2

def «Typing.nameOk» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.Geb.Kernel.Const.equal x1 _root_.GebMirror.DatatypeSoundness.«Typing.kwRep»)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
        (_root_.Geb.Kernel.Const.equal x1 _root_.GebMirror.DatatypeSoundness.«Typing.kwDecode»)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.Geb.Kernel.Const.equal x1 _root_.GebMirror.DatatypeSoundness.«Typing.kwDatum»)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.Geb.Kernel.Const.equal x1 _root_.GebMirror.DatatypeSoundness.«Reader.kwUnitValue»)
            (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
              (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                  x1
                  _root_.GebMirror.DatatypeSoundness.«Reader.primNames»))
              (_root_.GebMirror.DatatypeSoundness.«Typing.isRecognizer»
                (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
                x1)))))).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      _root_.Geb.Kernel.leaf 1);
    x2

def «Typing.kwDecoded» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 101]

def «Typing.kwScrutinee» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 115]

def «Typing.kwNode» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 111]

def «Typing.kwResults» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 107]

def «Typing.kwUnitArg» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 117]

def «Typing.kwFields» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 99]

def «Typing.kwSplit» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 113]

def «Typing.boundNames» :=
  (_root_.GebMirror.DatatypeSoundness.«Typing.kwDecoded» ::
    (_root_.GebMirror.DatatypeSoundness.«Typing.kwScrutinee» ::
      (_root_.GebMirror.DatatypeSoundness.«Typing.kwNode» ::
        (_root_.GebMirror.DatatypeSoundness.«Typing.kwResults» ::
          (_root_.GebMirror.DatatypeSoundness.«Typing.kwUnitArg» ::
            (_root_.GebMirror.DatatypeSoundness.«Typing.kwFields» ::
              (_root_.GebMirror.DatatypeSoundness.«Typing.kwSplit» ::
                ([] : _root_.List _root_.Geb.Kernel.Tree))))))))

def «Typing.decimalChars» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.Geb.Kernel.leaf 48)
    else
      let x1 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.iter
        (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
        (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.eq
            (x1).2
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            x1
          else
            (_root_.Geb.Kernel.Const.add (x1).1 (_root_.Geb.Kernel.leaf 1),
              _root_.Geb.Kernel.Const.div (x1).2 (_root_.Geb.Kernel.leaf 10)))
        (_root_.Geb.Kernel.leaf 0, x0)
        (_root_.Geb.Kernel.Const.add
          (_root_.Geb.Kernel.Const.log2 x0)
          (_root_.Geb.Kernel.leaf 1))).1;
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((_root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 48)) :: x3))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.digitsMsb»
          (_root_.Geb.Kernel.leaf 10)
          x0
          x1));
    x1

def «Typing.boundName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.name»
      (_root_.Geb.Kernel.Const.children x0);
    x1

def «Typing.binderName» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.GebMirror.DatatypeSoundness.«Typing.isAtomTx» x1)
      (_root_.GebMirror.DatatypeSoundness.«Typing.nameOk»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Typing.atomName» x1));
    x2

def «$547970696e672f4f416262722e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$547970696e672f4f416262722e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$547970696e672f4f416262722e69734a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$547970696e672f4f416262722e66726f6d4d61796265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$547970696e672f4f416262722e6e74684f66» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6a757374» x2);
    x2

def «$547970696e672f4f416262722e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «Typing.bindersOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                                                if (_root_.Geb.Kernel.Const.eq
                                                                  (_root_.Geb.Kernel.Const.label x2)
                                                                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                                  let x3 : _root_.List
                                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                    x2;
                                                                  let x4 : _root_.List
                                                                    _root_.Geb.Kernel.Tree := x3;
                                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e6c656e677468»
                                                                        x4)
                                                                      (_root_.Geb.Kernel.leaf 2))
                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.isAtomTx»
                                                                      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                                        x4
                                                                        (_root_.Geb.Kernel.leaf 0)))).label ≠ 0 then
                                                                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e73696e676c65»
                                                                      x1
                                                                  else
                                                                    x4
                                                                else
                                                                  ([] : _root_.List _root_.Geb.Kernel.Tree));
                                   _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e616c6c4a757374»
                                     (_root_.Geb.Kernel.Const.foldr
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (x3 : _root_.Geb.Kernel.Tree)
                                          (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         ((let x5 : _root_.Geb.Kernel.Tree := x3;
                                           if (_root_.Geb.Kernel.Const.eq
                                             (_root_.Geb.Kernel.Const.label x5)
                                             (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                             let x6 : _root_.List
                                               _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                               x5;
                                             let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
                                             if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                               (_root_.Geb.Kernel.Const.eq
                                                 (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e6c656e677468»
                                                   x7)
                                                 (_root_.Geb.Kernel.leaf 2))
                                               (_root_.GebMirror.DatatypeSoundness.«Typing.binderName»
                                                 x0
                                                 (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                   _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                   x7
                                                   (_root_.Geb.Kernel.leaf 0)))).label ≠ 0 then
                                               let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                 x0
                                                 (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                   _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                   x7
                                                   (_root_.Geb.Kernel.leaf 1));
                                               if (_root_.Geb.Kernel.Const.eq
                                                 (_root_.Geb.Kernel.Const.label x8)
                                                 (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                 let x9 : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                   x8;
                                                 let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.Geb.Kernel.Tree)
                                                   x9
                                                   (_root_.Geb.Kernel.leaf 0)
                                                   (fun (x10 : _root_.Geb.Kernel.Tree)
                                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                     x10);
                                                 let _ : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                                   x9
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                                      (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                     x12);
                                                 _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6a757374»
                                                   (_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                     (_root_.GebMirror.DatatypeSoundness.«Typing.atomName»
                                                       (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                         _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                         x7
                                                         (_root_.Geb.Kernel.leaf 0)))
                                                     x10)
                                               else
                                                 let _ : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                   x8;
                                                 _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6e6f7468696e67»
                                             else
                                               _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6e6f7468696e67»
                                           else
                                             _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f416262722e6e6f7468696e67») ::
                                           x4))
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       x2));
    x2

def «Typing.synAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                          x1;
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.keywordTx»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x1))
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                            (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                              x3
                                              _root_.GebMirror.DatatypeSoundness.«Typing.boundNames»))).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                            (_root_.GebMirror.DatatypeSoundness.«Reader.numeral» x1)).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                              _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
                                          else
                                            if (_root_.GebMirror.DatatypeSoundness.«Typing.hasName»
                                              x3
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
                                            else
                                              let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.lookupName»
                                                x3
                                                x2;
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x4)
                                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                let x5 : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x4;
                                                let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.Geb.Kernel.Tree)
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (fun (x6 : _root_.Geb.Kernel.Tree)
                                                     (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x6);
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x5
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x8);
                                                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x6
                                              else
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x4;
                                                let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.lookupName»
                                                  x3
                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0);
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x6)
                                                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                  let x7 : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x6;
                                                  let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.Geb.Kernel.Tree)
                                                    x7
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (fun (x8 : _root_.Geb.Kernel.Tree)
                                                       (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x8);
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.List _root_.Geb.Kernel.Tree)
                                                    x7
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (fun (_ : _root_.Geb.Kernel.Tree)
                                                       (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x10);
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                    x8
                                                else
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x6;
                                                  let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                                    x3
                                                    _root_.GebMirror.DatatypeSoundness.«Reader.primNames»;
                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                                    x8).label ≠ 0 then
                                                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5479732e61744f72»
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.primTys»
                                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x8))
                                                  else
                                                    if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x1)
                                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwUnitValue»).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit»
                                                    else
                                                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x3

def «Typing.both2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x3)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x4 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x3;
                                          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x4
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x5 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x4
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x7 : _root_.Geb.Kernel.Tree := x1;
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x7)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x8 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x7;
                                            let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x8
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x9 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x9);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x8
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x11);
                                            x2 x5 x9
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x7;
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x3;
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x3

def «Typing.then1» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x1 x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x2

def «Typing.when» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (x0).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x1
    else
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x2

def «Typing.synList» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e6c656e677468»
                                          x2;
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                          _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                          x1
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x6 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                            x1
                                            x6);
                                        let x7 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                          _root_.GebMirror.DatatypeSoundness.«Typing.srAt» x2 x7 x3);
                                        if (_root_.Geb.Kernel.Const.eq
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                              x5
                                              _root_.GebMirror.DatatypeSoundness.«Reader.kwLam»)
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                            let x8 : _root_.Geb.Kernel.Tree ×
                                              _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.bindersOf»
                                              x0
                                              (x6 (_root_.Geb.Kernel.leaf 1));
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (x8).1
                                              (_root_.Geb.Kernel.Const.lt
                                                (_root_.Geb.Kernel.leaf 0)
                                                (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e6c656e677468»
                                                  (x8).2))).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 2)
                                                  (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e617070656e64»
                                                    (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e72657665727365»
                                                      (x8).2)
                                                    x3))
                                                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                    (_root_.Geb.Kernel.Const.foldr
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.Geb.Kernel.Tree)
                                                      (fun (x10 : _root_.Geb.Kernel.Tree)
                                                         (x11 : _root_.Geb.Kernel.Tree) =>
                                                        let x12 : _root_.Geb.Kernel.Tree := x10;
                                                        let x13 : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                          x12;
                                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.Geb.Kernel.Tree)
                                                          x13
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          (fun (x14 : _root_.Geb.Kernel.Tree)
                                                             (_ : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x14);
                                                        let x15 : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                                          x13
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                                             (x16 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x16);
                                                        let x16 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.Geb.Kernel.Tree)
                                                          x15
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          (fun (x16 : _root_.Geb.Kernel.Tree)
                                                             (_ : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x16);
                                                        let _ : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                                          x15
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                                             (x18 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x18);
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow» x16 x11)
                                                      x9
                                                      (x8).2))
                                            else
                                              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                          else
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                x5
                                                _root_.GebMirror.DatatypeSoundness.«Reader.kwLet»)
                                              (_root_.Geb.Kernel.Const.eq
                                                x4
                                                (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                  x0
                                                  (x6 (_root_.Geb.Kernel.leaf 2)))
                                                (x7 (_root_.Geb.Kernel.leaf 3))
                                                (fun (x8 : _root_.Geb.Kernel.Tree)
                                                   (x9 : _root_.Geb.Kernel.Tree) =>
                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.binderName»
                                                      x0
                                                      (x6 (_root_.Geb.Kernel.leaf 1)))
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                      x8
                                                      x9)).label ≠ 0 then
                                                    _root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 4)
                                                      ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.atomName»
                                                          (x6 (_root_.Geb.Kernel.leaf 1)))
                                                        x8) ::
                                                        x3)
                                                  else
                                                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
                                            else
                                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                  x5
                                                  _root_.GebMirror.DatatypeSoundness.«Reader.kwPair»)
                                                (_root_.Geb.Kernel.Const.eq
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                                _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                  (x7 (_root_.Geb.Kernel.leaf 1))
                                                  (x7 (_root_.Geb.Kernel.leaf 2))
                                                  (fun (x8 : _root_.Geb.Kernel.Tree)
                                                     (x9 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.tyProd» x8 x9))
                                              else
                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                      x5
                                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwFst»)
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                      x5
                                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwSnd»))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                  _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                    (x7 (_root_.Geb.Kernel.leaf 1))
                                                    (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                      let x9 : _root_.Geb.Kernel.Tree := x8;
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        (_root_.Geb.Kernel.Const.label x9)
                                                        (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                        let x10 : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                          x9;
                                                        let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.Geb.Kernel.Tree)
                                                          x10
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                                             (_ : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x11);
                                                        let x12 : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                                          x10
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                                             (x13 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x13);
                                                        let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.Geb.Kernel.Tree)
                                                          x12
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                                             (_ : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x13);
                                                        let _ : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                                          x12
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                                             (x15 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x15);
                                                        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                          (if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                            x5
                                                            _root_.GebMirror.DatatypeSoundness.«Reader.kwFst»).label ≠ 0 then
                                                            x11
                                                          else
                                                            x13)
                                                      else
                                                        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
                                                else
                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                      x5
                                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwIf»)
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 4))).label ≠ 0 then
                                                    _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                      (x7 (_root_.Geb.Kernel.leaf 1))
                                                      (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                          (x7 (_root_.Geb.Kernel.leaf 2))
                                                          (x7 (_root_.Geb.Kernel.leaf 3))
                                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                                             (x10 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                                  x8
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)
                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                                  x9
                                                                  x10))
                                                              x9))
                                                  else
                                                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                        x5
                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwCons»)
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x4
                                                        (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                        (x7 (_root_.Geb.Kernel.leaf 1))
                                                        (x7 (_root_.Geb.Kernel.leaf 2))
                                                        (fun (x8 : _root_.Geb.Kernel.Tree)
                                                           (x9 : _root_.Geb.Kernel.Tree) =>
                                                          _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x8)
                                                              x9)
                                                            x9)
                                                    else
                                                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                          x5
                                                          _root_.GebMirror.DatatypeSoundness.«Reader.kwNil»)
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                            x0
                                                            (x6 (_root_.Geb.Kernel.leaf 1)))
                                                          (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x8))
                                                      else
                                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                            x5
                                                            _root_.GebMirror.DatatypeSoundness.«Reader.kwQuote»)
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x4
                                                            (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.tyT»
                                                        else
                                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                              x5
                                                              _root_.GebMirror.DatatypeSoundness.«Typing.kwDatum»)
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x4
                                                              (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                                x0
                                                                (x6 (_root_.Geb.Kernel.leaf 1)))
                                                              (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                                let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readDatum»
                                                                  (x6 (_root_.Geb.Kernel.leaf 2));
                                                                _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namesData»
                                                                      x0
                                                                      x8
                                                                      (x6
                                                                        (_root_.Geb.Kernel.leaf 1)))
                                                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                                                        x9)
                                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.plainDatum»
                                                                          x0
                                                                          (x6
                                                                            (_root_.Geb.Kernel.leaf 2)))
                                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.memberOf»
                                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.envMs»
                                                                            x0)
                                                                          (x6
                                                                            (_root_.Geb.Kernel.leaf 1))
                                                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.get»
                                                                            x9)))))
                                                                  x8)
                                                          else
                                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                x5
                                                                _root_.GebMirror.DatatypeSoundness.«Typing.kwRep»)
                                                              (_root_.Geb.Kernel.Const.eq
                                                                x4
                                                                (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                              _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                                (x7 (_root_.Geb.Kernel.leaf 1))
                                                                (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.isData»
                                                                      x8)
                                                                    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)
                                                            else
                                                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                  x5
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.kwDecode»)
                                                                (_root_.Geb.Kernel.Const.eq
                                                                  x4
                                                                  (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
                                                                _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                                    x0
                                                                    (x6 (_root_.Geb.Kernel.leaf 1)))
                                                                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                                    _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                                      (x7
                                                                        (_root_.Geb.Kernel.leaf 2))
                                                                      (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                                        _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                                            x2
                                                                            (_root_.Geb.Kernel.leaf 3)
                                                                            ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                                                _root_.GebMirror.DatatypeSoundness.«Typing.kwDecoded»)
                                                                              _root_.GebMirror.DatatypeSoundness.«Typing.tyT») ::
                                                                              x3))
                                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                                            x2
                                                                            (_root_.Geb.Kernel.leaf 4)
                                                                            ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                                                _root_.GebMirror.DatatypeSoundness.«Typing.kwDecoded»)
                                                                              _root_.GebMirror.DatatypeSoundness.«Typing.tyT») ::
                                                                              x3))
                                                                          (fun (x10 : _root_.Geb.Kernel.Tree)
                                                                             (x11 : _root_.Geb.Kernel.Tree) =>
                                                                            _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.namesData»
                                                                                  x0
                                                                                  x8
                                                                                  (x6
                                                                                    (_root_.Geb.Kernel.leaf 1)))
                                                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                                                    x9
                                                                                    _root_.GebMirror.DatatypeSoundness.«Typing.tyT»)
                                                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                                                    x10
                                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
                                                                                      x8
                                                                                      x11))))
                                                                              x11)))
                                                              else
                                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                      x5
                                                                      _root_.GebMirror.DatatypeSoundness.«Reader.kwFold»)
                                                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                        x5
                                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwPara»)
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                        x5
                                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwIter»)))
                                                                  (_root_.Geb.Kernel.Const.lt
                                                                    (_root_.Geb.Kernel.leaf 1)
                                                                    x4)).label ≠ 0 then
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                                      x0
                                                                      (x6
                                                                        (_root_.Geb.Kernel.leaf 1)))
                                                                    (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                                      _root_.GebMirror.DatatypeSoundness.«Typing.applyTy»
                                                                        (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                                          (if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                            x5
                                                                            _root_.GebMirror.DatatypeSoundness.«Reader.kwIter»).label ≠ 0 then
                                                                            _root_.GebMirror.DatatypeSoundness.«Typing.iterTyOf»
                                                                              x8
                                                                          else
                                                                            _root_.GebMirror.DatatypeSoundness.«Typing.foldTyOf»
                                                                              x8))
                                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.srFrom»
                                                                          x2
                                                                          (_root_.Geb.Kernel.leaf 2)
                                                                          x3))
                                                                else
                                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                        x5
                                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwFoldr»)
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                        x5
                                                                        _root_.GebMirror.DatatypeSoundness.«Reader.kwLcase»))
                                                                    (_root_.Geb.Kernel.Const.lt
                                                                      (_root_.Geb.Kernel.leaf 2)
                                                                      x4)).label ≠ 0 then
                                                                    _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                                        x0
                                                                        (x6
                                                                          (_root_.Geb.Kernel.leaf 1)))
                                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                                        x0
                                                                        (x6
                                                                          (_root_.Geb.Kernel.leaf 2)))
                                                                      (fun (x8 : _root_.Geb.Kernel.Tree)
                                                                         (x9 : _root_.Geb.Kernel.Tree) =>
                                                                        _root_.GebMirror.DatatypeSoundness.«Typing.applyTy»
                                                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                                            (if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                                              x5
                                                                              _root_.GebMirror.DatatypeSoundness.«Reader.kwFoldr»).label ≠ 0 then
                                                                              _root_.GebMirror.DatatypeSoundness.«Typing.foldrTyOf»
                                                                                x8
                                                                                x9
                                                                            else
                                                                              _root_.GebMirror.DatatypeSoundness.«Typing.lcaseTyOf»
                                                                                x8
                                                                                x9))
                                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.srFrom»
                                                                            x2
                                                                            (_root_.Geb.Kernel.leaf 3)
                                                                            x3))
                                                                  else
                                                                    if (_root_.GebMirror.DatatypeSoundness.«Typing.keywordTx»
                                                                      x5).label ≠ 0 then
                                                                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                                                    else
                                                                      _root_.GebMirror.DatatypeSoundness.«Typing.applyTy»
                                                                        (x7
                                                                          (_root_.Geb.Kernel.leaf 0))
                                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.srFrom»
                                                                          x2
                                                                          (_root_.Geb.Kernel.leaf 1)
                                                                          x3));
    x4

def «Typing.elemsTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x1)
                                   (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                   let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                   let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3
                                 else
                                   ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Typing.numTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let x3 : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.GebMirror.DatatypeSoundness.«Reader.numeral» x3
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x1

def «Typing.markerCtors» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                     x1
                                     (_root_.GebMirror.DatatypeSoundness.«Typing.markerNames» x0);
                                   if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x2).label ≠ 0 then
                                     (_root_.Geb.Kernel.leaf 1,
                                       _root_.GebMirror.DatatypeSoundness.«Prelude.tail»
                                         (_root_.Geb.Kernel.Const.children
                                           (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                             _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                             x0
                                             (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x2))))
                                   else
                                     (_root_.Geb.Kernel.leaf 0,
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «Typing.fieldTy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.GebMirror.DatatypeSoundness.«Typing.Tx.member» x2).label ≠ 0 then
                                          let x3 : _root_.Geb.Kernel.Tree := x2;
                                          _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x0 x3)
                                            (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                              let x5 : _root_.Geb.Kernel.Tree := x4;
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x5)
                                                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x5;
                                                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374» x4
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x5)
                                                  (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                                  let x6 : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x5;
                                                  let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.Geb.Kernel.Tree)
                                                    x6
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (fun (x7 : _root_.Geb.Kernel.Tree)
                                                       (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x7);
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.List _root_.Geb.Kernel.Tree)
                                                    x6
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (fun (_ : _root_.Geb.Kernel.Tree)
                                                       (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x9);
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                    x4
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    (_root_.Geb.Kernel.Const.label x5)
                                                    (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                                    let x6 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x5;
                                                    let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.Geb.Kernel.Tree)
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 0)
                                                      (fun (x7 : _root_.Geb.Kernel.Tree)
                                                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                        x7);
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.List _root_.Geb.Kernel.Tree)
                                                      x6
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (fun (_ : _root_.Geb.Kernel.Tree)
                                                         (x9 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x9);
                                                    _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.namesData» x0 x4 x3)
                                                        (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                                          (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
                                                            x3
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.markerNames»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0)))))
                                                      x4
                                                  else
                                                    _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x2

def «Typing.clauseVar» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.GebMirror.DatatypeSoundness.«Typing.binderName» x0 x1)
      (if (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
          (_root_.Geb.Kernel.Const.children x1)
          (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.leaf 37)).label ≠ 0 then
        _root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x1)
            (_root_.Geb.Kernel.leaf 1))
          (_root_.Geb.Kernel.leaf 37)
      else
        _root_.Geb.Kernel.leaf 1);
    x2

def «Typing.sameAll» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.then1»
      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4d5479732e61744f72»
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
        x0
        (_root_.Geb.Kernel.leaf 0))
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Typing.when»
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (let x4 : _root_.Geb.Kernel.Tree := x2;
                 if (_root_.Geb.Kernel.Const.eq
                   (_root_.Geb.Kernel.Const.label x4)
                   (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                   let x5 : _root_.List
                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
                   let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                     (α := _root_.Geb.Kernel.Tree)
                     (β := _root_.Geb.Kernel.Tree)
                     x5
                     (_root_.Geb.Kernel.leaf 0)
                     (fun (x6 : _root_.Geb.Kernel.Tree)
                        (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                       x6);
                   let _ : _root_.List
                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                     (α := _root_.Geb.Kernel.Tree)
                     (β := _root_.List _root_.Geb.Kernel.Tree)
                     x5
                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                     (fun (_ : _root_.Geb.Kernel.Tree)
                        (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                       x8);
                   _root_.GebMirror.DatatypeSoundness.«Typing.sameTy» x6 x1
                 else
                   let _ : _root_.List
                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
                   _root_.Geb.Kernel.leaf 0)
                x3)
            (_root_.Geb.Kernel.leaf 1)
            x0)
          x1);
    x1

def «Typing.bindVar» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.then1»
      x2
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.DatatypeSoundness.«Typing.clauseVar» x0 x1).label ≠ 0 then
          x3
            (_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
              (_root_.GebMirror.DatatypeSoundness.«Typing.atomName» x1)
              x4)
        else
          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x4

def «Typing.fieldScope» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
      x0
      (_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 95])).label ≠ 0 then
      x2
    else
      (x1 :: x2));
    x3

def «Typing.bindRest» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        x1
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
        (fun (x5 : _root_.Geb.Kernel.Tree)
           (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x6
            (x2 x5 (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 3)))
            (fun (_ : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))
    else
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        x1
        (x3 x4)
        (fun (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»));
    x5

def «Typing.caseFields» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                          x2;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.kwFields»)
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.tyList»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.tyT»);
                                        _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.List _root_.Geb.Kernel.Tree →
                                              _root_.Geb.Kernel.Tree)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.List _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x9
                                              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                              (fun (x11 : _root_.Geb.Kernel.Tree)
                                                 (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«Typing.bindVar»
                                                  x0
                                                  x7
                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.fieldTy» x0 x11)
                                                  (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                    x8
                                                      x12
                                                      (x6 ::
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.fieldScope»
                                                          x7
                                                          x13
                                                          x10)))))
                                          (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x7
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.bindRest»
                                                x1
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                                  (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                    _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 2)))
                                                (fun (x9 : _root_.Geb.Kernel.Tree)
                                                   (x10 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.DatatypeSoundness.«Typing.bindVar»
                                                    x0
                                                    x9
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.fieldTy» x0 x10)
                                                      (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x11)))
                                                    (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                      x3
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.fieldScope»
                                                          x9
                                                          x11
                                                          x8)))
                                                x3
                                                x8)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                            (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                              _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                              x5
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.Geb.Kernel.Const.child
                                              x1
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (x6 :: x4));
    x5

def «Typing.cataFields» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := (let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                          x4;
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
                                          _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit»
                                          x2;
                                        let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.kwSplit»)
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.tyProd»
                                            x8
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.tyList» x8));
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.kwFields»)
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.tyList»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.tyT»);
                                        let x11 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree →
                                            (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                                              (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                                                _root_.Geb.Kernel.Tree := (fun (x11 : _root_.Geb.Kernel.Tree)
                                                                             (x12 : _root_.Geb.Kernel.Tree)
                                                                             (x13 : _root_.Geb.Kernel.Tree →
                                                                               _root_.Geb.Kernel.Tree)
                                                                             (x14 : _root_.Geb.Kernel.Tree →
                                                                               _root_.Geb.Kernel.Tree) =>
                                          let x15 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                            x11;
                                          let x16 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.equal
                                            x12
                                            x1;
                                          let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.numTx»
                                            (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                              _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                              x15
                                              (_root_.Geb.Kernel.leaf 1));
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x17)
                                            (_root_.Geb.Kernel.Const.eq
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x17)
                                              x16)).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Typing.bindVar»
                                              x0
                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                x15
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                (if (x16).label ≠ 0 then
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                    x2
                                                else
                                                  _root_.GebMirror.DatatypeSoundness.«Typing.fieldTy» x0 x12)
                                                (fun (x18 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6a757374»
                                                    (x13 x18)))
                                              x14
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
                                        _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.List _root_.Geb.Kernel.Tree →
                                              _root_.Geb.Kernel.Tree)
                                          (fun (x12 : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.List _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree)
                                             (x14 : _root_.List _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x14
                                              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                              (fun (x16 : _root_.Geb.Kernel.Tree)
                                                 (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x11
                                                  x12
                                                  x16
                                                  (fun (x18 : _root_.Geb.Kernel.Tree) => x18)
                                                  (fun (x18 : _root_.Geb.Kernel.Tree) =>
                                                    x13
                                                      x17
                                                      (x10 ::
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.fieldScope»
                                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx» x12)
                                                            (_root_.Geb.Kernel.leaf 0))
                                                          x18
                                                          (x9 :: x15))))))
                                          (fun (x12 : _root_.List _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x12
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.bindRest»
                                                x3
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                                  (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                    _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                    x7
                                                    (_root_.Geb.Kernel.leaf 2)))
                                                (fun (x14 : _root_.Geb.Kernel.Tree)
                                                   (x15 : _root_.Geb.Kernel.Tree) =>
                                                  x11
                                                    x14
                                                    x15
                                                    (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.DatatypeSoundness.«Typing.tyList» x16)
                                                    (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                                      x5
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.fieldScope»
                                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx» x14)
                                                            (_root_.Geb.Kernel.leaf 0))
                                                          x16
                                                          x13)))
                                                x5
                                                x13)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                            (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                              _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                              x7
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.Geb.Kernel.Const.child
                                              x3
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (x10 :: (x9 :: x6)));
    x7

def «Typing.clauseTy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.numTx»
                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                            _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                            (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx» x1)
                                            (_root_.Geb.Kernel.leaf 0));
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x5).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.child
                                                  x6
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x5)).label ≠ 0 then
                                                (x6 :: x7)
                                              else
                                                x7)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            x0;
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x6)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            x2
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                                x6
                                                (_root_.Geb.Kernel.leaf 0))
                                              x1
                                              (x3).2
                                              x4
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x5

def «Typing.clausesTy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e6c656e677468»
                                          x1;
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lt
                                          x6
                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e6c656e677468» x2);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e617070656e64»
                                          x4
                                          x3;
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.numTx»
                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx» x9)
                                                (_root_.Geb.Kernel.leaf 0));
                                            ((if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                              x11).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Prelude.get» x11
                                            else
                                              _root_.Geb.Kernel.leaf 0) ::
                                              x10))
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          x1;
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                          x7
                                          (_root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (x11 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.foldr
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.Geb.Kernel.Tree)
                                                  (fun (x12 : _root_.Geb.Kernel.Tree)
                                                     (x13 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x12
                                                        (_root_.Geb.Kernel.Const.child
                                                          x10
                                                          (_root_.Geb.Kernel.leaf 0)))
                                                      x13)
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  x9)
                                                x11)
                                            (_root_.Geb.Kernel.leaf 1)
                                            x0);
                                        let x11 : _root_.Geb.Kernel.Tree ×
                                          (_root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree) := (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
                                          fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List
                                            (_root_.Geb.Kernel.Tree ×
                                              (_root_.List _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree)) →
                                            _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (x12 : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List
                                               (_root_.Geb.Kernel.Tree ×
                                                 (_root_.List _root_.Geb.Kernel.Tree →
                                                   _root_.Geb.Kernel.Tree)) →
                                               _root_.List _root_.Geb.Kernel.Tree)
                                             (x14 : _root_.List
                                               (_root_.Geb.Kernel.Tree ×
                                                 (_root_.List _root_.Geb.Kernel.Tree →
                                                   _root_.Geb.Kernel.Tree))) =>
                                            ((_root_.GebMirror.DatatypeSoundness.«Typing.clauseTy»
                                              x0
                                              x12
                                              x5
                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e61744f72»
                                                x11
                                                x14
                                                (_root_.Geb.Kernel.leaf 0))
                                              x8) ::
                                              (x13
                                                (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e7461696c»
                                                  x14))))
                                          (fun (x12 : _root_.List
                                               (_root_.Geb.Kernel.Tree ×
                                                 (_root_.List _root_.Geb.Kernel.Tree →
                                                   _root_.Geb.Kernel.Tree))) =>
                                            if (x7).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«$547970696e672f4d5479732e73696e676c65»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                  x12
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  x8)
                                            else
                                              ([] : _root_.List _root_.Geb.Kernel.Tree))
                                          x1
                                          x2;
                                        if (x10).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Typing.sameAll» x12
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»);
    x6

def «Typing.synCase» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                          _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                          x1
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x5 : _root_.Geb.Kernel.Tree ×
                                          _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.markerCtors»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0)
                                          x4;
                                        _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x0 x4)
                                          (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                x2
                                                (_root_.Geb.Kernel.leaf 1)
                                                x3)
                                              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                  (x5).1
                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.namesData» x0 x6 x4)
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                      x6
                                                      x7))).label ≠ 0 then
                                                  _root_.GebMirror.DatatypeSoundness.«Typing.clausesTy»
                                                    (x5).2
                                                    (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                                      (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                        x1
                                                        (_root_.Geb.Kernel.leaf 2)))
                                                    (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e64726f70»
                                                      (_root_.Geb.Kernel.leaf 3)
                                                      x2)
                                                    x3
                                                    (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e73696e676c65»
                                                      (_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                          _root_.GebMirror.DatatypeSoundness.«Typing.kwScrutinee»)
                                                        _root_.GebMirror.DatatypeSoundness.«Typing.tyT»))
                                                    (fun (x8 : _root_.Geb.Kernel.Tree)
                                                       (x9 : _root_.Geb.Kernel.Tree)
                                                       (x10 : _root_.List _root_.Geb.Kernel.Tree →
                                                         _root_.Geb.Kernel.Tree)
                                                       (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.DatatypeSoundness.«Typing.caseFields»
                                                        x0
                                                        x8
                                                        x9
                                                        x10
                                                        x11)
                                                else
                                                  _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»)));
    x4

def «Typing.synCata» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                          _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                          x1
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x5 : _root_.Geb.Kernel.Tree ×
                                          _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.markerCtors»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0)
                                          x4;
                                        _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                          (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x0 x4)
                                          (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                x0
                                                (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                  _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 1)))
                                              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.srAt»
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 2)
                                                    x3)
                                                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                      (x5).1
                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.namesData» x0 x6 x4)
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                                                          x6
                                                          x8))).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«Typing.then1»
                                                        (_root_.GebMirror.DatatypeSoundness.«Typing.clausesTy»
                                                          (x5).2
                                                          (_root_.GebMirror.DatatypeSoundness.«Typing.elemsTx»
                                                            (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                              _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                              x1
                                                              (_root_.Geb.Kernel.leaf 4)))
                                                          (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5352732e64726f70»
                                                            (_root_.Geb.Kernel.leaf 5)
                                                            x2)
                                                          x3
                                                          ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                              _root_.GebMirror.DatatypeSoundness.«Typing.kwUnitArg»)
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit») ::
                                                            ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                                _root_.GebMirror.DatatypeSoundness.«Typing.kwResults»)
                                                              (_root_.GebMirror.DatatypeSoundness.«Typing.tyList»
                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.tyArrow»
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.tyUnit»
                                                                  x7))) ::
                                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e73696e676c65»
                                                                (_root_.GebMirror.DatatypeSoundness.«Typing.abbr»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Typing.boundName»
                                                                    _root_.GebMirror.DatatypeSoundness.«Typing.kwNode»)
                                                                  _root_.GebMirror.DatatypeSoundness.«Typing.tyT»))))
                                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                                             (x10 : _root_.Geb.Kernel.Tree)
                                                             (x11 : _root_.List
                                                               _root_.Geb.Kernel.Tree →
                                                               _root_.Geb.Kernel.Tree)
                                                             (x12 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.DatatypeSoundness.«Typing.cataFields»
                                                              x0
                                                              x4
                                                              x7
                                                              x9
                                                              x10
                                                              x11
                                                              x12))
                                                        (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                          _root_.GebMirror.DatatypeSoundness.«Typing.when»
                                                            (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy» x9 x7)
                                                            x7)
                                                    else
                                                      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))));
    x4

def «Typing.synIn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.para
      (α := _root_.Unit →
        _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Unit →
             _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit →
            _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
            (_root_.Geb.Kernel.leaf 0,
              fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                _root_.Geb.Kernel.leaf 0),
            x4);
          let x7 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x8 : _root_.List _root_.Geb.Kernel.Tree := x7;
          (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x8,
            fun (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«Typing.synAtom» x0 x8 x9)
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x3)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x6 : (_root_.Unit →
              _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree →
                      _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
              (_root_.Geb.Kernel.leaf 0,
                fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  _root_.Geb.Kernel.leaf 0),
              x4);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
            let x8 : _root_.List
              (_root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
              (β := _root_.List
                (_root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
              (fun (x8 : _root_.Unit →
                   _root_.Geb.Kernel.Tree ×
                     (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                 (x9 : _root_.List
                   (_root_.Geb.Kernel.Tree ×
                     (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                ((x8 ()) :: x9))
              ([] : _root_.List (_root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
              (x6).2;
            let x9 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.srForms» x8;
            (_root_.GebMirror.DatatypeSoundness.«Typing.tList» x9,
              fun (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Typing.synList» x0 x9 x8 x10)
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x3)
              (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
              let x6 : (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree →
                        _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
                (_root_.Geb.Kernel.leaf 0,
                  fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                    _root_.Geb.Kernel.leaf 0),
                x4);
              let x7 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
              let x8 : (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree →
                        _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                (β := (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                (x6).2
                (fun (_ : _root_.Unit) =>
                  (_root_.Geb.Kernel.leaf 0,
                    fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                      _root_.Geb.Kernel.leaf 0),
                  ([] : _root_.List (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
                (fun (x8 : _root_.Unit →
                     _root_.Geb.Kernel.Tree ×
                       (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                   (x9 : _root_.List
                     (_root_.Unit →
                       _root_.Geb.Kernel.Tree ×
                         (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                  (x8, x9));
              let x9 : _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree) := (x8).1 ();
              let x10 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x7
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x11);
              let x11 : (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree →
                        _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                (β := (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                (x8).2
                (fun (_ : _root_.Unit) =>
                  (_root_.Geb.Kernel.leaf 0,
                    fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                      _root_.Geb.Kernel.leaf 0),
                  ([] : _root_.List (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
                (fun (x11 : _root_.Unit →
                     _root_.Geb.Kernel.Tree ×
                       (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                   (x12 : _root_.List
                     (_root_.Unit →
                       _root_.Geb.Kernel.Tree ×
                         (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                  (x11, x12));
              let x12 : _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree) := (x11).1 ();
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x10
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x14);
              (_root_.GebMirror.DatatypeSoundness.«Typing.tAs» (x9).1 (x12).1,
                fun (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                    (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x0 (x9).1)
                    ((x12).2 x14)
                    (fun (x15 : _root_.Geb.Kernel.Tree) (x16 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.DatatypeSoundness.«Typing.when»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy»
                          (_root_.GebMirror.DatatypeSoundness.«Typing.eraseTy» x15)
                          x16)
                        x15))
            else
              if (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.label x3)
                (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                let x6 : (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree →
                          _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
                  (_root_.Geb.Kernel.leaf 0,
                    fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                      _root_.Geb.Kernel.leaf 0),
                  x4);
                let x7 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
                let x8 : (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree →
                          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                  (β := (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree ×
                          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                  (x6).2
                  (fun (_ : _root_.Unit) =>
                    (_root_.Geb.Kernel.leaf 0,
                      fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.Geb.Kernel.leaf 0),
                    ([] : _root_.List (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
                  (fun (x8 : _root_.Unit →
                       _root_.Geb.Kernel.Tree ×
                         (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                     (x9 : _root_.List
                       (_root_.Unit →
                         _root_.Geb.Kernel.Tree ×
                           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                    (x8, x9));
                let x9 : _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree) := (x8).1 ();
                let x10 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.List _root_.Geb.Kernel.Tree)
                  x7
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (fun (_ : _root_.Geb.Kernel.Tree)
                     (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                    x11);
                let x11 : (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree →
                          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                  (β := (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree ×
                          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                  (x8).2
                  (fun (_ : _root_.Unit) =>
                    (_root_.Geb.Kernel.leaf 0,
                      fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.Geb.Kernel.leaf 0),
                    ([] : _root_.List (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
                  (fun (x11 : _root_.Unit →
                       _root_.Geb.Kernel.Tree ×
                         (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                     (x12 : _root_.List
                       (_root_.Unit →
                         _root_.Geb.Kernel.Tree ×
                           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                    (x11, x12));
                let x12 : _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree) := (x11).1 ();
                let _ : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.List _root_.Geb.Kernel.Tree)
                  x10
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (fun (_ : _root_.Geb.Kernel.Tree)
                     (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                    x14);
                (_root_.GebMirror.DatatypeSoundness.«Typing.tOf» (x9).1 (x12).1,
                  fun (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.DatatypeSoundness.«Typing.both2»
                      (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x0 (x9).1)
                      ((x12).2 x14)
                      (fun (x15 : _root_.Geb.Kernel.Tree) (x16 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.DatatypeSoundness.«Typing.when»
                          (_root_.GebMirror.DatatypeSoundness.«Typing.sameTy» x15 x16)
                          (_root_.GebMirror.DatatypeSoundness.«Typing.eraseTy» x15)))
              else
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x3)
                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                  let x6 : (_root_.Unit →
                    _root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree ×
                          (_root_.List _root_.Geb.Kernel.Tree →
                            _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
                    (_root_.Geb.Kernel.leaf 0,
                      fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.Geb.Kernel.leaf 0),
                    x4);
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
                  let x8 : _root_.List
                    (_root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree →
                        _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
                    (α := _root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                    (β := _root_.List
                      (_root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                    (fun (x8 : _root_.Unit →
                         _root_.Geb.Kernel.Tree ×
                           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                       (x9 : _root_.List
                         (_root_.Geb.Kernel.Tree ×
                           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                      ((x8 ()) :: x9))
                    ([] : _root_.List (_root_.Geb.Kernel.Tree ×
                      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                    (x6).2;
                  let x9 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.srForms» x8;
                  (_root_.GebMirror.DatatypeSoundness.«Typing.tCase» x9,
                    fun (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.DatatypeSoundness.«Typing.synCase» x0 x9 x8 x10)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x3)
                    (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                    let x6 : (_root_.Unit →
                      _root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree ×
                            (_root_.List _root_.Geb.Kernel.Tree →
                              _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
                      (_root_.Geb.Kernel.leaf 0,
                        fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          _root_.Geb.Kernel.leaf 0),
                      x4);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
                    let x8 : _root_.List
                      (_root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree →
                          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
                      (α := _root_.Unit →
                        _root_.Geb.Kernel.Tree ×
                          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                      (β := _root_.List
                        (_root_.Geb.Kernel.Tree ×
                          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                      (fun (x8 : _root_.Unit →
                           _root_.Geb.Kernel.Tree ×
                             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                         (x9 : _root_.List
                           (_root_.Geb.Kernel.Tree ×
                             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                        ((x8 ()) :: x9))
                      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
                        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
                      (x6).2;
                    let x9 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.srForms» x8;
                    (_root_.GebMirror.DatatypeSoundness.«Typing.tCata» x9,
                      fun (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.DatatypeSoundness.«Typing.synCata» x0 x9 x8 x10)
                  else
                    (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
                      fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f54792e6e6f7468696e67»))
      x2
      ()).2
      x1;
    x3

def «$547970696e672f4f4e616d652e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$547970696e672f4f4e616d652e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$547970696e672f4f4e616d652e69734a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$547970696e672f4f4e616d652e66726f6d4d61796265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$547970696e672f4f4e616d652e6e74684f66» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6a757374» x2);
    x2

def «$547970696e672f4f4e616d652e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «Typing.withAl» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      x1
      (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0);
    x2

def «Typing.withDefs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0)
      x1
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0);
    x2

def «Typing.withNoms» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0)
      x1
      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0);
    x2

def «Typing.withSorts» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
      x1
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0);
    x2

def «Typing.withNums» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)
      x1
      (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x0);
    x2

def «Typing.withMs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List
                _root_.Geb.Kernel.Tree)))) := _root_.GebMirror.DatatypeSoundness.«Typing.mkEnv»
      (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x0)
      (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x0)
      x1;
    x2

def «Typing.checkStep» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := (x0).2;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x2)
                                   (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                   let x3 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
                                   let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                     (α := _root_.Geb.Kernel.Tree)
                                     (β := _root_.Geb.Kernel.Tree)
                                     x3
                                     (_root_.Geb.Kernel.leaf 0)
                                     (fun (x4 : _root_.Geb.Kernel.Tree)
                                        (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                       x4);
                                   let _ : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                     (α := _root_.Geb.Kernel.Tree)
                                     (β := _root_.List _root_.Geb.Kernel.Tree)
                                     x3
                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                     (fun (_ : _root_.Geb.Kernel.Tree)
                                        (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                       x6);
                                   x0
                                 else
                                   let _ : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
                                   let x4 : _root_.List _root_.Geb.Kernel.Tree ×
                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                         (_root_.List _root_.Geb.Kernel.Tree ×
                                           (_root_.List _root_.Geb.Kernel.Tree ×
                                             _root_.List _root_.Geb.Kernel.Tree)))) := (x0).1;
                                   let x5 : (_root_.List _root_.Geb.Kernel.Tree ×
                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                         (_root_.List _root_.Geb.Kernel.Tree ×
                                           (_root_.List _root_.Geb.Kernel.Tree ×
                                             _root_.List _root_.Geb.Kernel.Tree))))) →
                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                         (_root_.List _root_.Geb.Kernel.Tree ×
                                           (_root_.List _root_.Geb.Kernel.Tree ×
                                             (_root_.List _root_.Geb.Kernel.Tree ×
                                               _root_.List _root_.Geb.Kernel.Tree))))) ×
                                       _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List
                                                                      _root_.Geb.Kernel.Tree ×
                                                                      (_root_.List
                                                                        _root_.Geb.Kernel.Tree ×
                                                                        (_root_.List
                                                                          _root_.Geb.Kernel.Tree ×
                                                                          (_root_.List
                                                                            _root_.Geb.Kernel.Tree ×
                                                                            (_root_.List
                                                                              _root_.Geb.Kernel.Tree ×
                                                                              _root_.List
                                                                                _root_.Geb.Kernel.Tree))))) =>
                                     (x5,
                                       _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6e6f7468696e67»));
                                   let x6 : (_root_.List _root_.Geb.Kernel.Tree ×
                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                         (_root_.List _root_.Geb.Kernel.Tree ×
                                           (_root_.List _root_.Geb.Kernel.Tree ×
                                             _root_.List _root_.Geb.Kernel.Tree))))) ×
                                     _root_.Geb.Kernel.Tree := (x4,
                                     _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6a757374»
                                       (let x6 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x6)
                                          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                          let x7 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
                                          let x8 : _root_.List _root_.Geb.Kernel.Tree := x7;
                                          if (_root_.Geb.Kernel.Const.lt
                                            (_root_.Geb.Kernel.leaf 1)
                                            (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e6c656e677468»
                                              x8)).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Typing.atomName»
                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                                _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                                x8
                                                (_root_.Geb.Kernel.leaf 1))
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)));
                                   let x7 : _root_.Geb.Kernel.Tree := x1;
                                   if (_root_.Geb.Kernel.Const.eq
                                     (_root_.Geb.Kernel.Const.label x7)
                                     (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                     let x8 : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x7;
                                     let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.Geb.Kernel.Tree)
                                       x8
                                       (_root_.Geb.Kernel.leaf 0)
                                       (fun (x9 : _root_.Geb.Kernel.Tree)
                                          (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x9);
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x8
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x11);
                                     x5
                                       (_root_.GebMirror.DatatypeSoundness.«Typing.withNoms»
                                         x4
                                         (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e617070656e64»
                                           (_root_.GebMirror.DatatypeSoundness.«Typing.envNoms» x4)
                                           (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e73696e676c65»
                                             (_root_.GebMirror.DatatypeSoundness.«Typing.atomName» x9))))
                                   else
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.Geb.Kernel.Const.label x7)
                                       (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                       let x8 : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                         x7;
                                       let _ : _root_.List _root_.Geb.Kernel.Tree := x8;
                                       x5
                                         (_root_.GebMirror.DatatypeSoundness.«Typing.withMs»
                                           x4
                                           (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e617070656e64»
                                             (_root_.GebMirror.DatatypeSoundness.«Typing.envMs» x4)
                                             (_root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e73696e676c65»
                                               x1)))
                                     else
                                       if (_root_.Geb.Kernel.Const.eq
                                         (_root_.Geb.Kernel.Const.label x7)
                                         (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                         let x8 : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                           x7;
                                         let x9 : _root_.List _root_.Geb.Kernel.Tree := x8;
                                         let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                           _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                           x9
                                           (_root_.Geb.Kernel.leaf 0);
                                         let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                           _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                           x9
                                           (_root_.Geb.Kernel.leaf 1);
                                         let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e6c656e677468»
                                           x9;
                                         if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                           (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                             x10
                                             _root_.GebMirror.DatatypeSoundness.«Typing.kwSort»)
                                           (_root_.Geb.Kernel.Const.eq
                                             x12
                                             (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                           x5
                                             (_root_.GebMirror.DatatypeSoundness.«Typing.withSorts»
                                               x4
                                               (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e617070656e64»
                                                 (_root_.GebMirror.DatatypeSoundness.«Typing.envSorts» x4)
                                                 (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e73696e676c65»
                                                   (_root_.GebMirror.DatatypeSoundness.«Typing.atomName» x11))))
                                         else
                                           if (_root_.Geb.Kernel.Const.eq
                                             x12
                                             (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                             let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.atomName»
                                               x11;
                                             let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$547970696e672f5478732e61744f72»
                                               _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
                                               x9
                                               (_root_.Geb.Kernel.leaf 2);
                                             let x15 : _root_.Geb.Kernel.Tree →
                                               (_root_.List _root_.Geb.Kernel.Tree ×
                                                 (_root_.List _root_.Geb.Kernel.Tree ×
                                                   (_root_.List _root_.Geb.Kernel.Tree ×
                                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                                         _root_.List _root_.Geb.Kernel.Tree))))) ×
                                                 _root_.Geb.Kernel.Tree := (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                               let x16 : _root_.Geb.Kernel.Tree := x15;
                                               if (_root_.Geb.Kernel.Const.eq
                                                 (_root_.Geb.Kernel.Const.label x16)
                                                 (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                 let x17 : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                   x16;
                                                 let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.Geb.Kernel.Tree)
                                                   x17
                                                   (_root_.Geb.Kernel.leaf 0)
                                                   (fun (x18 : _root_.Geb.Kernel.Tree)
                                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                     x18);
                                                 let _ : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                                   x17
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                                      (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                     x20);
                                                 x5
                                                   (_root_.GebMirror.DatatypeSoundness.«Typing.withDefs»
                                                     x4
                                                     (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e617070656e64»
                                                       (_root_.GebMirror.DatatypeSoundness.«Typing.envDefs» x4)
                                                       (_root_.GebMirror.DatatypeSoundness.«$547970696e672f41626272732e73696e676c65»
                                                         (_root_.GebMirror.DatatypeSoundness.«Typing.abbr» x13 x18))))
                                               else
                                                 let _ : _root_.List
                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                   x16;
                                                 x6);
                                             if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                               x10
                                               _root_.GebMirror.DatatypeSoundness.«Reader.kwDef»).label ≠ 0 then
                                               x15
                                                 (_root_.GebMirror.DatatypeSoundness.«Typing.synIn»
                                                   x4
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   x14)
                                             else
                                               if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                 x10
                                                 _root_.GebMirror.DatatypeSoundness.«Typing.kwPostulate»).label ≠ 0 then
                                                 x15 (_root_.GebMirror.DatatypeSoundness.«Typing.readTy» x4 x14)
                                               else
                                                 if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                   x10
                                                   _root_.GebMirror.DatatypeSoundness.«Reader.kwDeftype»).label ≠ 0 then
                                                   let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.readTy»
                                                     x4
                                                     x14;
                                                   if (_root_.Geb.Kernel.Const.eq
                                                     (_root_.Geb.Kernel.Const.label x16)
                                                     (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                     let x17 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                       x16;
                                                     let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x17
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x18 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x18);
                                                     let _ : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x17
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x20 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x20);
                                                     x5
                                                       (_root_.GebMirror.DatatypeSoundness.«Typing.withAl»
                                                         x4
                                                         ((_root_.GebMirror.DatatypeSoundness.«Typing.abbr» x13 x18) ::
                                                           (_root_.GebMirror.DatatypeSoundness.«Typing.envAl» x4)))
                                                   else
                                                     let _ : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                       x16;
                                                     x6
                                                 else
                                                   if (_root_.GebMirror.DatatypeSoundness.«Typing.namedTx»
                                                     x10
                                                     _root_.GebMirror.DatatypeSoundness.«Reader.kwDefnum»).label ≠ 0 then
                                                     if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
                                                       (_root_.GebMirror.DatatypeSoundness.«Reader.numeral»
                                                         (_root_.Geb.Kernel.Const.children
                                                           x13))).label ≠ 0 then
                                                       x6
                                                     else
                                                       x5
                                                         (_root_.GebMirror.DatatypeSoundness.«Typing.withNums»
                                                           x4
                                                           (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e617070656e64»
                                                             (_root_.GebMirror.DatatypeSoundness.«Typing.envNums» x4)
                                                             (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4e616d65732e73696e676c65»
                                                               x13)))
                                                   else
                                                     x6
                                           else
                                             x6
                                       else
                                         x6);
    x2

def «Typing.checkRun» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := ((_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree ×
                _root_.List _root_.Geb.Kernel.Tree))))) ×
        _root_.Geb.Kernel.Tree) →
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree ×
                  _root_.List _root_.Geb.Kernel.Tree))))) ×
          _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : ((_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) →
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   (_root_.List _root_.Geb.Kernel.Tree ×
                     _root_.List _root_.Geb.Kernel.Tree))))) ×
             _root_.Geb.Kernel.Tree)
         (x4 : (_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) =>
        x3 (_root_.GebMirror.DatatypeSoundness.«Typing.checkStep» x4 x2))
      (fun (x2 : (_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) =>
        x2)
      x1
      x0;
    x2

def «Typing.checkAll» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : (_root_.List _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))))) ×
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := ((_root_.List _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree ×
                _root_.List _root_.Geb.Kernel.Tree))))) ×
        _root_.Geb.Kernel.Tree) →
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree ×
                  _root_.List _root_.Geb.Kernel.Tree))))) ×
          _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : ((_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) →
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   (_root_.List _root_.Geb.Kernel.Tree ×
                     _root_.List _root_.Geb.Kernel.Tree))))) ×
             _root_.Geb.Kernel.Tree)
         (x4 : (_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) =>
        x3
          (let x5 : _root_.Geb.Kernel.Tree := x2;
           if (_root_.Geb.Kernel.Const.eq
             (_root_.Geb.Kernel.Const.label x5)
             (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
             let x6 : _root_.List
               _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
             let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
             let x8 : _root_.Geb.Kernel.Tree := (x4).2;
             if (_root_.Geb.Kernel.Const.eq
               (_root_.Geb.Kernel.Const.label x8)
               (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
               let x9 : _root_.List
                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
               let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                 (α := _root_.Geb.Kernel.Tree)
                 (β := _root_.Geb.Kernel.Tree)
                 x9
                 (_root_.Geb.Kernel.leaf 0)
                 (fun (x10 : _root_.Geb.Kernel.Tree)
                    (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                   x10);
               let _ : _root_.List
                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                 (α := _root_.Geb.Kernel.Tree)
                 (β := _root_.List _root_.Geb.Kernel.Tree)
                 x9
                 ([] : _root_.List _root_.Geb.Kernel.Tree)
                 (fun (_ : _root_.Geb.Kernel.Tree)
                    (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                   x12);
               x4
             else
               let _ : _root_.List
                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
               ((x4).1, (_root_.GebMirror.DatatypeSoundness.«Typing.checkRun» x4 x7).2)
           else
             _root_.GebMirror.DatatypeSoundness.«Typing.checkStep» x4 x2))
      (fun (x2 : (_root_.List _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 (_root_.List _root_.Geb.Kernel.Tree ×
                   _root_.List _root_.Geb.Kernel.Tree))))) ×
           _root_.Geb.Kernel.Tree) =>
        x2)
      x1
      x0;
    x2

def «Typing.checkForms» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.DatatypeSoundness.«Typing.checkAll»
      (_root_.GebMirror.DatatypeSoundness.«Typing.env0»,
        _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6e6f7468696e67»)
      x0).2;
    x1

def «$44617461747970652f5478732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$44617461747970652f5478732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$44617461747970652f5478732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$44617461747970652f5478732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$44617461747970652f5478732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$44617461747970652f5478732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c»
      x1
      x0;
    x2

def «$44617461747970652f5478732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$44617461747970652f4f54782e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$44617461747970652f4f54782e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$44617461747970652f4f54782e69734a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$44617461747970652f4f54782e66726f6d4d61796265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$44617461747970652f4f54782e6e74684f66» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374» x2);
    x2

def «$44617461747970652f4f54782e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «$44617461747970652f4d5478732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$44617461747970652f4d5478732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$44617461747970652f4d5478732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$44617461747970652f4d5478732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$44617461747970652f4d5478732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$44617461747970652f4d5478732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4d5478732e7461696c»
      x1
      x0;
    x2

def «$44617461747970652f4d5478732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f4d5478732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Datatype.sameName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.equal
      x0
      x1;
    x2

def «Datatype.atomName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let x3 : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.GebMirror.DatatypeSoundness.«Typing.name» x3
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                            ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Datatype.isAtomTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «Datatype.isListTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.List _root_.Geb.Kernel.Tree := x2;
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «Datatype.namedTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.named»
      x0
      x1;
    x2

def «Datatype.elems» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x1)
                                   (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                   let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                   let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3
                                 else
                                   ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Datatype.nthTx» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e61744f72»
      _root_.GebMirror.DatatypeSoundness.«Typing.tx0»
      x0
      x1;
    x2

def «Datatype.sx1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x0);
    x1

def «Datatype.sx2» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (x0 :: (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x1));
    x2

def «Datatype.sx3» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (x0 ::
        (x1 ::
          (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x2)));
    x3

def «Datatype.sx4» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (x0 ::
        (x1 ::
          (x2 ::
            (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x3))));
    x4

def «Datatype.sx5» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (x0 ::
        (x1 ::
          (x2 ::
            (x3 ::
              (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x4)))));
    x5

def «Datatype.sx6» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tList»
      (x0 ::
        (x1 ::
          (x2 ::
            (x3 ::
              (x4 ::
                (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x5))))));
    x6

def «Datatype.aLet» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aIf» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 102]

def «Datatype.aLam» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 109]

def «Datatype.aPair» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 114]

def «Datatype.aFst» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aSnd» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 100]

def «Datatype.aCons» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 115]

def «Datatype.aNil» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 108]

def «Datatype.aLcase» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aFoldr» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 114]

def «Datatype.aPara» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 97]

def «Datatype.aDef» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102]

def «Datatype.aDeftype» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 121,
    _root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aUnitV» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aQuote» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 113,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aLabel» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 98,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 108]

def «Datatype.aChildren» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 104,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 110]

def «Datatype.aNode» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aEq» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 113]

def «Datatype.aT» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 84]

def «Datatype.aUnit» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 85,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aProd» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 80,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100]

def «Datatype.aArrow» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 65,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 119]

def «Datatype.aList» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 76,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aZero» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 48]

def «Datatype.aS» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwScrutinee»)

def «Datatype.aO» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwNode»)

def «Datatype.aA» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 97]

def «Datatype.aH» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 104]

def «Datatype.aTl» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aX» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 120]

def «Datatype.aU» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwUnitArg»)

def «Datatype.aR» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 114]

def «Datatype.aD» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 100]

def «Datatype.aRest» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.aK» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwResults»)

def «Datatype.aC» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwFields»)

def «Datatype.aQ» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwSplit»)

def «Datatype.aE» :=
  _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
    (_root_.Geb.Kernel.Const.children _root_.GebMirror.DatatypeSoundness.«Typing.kwDecoded»)

def «Datatype.kwData» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 97]

def «Datatype.kwCase» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.kwCata» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 97]

def «Datatype.kwDefn» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 110]

def «Datatype.kwElse» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.kwRep» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 112]

def «Datatype.kwDecode» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.kwDatum» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 109]

def «Datatype.kwGeneric» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 103,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 99]

def «Datatype.kwSort» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 116]

def «Datatype.kwPostulate» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 112,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.kwAmp» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 38]

def «Datatype.numAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
      (_root_.GebMirror.DatatypeSoundness.«Typing.decimalChars» x0);
    x1

def «Datatype.memberName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 46,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 98,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 114])));
    x1

def «Datatype.memberAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 46,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 98,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 114])));
    x1

def «Datatype.fieldAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
      ((_root_.Geb.Kernel.leaf 37) ::
        ((_root_.Geb.Kernel.leaf 102) ::
          (_root_.GebMirror.DatatypeSoundness.«Typing.decimalChars» x0)));
    x1

def «Datatype.sList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aList»
      x0;
    x1

def «Datatype.sProd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aProd»
      x0
      x1;
    x2

def «Datatype.sArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aArrow»
      x0
      x1;
    x2

def «Datatype.sLet» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx5»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aLet»
      x0
      x1
      x2
      x3;
    x4

def «Datatype.sIf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx4»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aIf»
      x0
      x1
      x2;
    x3

def «Datatype.sLam1» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aLam»
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sx1» (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2» x0 x1))
      x2;
    x3

def «Datatype.sLam2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sLam1»
      x0
      x1
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam1» x2 x3 x4);
    x5

def «Datatype.bindersTx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x1)
                                   (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                   let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                   let x3 : _root_.List _root_.Geb.Kernel.Tree := x2;
                                   if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                     (_root_.Geb.Kernel.Const.eq
                                       (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468» x3)
                                       (_root_.Geb.Kernel.leaf 2))
                                     (_root_.GebMirror.DatatypeSoundness.«Datatype.isAtomTx»
                                       (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                         x3
                                         (_root_.Geb.Kernel.leaf 0)))).label ≠ 0 then
                                     _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65» x0
                                   else
                                     x3
                                 else
                                   ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Datatype.curry» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
          _root_.GebMirror.DatatypeSoundness.«Datatype.aLam»
          (_root_.GebMirror.DatatypeSoundness.«Datatype.sx1» x2)
          x3)
      x1
      x0;
    x2

def «Datatype.curried» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                          x0;
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                              x1
                                              (_root_.Geb.Kernel.leaf 0))
                                            _root_.GebMirror.DatatypeSoundness.«Reader.kwLam»)
                                          (_root_.Geb.Kernel.Const.eq
                                            (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                              x1)
                                            (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.bindersTx»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                              x1
                                              (_root_.Geb.Kernel.leaf 1));
                                          if (_root_.Geb.Kernel.Const.lt
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                              x2)).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.curry»
                                                x2
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 2)))
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374» x0);
    x1

def «Datatype.sHeadOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx6»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aLcase»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
      x0
      _root_.GebMirror.DatatypeSoundness.«Datatype.aZero»
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam2»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aTl»
        (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
        _root_.GebMirror.DatatypeSoundness.«Datatype.aH»);
    x1

def «Datatype.sTailOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sx6»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aLcase»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
      x0
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aNil»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam2»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aTl»
        (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
        _root_.GebMirror.DatatypeSoundness.«Datatype.aTl»);
    x1

def «Datatype.asTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tAs» x0 x1;
    x2

def «Datatype.ofTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tOf» x0 x1;
    x2

def «Datatype.dropLast» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e72657665727365»
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c»
        (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e72657665727365» x0));
    x1

def «Datatype.allTrue» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.and» x1 x2)
      (_root_.Geb.Kernel.leaf 1)
      x0;
    x1

def «Datatype.ctorD» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 ::
          (x2 ::
            (x3 :: (x4 :: (x5 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))))

def «Datatype.dataD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Datatype.aliasD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$44617461747970652f4465636c732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$44617461747970652f4465636c732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$44617461747970652f4465636c732e617070656e64» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$44617461747970652f4465636c732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$44617461747970652f4465636c732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$44617461747970652f4465636c732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4465636c732e7461696c»
      x1
      x0;
    x2

def «$44617461747970652f4465636c732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f4465636c732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$44617461747970652f4f4465636c2e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$44617461747970652f4f4465636c2e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$44617461747970652f4f4465636c2e69734a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$44617461747970652f4f4465636c2e66726f6d4d61796265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$44617461747970652f4f4465636c2e6e74684f66» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f4465636c2e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f4465636c2e6a757374» x2);
    x2

def «$44617461747970652f4f4465636c2e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «Datatype.findCtor» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x4)
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x5
            (_root_.Geb.Kernel.leaf 0)
            (fun (x6 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x6);
          let x7 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x7
            (_root_.Geb.Kernel.leaf 0)
            (fun (x8 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let x9 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x7
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
              x10);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x9
            (_root_.Geb.Kernel.leaf 0)
            (fun (x10 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x10);
          let x11 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x9
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
              x12);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x11
            (_root_.Geb.Kernel.leaf 0)
            (fun (x12 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x12);
          let x13 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x11
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
              x14);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x13
            (_root_.Geb.Kernel.leaf 0)
            (fun (x14 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x14);
          let x15 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x13
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
              x16);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x15
            (_root_.Geb.Kernel.leaf 0)
            (fun (x16 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x16);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x15
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x18 : _root_.List _root_.Geb.Kernel.Tree) =>
              x18);
          if (_root_.GebMirror.DatatypeSoundness.«Datatype.sameName» x6 x0).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f4465636c2e6a757374» x2
          else
            x3
        else
          x3)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f4465636c2e6e6f7468696e67»
      x1;
    x2

def «Datatype.isData» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x4)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x5
            (_root_.Geb.Kernel.leaf 0)
            (fun (x6 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x6);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          _root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.GebMirror.DatatypeSoundness.«Datatype.sameName» x6 x0)
            x3
        else
          x3)
      (_root_.Geb.Kernel.leaf 0)
      x1;
    x2

def «Datatype.findAlias» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x4)
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x5
            (_root_.Geb.Kernel.leaf 0)
            (fun (x6 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x6);
          let x7 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x7
            (_root_.Geb.Kernel.leaf 0)
            (fun (x8 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x7
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
              x10);
          if (_root_.GebMirror.DatatypeSoundness.«Datatype.sameName» x6 x0).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374» x8
          else
            x3
        else
          x3)
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
      x1;
    x2

def «Datatype.ctorsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x4)
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x5
            (_root_.Geb.Kernel.leaf 0)
            (fun (x6 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x6);
          let x7 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x7
            (_root_.Geb.Kernel.leaf 0)
            (fun (x8 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x8);
          let x9 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x7
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
              x10);
          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x9
            (_root_.Geb.Kernel.leaf 0)
            (fun (x10 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x10);
          let x11 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x9
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
              x12);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x11
            (_root_.Geb.Kernel.leaf 0)
            (fun (x12 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x12);
          let x13 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x11
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
              x14);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x13
            (_root_.Geb.Kernel.leaf 0)
            (fun (x14 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x14);
          let x15 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x13
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
              x16);
          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x15
            (_root_.Geb.Kernel.leaf 0)
            (fun (x16 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x16);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x15
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x18 : _root_.List _root_.Geb.Kernel.Tree) =>
              x18);
          if (_root_.GebMirror.DatatypeSoundness.«Datatype.sameName» x10 x0).label ≠ 0 then
            (x2 :: x3)
          else
            x3
        else
          x3)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «Datatype.ctorName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let x4 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x4
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x5 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x4
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x8 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x8
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x9 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let x10 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x8
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x11);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x10
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x11 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x11);
                                          let x12 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x10
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x12
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x13 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x12
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x15);
                                          x3
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x2 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x1;
                                            let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x2
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x3 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x3);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x2
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            x3
                                          else
                                            let x2 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x1;
                                            let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x2
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x3 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x3);
                                            let x4 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x2
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x4
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x5 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x4
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x7);
                                            x3);
    x1

def «Datatype.ctorData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let x4 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x4
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x5 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x4
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x8 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x8
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x9 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let x10 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x8
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x11);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x10
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x11 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x11);
                                          let x12 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x10
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x12
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x13 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x12
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x15);
                                          x7
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x2 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x1;
                                            let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x2
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x3 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x3);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x2
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            x3
                                          else
                                            let x2 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x1;
                                            let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x2
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x3 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x3);
                                            let x4 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x2
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x4
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x5 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x4
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x7);
                                            x3);
    x1

def «Datatype.expandAliases» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            _root_.Geb.Kernel.leaf 0,
            x3);
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
          let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.findAlias»
            (_root_.GebMirror.DatatypeSoundness.«Typing.name» x7)
            x0;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x8)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x9 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
            let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x9
              (_root_.Geb.Kernel.leaf 0)
              (fun (x10 : _root_.Geb.Kernel.Tree)
                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                x10);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x9
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                x12);
            x10
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
            _root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x5 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              _root_.Geb.Kernel.leaf 0,
              x3);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
            let x7 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit → _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              (fun (x7 : _root_.Unit → _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                ((x7 ()) :: x8))
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (x5).2;
            _root_.GebMirror.DatatypeSoundness.«Typing.tList» x7
          else
            _root_.GebMirror.DatatypeSoundness.«Typing.tx0»)
      x1
      ();
    x2

def «$44617461747970652f5454732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := (x0 ::
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)));
    x1

def «$44617461747970652f5454732e6c656e677468» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$44617461747970652f5454732e617070656e64» :=
  fun (x0 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$44617461747970652f5454732e72657665727365» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) →
        _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x1 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) →
           _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x1)
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree));
    x1

def «$44617461747970652f5454732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$44617461747970652f5454732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5454732e7461696c»
      x1
      x0;
    x2

def «$44617461747970652f5454732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5454732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
         (_ : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        x3);
    x3

def «Datatype.defaultOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit →
            _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0),
            x2);
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
          let x6 : _root_.List _root_.Geb.Kernel.Tree := x5;
          (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x6,
            if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
              (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x6)
              _root_.GebMirror.DatatypeSoundness.«Reader.kwUnit»).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Datatype.aUnitV»
            else
              _root_.GebMirror.DatatypeSoundness.«Datatype.asTy»
                (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x6)
                _root_.GebMirror.DatatypeSoundness.«Datatype.aZero»)
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x4 : (_root_.Unit →
              _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0),
              x2);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
            let x6 : _root_.List
              (_root_.Geb.Kernel.Tree ×
                _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
              (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
              (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                 (x7 : _root_.List
                   (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
                ((x6 ()) :: x7))
              ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
              (x4).2;
            let x7 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              (fun (x7 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                ((x7).1 :: x8))
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              x6;
            let x8 : _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x8 : _root_.Geb.Kernel.Tree) =>
              (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5454732e61744f72»
                (_root_.GebMirror.DatatypeSoundness.«Typing.tx0», _root_.GebMirror.DatatypeSoundness.«Datatype.aZero»)
                x6
                x8).2);
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
              x7
              (_root_.Geb.Kernel.leaf 0);
            (_root_.GebMirror.DatatypeSoundness.«Typing.tList» x7,
              if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                x9
                _root_.GebMirror.DatatypeSoundness.«Reader.kwProd»).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                  _root_.GebMirror.DatatypeSoundness.«Datatype.aPair»
                  (x8 (_root_.Geb.Kernel.leaf 1))
                  (x8 (_root_.Geb.Kernel.leaf 2))
              else
                if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                  x9
                  _root_.GebMirror.DatatypeSoundness.«Reader.kwArrow»).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Datatype.sLam1»
                    _root_.GebMirror.DatatypeSoundness.«Datatype.aD»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x7 (_root_.Geb.Kernel.leaf 1))
                    (x8 (_root_.Geb.Kernel.leaf 2))
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                    x9
                    _root_.GebMirror.DatatypeSoundness.«Reader.kwList»).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                      _root_.GebMirror.DatatypeSoundness.«Datatype.aNil»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x7 (_root_.Geb.Kernel.leaf 1))
                  else
                    _root_.GebMirror.DatatypeSoundness.«Datatype.aZero»)
          else
            (_root_.GebMirror.DatatypeSoundness.«Typing.tx0», _root_.GebMirror.DatatypeSoundness.«Datatype.aZero»))
      x0
      ()).2;
    x1

def «$44617461747970652f5852732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := (x0 ::
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))));
    x1

def «$44617461747970652f5852732e6c656e677468» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$44617461747970652f5852732e617070656e64» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$44617461747970652f5852732e72657665727365» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
        _root_.List
          (_root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
           _root_.List
             (_root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x1)
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)));
    x1

def «$44617461747970652f5852732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2);
    x1

def «$44617461747970652f5852732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5852732e7461696c»
      x1
      x0;
    x2

def «$44617461747970652f5852732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5852732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (_ : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x3);
    x3

def «Datatype.xrForms» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Datatype.xrAt» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5852732e61744f72»
      (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
        fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»)
      x0
      x1).2
      x2;
    x3

def «Datatype.xrFrom» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e616c6c4a757374»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x3 : _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
           (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
          (((x3).2 x2) :: x4))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5852732e64726f70» x1 x0));
    x3

def «Datatype.clauseCtor» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x1)
                                          (_root_.Geb.Kernel.leaf 0);
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.List _root_.Geb.Kernel.Tree := x3;
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.findCtor»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.atomName»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                x4
                                                (_root_.Geb.Kernel.leaf 0)))
                                            x0
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f4465636c2e6e6f7468696e67»);
    x2

def «Datatype.splitVars» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree ×
          _root_.List _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree ×
             _root_.List _root_.Geb.Kernel.Tree)
         (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree ×
            _root_.List _root_.Geb.Kernel.Tree)
          x6
          (let x7 : _root_.List _root_.Geb.Kernel.Tree ×
             _root_.List _root_.Geb.Kernel.Tree := x5 x6;
           ((x7).1, ((x3 x4 x1) :: (x7).2)))
          (fun (x7 : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            let x9 : _root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree := x5 x8;
            (((x3 x4 x7) :: (x9).1), (x9).2)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        (([] : _root_.List _root_.Geb.Kernel.Tree),
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x2
      x0;
    x4

def «Datatype.clauseParts» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          _root_.List
            _root_.Geb.Kernel.Tree)) := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                           x2;
                                         let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                           x2
                                           (_root_.Geb.Kernel.Const.sub
                                             x5
                                             (_root_.Geb.Kernel.leaf 1));
                                         let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.isListTx» x6)
                                           (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                             (_root_.Geb.Kernel.Const.eq
                                               (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                 (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x6))
                                               (_root_.Geb.Kernel.leaf 2))
                                             (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                               (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                 (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x6)
                                                 (_root_.Geb.Kernel.leaf 0))
                                               _root_.GebMirror.DatatypeSoundness.«Datatype.kwElse»));
                                         let x8 : _root_.Geb.Kernel.Tree := (let x8 : _root_.Geb.Kernel.Tree := x1;
                                                                             if (_root_.Geb.Kernel.Const.eq
                                                                               (_root_.Geb.Kernel.Const.label
                                                                                 x8)
                                                                               (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                               let x9 : _root_.List
                                                                                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                                 x8;
                                                                               let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                                 (α := _root_.Geb.Kernel.Tree)
                                                                                 (β := _root_.Geb.Kernel.Tree)
                                                                                 x9
                                                                                 (_root_.Geb.Kernel.leaf 0)
                                                                                 (fun (x10 : _root_.Geb.Kernel.Tree)
                                                                                    (_ : _root_.List
                                                                                      _root_.Geb.Kernel.Tree) =>
                                                                                   x10);
                                                                               let _ : _root_.List
                                                                                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                                 (α := _root_.Geb.Kernel.Tree)
                                                                                 (β := _root_.List
                                                                                   _root_.Geb.Kernel.Tree)
                                                                                 x9
                                                                                 ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                                 (fun (_ : _root_.Geb.Kernel.Tree)
                                                                                    (x12 : _root_.List
                                                                                      _root_.Geb.Kernel.Tree) =>
                                                                                   x12);
                                                                               x10
                                                                             else
                                                                               let _ : _root_.List
                                                                                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                                 x8;
                                                                               let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.clauseCtor»
                                                                                 x0
                                                                                 (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                                                   x2
                                                                                   (_root_.Geb.Kernel.leaf 0));
                                                                               if (_root_.Geb.Kernel.Const.eq
                                                                                 (_root_.Geb.Kernel.Const.label
                                                                                   x10)
                                                                                 (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                                 let x11 : _root_.List
                                                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                                   x10;
                                                                                 let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                                   (α := _root_.Geb.Kernel.Tree)
                                                                                   (β := _root_.Geb.Kernel.Tree)
                                                                                   x11
                                                                                   (_root_.Geb.Kernel.leaf 0)
                                                                                   (fun (x12 : _root_.Geb.Kernel.Tree)
                                                                                      (_ : _root_.List
                                                                                        _root_.Geb.Kernel.Tree) =>
                                                                                     x12);
                                                                                 let _ : _root_.List
                                                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                                   (α := _root_.Geb.Kernel.Tree)
                                                                                   (β := _root_.List
                                                                                     _root_.Geb.Kernel.Tree)
                                                                                   x11
                                                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                                                                      (x14 : _root_.List
                                                                                        _root_.Geb.Kernel.Tree) =>
                                                                                     x14);
                                                                                 _root_.GebMirror.DatatypeSoundness.«Datatype.ctorData»
                                                                                   x12
                                                                               else
                                                                                 let _ : _root_.List
                                                                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                                   x10;
                                                                                 _root_.GebMirror.DatatypeSoundness.«Typing.name»
                                                                                   ([] : _root_.List _root_.Geb.Kernel.Tree));
                                         let x9 : _root_.Geb.Kernel.Tree ×
                                           _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e616c6c4a757374»
                                           (_root_.Geb.Kernel.Const.foldr
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.List _root_.Geb.Kernel.Tree)
                                             (fun (x9 : _root_.Geb.Kernel.Tree)
                                                (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                               ((let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.clauseCtor»
                                                   x0
                                                   x9;
                                                 if (_root_.Geb.Kernel.Const.eq
                                                   (_root_.Geb.Kernel.Const.label x11)
                                                   (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                   let x12 : _root_.List
                                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                     x11;
                                                   let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                     (α := _root_.Geb.Kernel.Tree)
                                                     (β := _root_.Geb.Kernel.Tree)
                                                     x12
                                                     (_root_.Geb.Kernel.leaf 0)
                                                     (fun (x13 : _root_.Geb.Kernel.Tree)
                                                        (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                       x13);
                                                   let _ : _root_.List
                                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                     (α := _root_.Geb.Kernel.Tree)
                                                     (β := _root_.List _root_.Geb.Kernel.Tree)
                                                     x12
                                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                     (fun (_ : _root_.Geb.Kernel.Tree)
                                                        (x15 : _root_.List
                                                          _root_.Geb.Kernel.Tree) =>
                                                       x15);
                                                   let x15 : _root_.Geb.Kernel.Tree := x13;
                                                   if (_root_.Geb.Kernel.Const.eq
                                                     (_root_.Geb.Kernel.Const.label x15)
                                                     (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                     let x16 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                       x15;
                                                     let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x16
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x17 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x17);
                                                     let x18 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x16
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x19 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x19);
                                                     let x19 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x18
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x19 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x19);
                                                     let x20 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x18
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x21 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x21);
                                                     let x21 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x20
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x21 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x21);
                                                     let x22 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x20
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x23 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x23);
                                                     let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x22
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x23 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x23);
                                                     let x24 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x22
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x25 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x25);
                                                     let x25 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x24
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x25 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x25);
                                                     let x26 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x24
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x27 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x27);
                                                     let x27 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.Geb.Kernel.Tree)
                                                       x26
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (fun (x27 : _root_.Geb.Kernel.Tree)
                                                          (_ : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x27);
                                                     let _ : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                       (α := _root_.Geb.Kernel.Tree)
                                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                                       x26
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                                          (x29 : _root_.List
                                                            _root_.Geb.Kernel.Tree) =>
                                                         x29);
                                                     let x29 : _root_.List
                                                       _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c»
                                                       (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                                         (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x9)
                                                           (_root_.Geb.Kernel.leaf 0)));
                                                     let x30 : _root_.List
                                                       _root_.Geb.Kernel.Tree := (if (x25).label ≠ 0 then
                                                       _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e617070656e64»
                                                         (_root_.GebMirror.DatatypeSoundness.«Datatype.dropLast»
                                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.dropLast» x29))
                                                         (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65»
                                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                             x29
                                                             (_root_.Geb.Kernel.Const.sub
                                                               (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                                 x29)
                                                               (_root_.Geb.Kernel.leaf 1))))
                                                     else
                                                       x29);
                                                     let x31 : _root_.List _root_.Geb.Kernel.Tree ×
                                                       _root_.List
                                                         _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.splitVars»
                                                       (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x23)
                                                       x27
                                                       x30
                                                       x4;
                                                     if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                       (_root_.Geb.Kernel.Const.eq
                                                         (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x9))
                                                         (_root_.Geb.Kernel.leaf 2))
                                                       (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                         (_root_.GebMirror.DatatypeSoundness.«Datatype.sameName» x21 x8)
                                                         (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                           (_root_.Geb.Kernel.Const.eq
                                                             (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                               x29)
                                                             (_root_.Geb.Kernel.Const.add
                                                               (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                                 (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                                                   x23))
                                                               (_root_.Geb.Kernel.Const.mul
                                                                 (_root_.Geb.Kernel.leaf 2)
                                                                 x25)))
                                                           (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                             (if (x25).label ≠ 0 then
                                                               _root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                                                 (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                                   x29
                                                                   (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                                     (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                                                       x23)))
                                                                 _root_.GebMirror.DatatypeSoundness.«Datatype.kwAmp»
                                                             else
                                                               _root_.Geb.Kernel.leaf 1)
                                                             (_root_.Geb.Kernel.Const.foldr
                                                               (α := _root_.Geb.Kernel.Tree)
                                                               (β := _root_.Geb.Kernel.Tree)
                                                               (fun (x32 : _root_.Geb.Kernel.Tree)
                                                                  (x33 : _root_.Geb.Kernel.Tree) =>
                                                                 _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                   (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                     (_root_.GebMirror.DatatypeSoundness.«Datatype.isAtomTx»
                                                                       x32)
                                                                     (if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                                                       x32
                                                                       _root_.GebMirror.DatatypeSoundness.«Datatype.kwAmp»).label ≠ 0 then
                                                                       _root_.Geb.Kernel.leaf 0
                                                                     else
                                                                       _root_.Geb.Kernel.leaf 1))
                                                                   x33)
                                                               (_root_.Geb.Kernel.leaf 1)
                                                               x30))))).label ≠ 0 then
                                                       _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                                                         (_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                                           ((_root_.GebMirror.DatatypeSoundness.«Datatype.numAtom»
                                                             x19) ::
                                                             ((_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                                               (x31).1) ::
                                                               (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65»
                                                                 (_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                                                   (x31).2)))))
                                                     else
                                                       _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                                   else
                                                     _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                                 else
                                                   let _ : _root_.List
                                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                     x11;
                                                   _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67») ::
                                                 x10))
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (if (x7).label ≠ 0 then
                                               _root_.GebMirror.DatatypeSoundness.«Datatype.dropLast» x2
                                             else
                                               x2));
                                         if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                           (x3).1
                                           (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                             (_root_.Geb.Kernel.Const.lt
                                               (_root_.Geb.Kernel.leaf 0)
                                               x5)
                                             (x9).1)).label ≠ 0 then
                                           (_root_.Geb.Kernel.leaf 1,
                                             (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
                                               (_root_.Geb.Kernel.Const.children x8),
                                               ((x9).2,
                                                 _root_.Geb.Kernel.Const.foldr
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                                   (fun (x10 : _root_.Geb.Kernel.Tree)
                                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                     ((_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                       (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x10)
                                                       (_root_.Geb.Kernel.leaf 1)) ::
                                                       x11))
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (x3).2)))
                                         else
                                           (_root_.Geb.Kernel.leaf 0,
                                             (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
                                               (([] : _root_.List _root_.Geb.Kernel.Tree),
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree)))));
    x5

def «Datatype.expandCase» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.xrAt»
                                          x2
                                          (_root_.Geb.Kernel.leaf 1)
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x3)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x4 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x3;
                                          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x4
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x5 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x4
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x7 : _root_.Geb.Kernel.Tree ×
                                            (_root_.Geb.Kernel.Tree ×
                                              (_root_.List _root_.Geb.Kernel.Tree ×
                                                _root_.List
                                                  _root_.Geb.Kernel.Tree)) := _root_.GebMirror.DatatypeSoundness.«Datatype.clauseParts»
                                            x0
                                            _root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6e6f7468696e67»
                                            (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
                                              (_root_.Geb.Kernel.leaf 2)
                                              x1)
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.xrFrom»
                                              x2
                                              (_root_.Geb.Kernel.leaf 2)
                                              x0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let x8 : _root_.Geb.Kernel.Tree ×
                                            (_root_.List _root_.Geb.Kernel.Tree ×
                                              _root_.List _root_.Geb.Kernel.Tree) := (x7).2;
                                          if ((x7).1).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.tCase»
                                                ((x8).1 ::
                                                  (x5 ::
                                                    ((_root_.GebMirror.DatatypeSoundness.«Typing.tList» ((x8).2).1) ::
                                                      ((x8).2).2))))
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x3;
                                          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»);
    x3

def «Datatype.thTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sArrow»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aUnit»
      x0;
    x1

def «Datatype.splitTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sProd»
      (_root_.GebMirror.DatatypeSoundness.«Datatype.thTy» x0)
      (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» (_root_.GebMirror.DatatypeSoundness.«Datatype.thTy» x0));
    x1

def «Datatype.expandCata» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.atomName»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                            x1
                                            (_root_.Geb.Kernel.leaf 1));
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x1
                                          (_root_.Geb.Kernel.leaf 2);
                                        let x5 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.Geb.Kernel.Tree)
                                                                         (x6 : _root_.Geb.Kernel.Tree) =>
                                          _root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                            (x5 ::
                                              (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65»
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.numAtom»
                                                  (_root_.GebMirror.DatatypeSoundness.«Reader.named» x6 x3)))));
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.xrAt»
                                          x2
                                          (_root_.Geb.Kernel.leaf 3)
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x6)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x7 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
                                          let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x7
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x8 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x7
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.isAtomTx»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                x1
                                                (_root_.Geb.Kernel.leaf 1)))
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.isData» x3 x0)).label ≠ 0 then
                                            let x10 : _root_.Geb.Kernel.Tree ×
                                              (_root_.Geb.Kernel.Tree ×
                                                (_root_.List _root_.Geb.Kernel.Tree ×
                                                  _root_.List
                                                    _root_.Geb.Kernel.Tree)) := _root_.GebMirror.DatatypeSoundness.«Datatype.clauseParts»
                                              x0
                                              (_root_.GebMirror.DatatypeSoundness.«$547970696e672f4f4e616d652e6a757374»
                                                x3)
                                              (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
                                                (_root_.Geb.Kernel.leaf 4)
                                                x1)
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.xrFrom»
                                                x2
                                                (_root_.Geb.Kernel.leaf 4)
                                                x0)
                                              x5;
                                            let x11 : _root_.Geb.Kernel.Tree ×
                                              (_root_.List _root_.Geb.Kernel.Tree ×
                                                _root_.List _root_.Geb.Kernel.Tree) := (x10).2;
                                            if ((x10).1).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                                                (_root_.GebMirror.DatatypeSoundness.«Typing.tCata»
                                                  ((x11).1 ::
                                                    (x4 ::
                                                      (x8 ::
                                                        ((_root_.GebMirror.DatatypeSoundness.«Datatype.defaultOf»
                                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.expandAliases»
                                                            x0
                                                            x4)) ::
                                                          ((_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                                            ((x11).2).1) ::
                                                            ((x11).2).2))))))
                                            else
                                              _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
                                          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»);
    x3

def «Datatype.typeExpanded» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
        (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
          x1
          _root_.GebMirror.DatatypeSoundness.«Datatype.kwDecode»)
        (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 5)))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
        (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
          x1
          _root_.GebMirror.DatatypeSoundness.«Datatype.kwDatum»)
        (_root_.Geb.Kernel.Const.eq
          x2
          (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
      ((_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x3 (_root_.Geb.Kernel.leaf 0)) ::
        ((_root_.GebMirror.DatatypeSoundness.«Datatype.expandAliases»
          x0
          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x3 (_root_.Geb.Kernel.leaf 1))) ::
          (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
            (_root_.Geb.Kernel.leaf 2)
            x3)))
    else
      x3);
    x4

def «Datatype.expandExpr» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.para
      (α := _root_.Unit →
        _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Unit →
             _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let _ : (_root_.Unit →
            _root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
            (_root_.Geb.Kernel.leaf 0,
              fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                _root_.Geb.Kernel.leaf 0),
            x3);
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
          let x7 : _root_.List _root_.Geb.Kernel.Tree := x6;
          (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7,
            fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x7))
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x5 : (_root_.Unit →
              _root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree ×
                    (_root_.List _root_.Geb.Kernel.Tree →
                      _root_.Geb.Kernel.Tree)) := (fun (_ : _root_.Unit) =>
              (_root_.Geb.Kernel.leaf 0,
                fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  _root_.Geb.Kernel.leaf 0),
              x3);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
            let x7 : _root_.List
              (_root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
              (α := _root_.Unit →
                _root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
              (β := _root_.List
                (_root_.Geb.Kernel.Tree ×
                  (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
              (fun (x7 : _root_.Unit →
                   _root_.Geb.Kernel.Tree ×
                     (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
                 (x8 : _root_.List
                   (_root_.Geb.Kernel.Tree ×
                     (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
                ((x7 ()) :: x8))
              ([] : _root_.List (_root_.Geb.Kernel.Tree ×
                (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
              (x5).2;
            let x8 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.xrForms» x7;
            (_root_.GebMirror.DatatypeSoundness.«Typing.tList» x8,
              fun (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                  x8
                  (_root_.Geb.Kernel.leaf 0);
                let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5852732e6c656e677468»
                  x7;
                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                    x10
                    _root_.GebMirror.DatatypeSoundness.«Datatype.kwCase»)
                  (_root_.Geb.Kernel.Const.lt
                    (_root_.Geb.Kernel.leaf 2)
                    x11)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Datatype.expandCase» x9 x8 x7
                else
                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                      x10
                      _root_.GebMirror.DatatypeSoundness.«Datatype.kwCata»)
                    (_root_.Geb.Kernel.Const.lt
                      (_root_.Geb.Kernel.leaf 4)
                      x11)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Datatype.expandCata» x9 x8 x7
                  else
                    let x12 : _root_.Geb.Kernel.Tree ×
                      _root_.List
                        _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.xrFrom»
                      x7
                      (_root_.Geb.Kernel.leaf 0)
                      x9;
                    if ((x12).1).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Datatype.curried»
                        (_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                          (_root_.GebMirror.DatatypeSoundness.«Datatype.typeExpanded» x9 x10 x11 (x12).2))
                    else
                      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»)
          else
            (_root_.GebMirror.DatatypeSoundness.«Typing.tx0»,
              fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                  _root_.GebMirror.DatatypeSoundness.«Typing.tx0»))
      x1
      ()).2
      x0;
    x2

def «Datatype.ctorDecl» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := (let x3 : _root_.List
                                      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.elems» x2;
                                    let x4 : _root_.List
                                      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c»
                                      x3;
                                    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                      x4;
                                    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                      (_root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5)
                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x4
                                          (_root_.Geb.Kernel.Const.sub
                                            x5
                                            (_root_.Geb.Kernel.leaf 2)))
                                        _root_.GebMirror.DatatypeSoundness.«Datatype.kwAmp»);
                                    let x7 : _root_.List
                                      _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
                                      _root_.GebMirror.DatatypeSoundness.«Datatype.dropLast»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.dropLast» x4)
                                    else
                                      x4);
                                    let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                      x7;
                                    let x9 : _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
                                      _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                        x4
                                        (_root_.Geb.Kernel.Const.sub x5 (_root_.Geb.Kernel.leaf 1))
                                    else
                                      _root_.GebMirror.DatatypeSoundness.«Typing.tx0»);
                                    let x10 : _root_.List
                                      _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
                                      (α := _root_.Geb.Kernel.Tree)
                                      (β := _root_.Geb.Kernel.Tree ×
                                        _root_.List _root_.Geb.Kernel.Tree)
                                      (fun (x10 : _root_.Geb.Kernel.Tree)
                                         (x11 : _root_.Geb.Kernel.Tree ×
                                           _root_.List _root_.Geb.Kernel.Tree) =>
                                        (_root_.Geb.Kernel.Const.add
                                          (x11).1
                                          (_root_.Geb.Kernel.leaf 1),
                                          ((_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.fieldAtom»
                                              (_root_.Geb.Kernel.Const.sub
                                                (_root_.Geb.Kernel.Const.sub
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (x11).1))
                                            x10) ::
                                            (x11).2)))
                                      (_root_.Geb.Kernel.leaf 0,
                                        ([] : _root_.List _root_.Geb.Kernel.Tree))
                                      x7).2;
                                    let x11 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
                                      (α := _root_.Geb.Kernel.Tree)
                                      (β := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                                      (fun (x11 : _root_.Geb.Kernel.Tree)
                                         (x12 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
                                        (_root_.Geb.Kernel.Const.add
                                          (x12).1
                                          (_root_.Geb.Kernel.leaf 1),
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aCons»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.ofTy»
                                              x11
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.fieldAtom»
                                                (_root_.Geb.Kernel.Const.sub
                                                  (_root_.Geb.Kernel.Const.sub
                                                    x8
                                                    (_root_.Geb.Kernel.leaf 1))
                                                  (x12).1)))
                                            (x12).2))
                                      (_root_.Geb.Kernel.leaf 0,
                                        if (x6).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.ofTy»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» x9)
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aRest»
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aNil»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                                      x7).2;
                                    let x12 : _root_.List
                                      _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
                                      _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e617070656e64»
                                        x10
                                        (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aRest»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» x9)))
                                    else
                                      x10);
                                    let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.asTy»
                                      (_root_.GebMirror.DatatypeSoundness.«Typing.tAtom»
                                        (_root_.Geb.Kernel.Const.children x0))
                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aNode»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.numAtom» x1)
                                        x11);
                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.isListTx» x2)
                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.isAtomTx»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x3
                                          (_root_.Geb.Kernel.leaf 0))),
                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.ctorD»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.atomName»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)))
                                        x1
                                        x0
                                        (_root_.GebMirror.DatatypeSoundness.«Typing.tList» x7)
                                        x6
                                        x9,
                                        _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aDef»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                            x3
                                            (_root_.Geb.Kernel.leaf 0))
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.curry» x12 x13))));
    x3

def «Datatype.dataDecl» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List
          _root_.Geb.Kernel.Tree) := (let x1 : _root_.List
                                        _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                        x0;
                                      let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.atomName»
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x1
                                          (_root_.Geb.Kernel.leaf 1));
                                      let x3 : _root_.List
                                        _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
                                        (_root_.Geb.Kernel.leaf 2)
                                        x1;
                                      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                        x3;
                                      let x5 : _root_.Geb.Kernel.Tree ×
                                        (_root_.Geb.Kernel.Tree ×
                                          (_root_.List _root_.Geb.Kernel.Tree ×
                                            _root_.List
                                              _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
                                        (α := _root_.Geb.Kernel.Tree)
                                        (β := _root_.Geb.Kernel.Tree ×
                                          (_root_.Geb.Kernel.Tree ×
                                            (_root_.List _root_.Geb.Kernel.Tree ×
                                              _root_.List _root_.Geb.Kernel.Tree)))
                                        (fun (x5 : _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.Geb.Kernel.Tree ×
                                             (_root_.Geb.Kernel.Tree ×
                                               (_root_.List _root_.Geb.Kernel.Tree ×
                                                 _root_.List _root_.Geb.Kernel.Tree))) =>
                                          let x7 : _root_.Geb.Kernel.Tree ×
                                            (_root_.Geb.Kernel.Tree ×
                                              _root_.Geb.Kernel.Tree) := _root_.GebMirror.DatatypeSoundness.«Datatype.ctorDecl»
                                            x2
                                            (_root_.Geb.Kernel.Const.sub
                                              (_root_.Geb.Kernel.Const.sub
                                                x4
                                                (_root_.Geb.Kernel.leaf 1))
                                              (x6).1)
                                            x5;
                                          (_root_.Geb.Kernel.Const.add
                                            (x6).1
                                            (_root_.Geb.Kernel.leaf 1),
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.and» (x7).1 ((x6).2).1,
                                              ((((x7).2).1 :: (((x6).2).2).1),
                                                (((x7).2).2 :: (((x6).2).2).2)))))
                                        (_root_.Geb.Kernel.leaf 0,
                                          (_root_.Geb.Kernel.leaf 1,
                                            (([] : _root_.List _root_.Geb.Kernel.Tree),
                                              ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                        x3;
                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                        ((x5).2).1
                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.isAtomTx»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                            x1
                                            (_root_.Geb.Kernel.leaf 1))),
                                        (((_root_.GebMirror.DatatypeSoundness.«Datatype.dataD» x2) :: (((x5).2).2).1),
                                          ((_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aDeftype»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                              x1
                                              (_root_.Geb.Kernel.leaf 1))
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aT») ::
                                            (((x5).2).2).2))));
    x1

def «Datatype.marker» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.tMarker»
      (x1 ::
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x3 : _root_.Geb.Kernel.Tree)
             (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
            let x5 : _root_.Geb.Kernel.Tree := x3;
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x5)
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              let x6 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
              let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x6
                (_root_.Geb.Kernel.leaf 0)
                (fun (x7 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x7);
              let x8 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x6
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x9);
              let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x8
                (_root_.Geb.Kernel.leaf 0)
                (fun (x9 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x9);
              let x10 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x8
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x11);
              let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x10
                (_root_.Geb.Kernel.leaf 0)
                (fun (x11 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x11);
              let x12 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x10
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x13);
              let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x12
                (_root_.Geb.Kernel.leaf 0)
                (fun (x13 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x13);
              let x14 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x12
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x15);
              let x15 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x14
                (_root_.Geb.Kernel.leaf 0)
                (fun (x15 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x15);
              let x16 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x14
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x17);
              let x17 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x16
                (_root_.Geb.Kernel.leaf 0)
                (fun (x17 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x17);
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x16
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x19 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x19);
              ((_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (x9 ::
                  ((_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.Geb.Kernel.Const.foldr
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      (fun (x19 : _root_.Geb.Kernel.Tree)
                         (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                        ((_root_.GebMirror.DatatypeSoundness.«Datatype.expandAliases» x0 x19) :: x20))
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x13))) ::
                    (x15 ::
                      (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.expandAliases» x0 x17)))))) ::
                x4)
            else
              x4)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x2));
    x3

def «Datatype.xpFail» :=
  (_root_.Geb.Kernel.leaf 0,
    (([] : _root_.List _root_.Geb.Kernel.Tree),
      ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Datatype.xpStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List
          _root_.Geb.Kernel.Tree) := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (x0).1
      (_root_.GebMirror.DatatypeSoundness.«Datatype.isListTx» x1)).label ≠ 0 then
      let x2 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
      let x3 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).2;
      let x4 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.elems» x1;
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
        x4
        (_root_.Geb.Kernel.leaf 0);
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
        x4;
      if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
        x5
        _root_.GebMirror.DatatypeSoundness.«Datatype.kwData»).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            _root_.List
              _root_.Geb.Kernel.Tree) := _root_.GebMirror.DatatypeSoundness.«Datatype.dataDecl»
          x1;
        if ((x7).1).label ≠ 0 then
          let x8 : _root_.List _root_.Geb.Kernel.Tree := ((x7).2).1;
          let x9 : _root_.List _root_.Geb.Kernel.Tree := ((x7).2).2;
          (_root_.Geb.Kernel.leaf 1,
            (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f4465636c732e617070656e64» x2 x8,
              _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e617070656e64»
                (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e72657665727365»
                  (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e617070656e64»
                    ((_root_.GebMirror.DatatypeSoundness.«Typing.tData»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 1))) ::
                      (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c» x9))
                    (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e73696e676c65»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.marker»
                        x2
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 1))
                        x8))))
                x3))
        else
          _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
      else
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
          (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
            x5
            _root_.GebMirror.DatatypeSoundness.«Datatype.kwDefn»)
          (_root_.Geb.Kernel.Const.eq
            x6
            (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.expandExpr»
            x2
            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 4));
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x7)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x8 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
            let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x8
              (_root_.Geb.Kernel.leaf 0)
              (fun (x9 : _root_.Geb.Kernel.Tree)
                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                x9);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x8
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                x11);
            let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
              _root_.GebMirror.DatatypeSoundness.«Datatype.aR»
              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 3))
              x9
              _root_.GebMirror.DatatypeSoundness.«Datatype.aR»;
            (_root_.Geb.Kernel.leaf 1,
              (x2,
                ((_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                  _root_.GebMirror.DatatypeSoundness.«Datatype.aDef»
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.curry»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.bindersTx»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 2)))
                    x11)) ::
                  x3)))
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
            _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
        else
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
            (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx» x5 _root_.GebMirror.DatatypeSoundness.«Reader.kwDef»)
            (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.expandExpr»
              x2
              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 2));
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x7)
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              let x8 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
              let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                x8
                (_root_.Geb.Kernel.leaf 0)
                (fun (x9 : _root_.Geb.Kernel.Tree)
                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                  x9);
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                x8
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (fun (_ : _root_.Geb.Kernel.Tree)
                   (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                  x11);
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  ((_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                    _root_.GebMirror.DatatypeSoundness.«Datatype.aDef»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 1))
                    x9) ::
                    x3)))
            else
              let _ : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
              _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
          else
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
              (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                x5
                _root_.GebMirror.DatatypeSoundness.«Reader.kwDeftype»)
              (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f4465636c732e617070656e64»
                  x2
                  (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f4465636c732e73696e676c65»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.aliasD»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.atomName»
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 1)))
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.expandAliases»
                        x2
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 2))))),
                  (x1 :: x3)))
            else
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                  x5
                  _root_.GebMirror.DatatypeSoundness.«Reader.kwDefnum»)
                (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                (_root_.Geb.Kernel.leaf 1, (x2, (x1 :: x3)))
              else
                _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
    else
      _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»);
    x2

def «Datatype.genericStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List
          _root_.Geb.Kernel.Tree) := (if ((x0).1).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          _root_.List
            _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := (_root_.Geb.Kernel.Tree ×
          (_root_.List _root_.Geb.Kernel.Tree ×
            _root_.List _root_.Geb.Kernel.Tree)) →
          _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree))
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               _root_.List _root_.Geb.Kernel.Tree)) →
             _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree ×
                 _root_.List _root_.Geb.Kernel.Tree))
           (x4 : _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               _root_.List _root_.Geb.Kernel.Tree)) =>
          x3
            (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
              (x4).1
              (_root_.GebMirror.DatatypeSoundness.«Datatype.isListTx» x2)).label ≠ 0 then
              let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x2)
                (_root_.Geb.Kernel.leaf 0);
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                  x5
                  _root_.GebMirror.DatatypeSoundness.«Datatype.kwSort»)
                (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                  x5
                  _root_.GebMirror.DatatypeSoundness.«Datatype.kwPostulate»)).label ≠ 0 then
                (_root_.Geb.Kernel.leaf 1, (((x4).2).1, (x2 :: ((x4).2).2)))
              else
                if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                  x5
                  _root_.GebMirror.DatatypeSoundness.«Datatype.kwGeneric»).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
                else
                  _root_.GebMirror.DatatypeSoundness.«Datatype.xpStep» x4 x2
            else
              _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»))
        (fun (x2 : _root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree ×
               _root_.List _root_.Geb.Kernel.Tree)) =>
          x2)
        (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c»
          (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x1))
        (_root_.Geb.Kernel.leaf 1,
          (((x0).2).1, ([] : _root_.List _root_.Geb.Kernel.Tree)));
      if ((x2).1).label ≠ 0 then
        (_root_.Geb.Kernel.leaf 1,
          (((x0).2).1,
            ((_root_.GebMirror.DatatypeSoundness.«Typing.tGeneric»
              (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e72657665727365»
                ((x2).2).2)) ::
              ((x0).2).2)))
      else
        _root_.GebMirror.DatatypeSoundness.«Datatype.xpFail»
    else
      x0);
    x2

def «Datatype.expandTyped» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree ×
                                     (_root_.List _root_.Geb.Kernel.Tree ×
                                       _root_.List
                                         _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
                                     (α := _root_.Geb.Kernel.Tree)
                                     (β := (_root_.Geb.Kernel.Tree ×
                                       (_root_.List _root_.Geb.Kernel.Tree ×
                                         _root_.List _root_.Geb.Kernel.Tree)) →
                                       _root_.Geb.Kernel.Tree ×
                                         (_root_.List _root_.Geb.Kernel.Tree ×
                                           _root_.List _root_.Geb.Kernel.Tree))
                                     (fun (x1 : _root_.Geb.Kernel.Tree)
                                        (x2 : (_root_.Geb.Kernel.Tree ×
                                          (_root_.List _root_.Geb.Kernel.Tree ×
                                            _root_.List _root_.Geb.Kernel.Tree)) →
                                          _root_.Geb.Kernel.Tree ×
                                            (_root_.List _root_.Geb.Kernel.Tree ×
                                              _root_.List _root_.Geb.Kernel.Tree))
                                        (x3 : _root_.Geb.Kernel.Tree ×
                                          (_root_.List _root_.Geb.Kernel.Tree ×
                                            _root_.List _root_.Geb.Kernel.Tree)) =>
                                       x2
                                         (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.isListTx» x1)
                                           (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                             (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                               (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x1)
                                               (_root_.Geb.Kernel.leaf 0))
                                             _root_.GebMirror.DatatypeSoundness.«Datatype.kwGeneric»)).label ≠ 0 then
                                           _root_.GebMirror.DatatypeSoundness.«Datatype.genericStep» x3 x1
                                         else
                                           _root_.GebMirror.DatatypeSoundness.«Datatype.xpStep» x3 x1))
                                     (fun (x1 : _root_.Geb.Kernel.Tree ×
                                          (_root_.List _root_.Geb.Kernel.Tree ×
                                            _root_.List _root_.Geb.Kernel.Tree)) =>
                                       x1)
                                     x0
                                     (_root_.Geb.Kernel.leaf 1,
                                       (([] : _root_.List _root_.Geb.Kernel.Tree),
                                         ([] : _root_.List _root_.Geb.Kernel.Tree)));
                                   ((x1).1,
                                     _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e72657665727365»
                                       ((x1).2).2));
    x1

def «Datatype.eraseChain» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x7 : _root_.Geb.Kernel.Tree := x3
          x4
          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 0));
        if (_root_.Geb.Kernel.Const.lt
          (_root_.Geb.Kernel.leaf 1)
          (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
            x6)).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Datatype.sIf»
            (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
              _root_.GebMirror.DatatypeSoundness.«Datatype.aEq»
              (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2» _root_.GebMirror.DatatypeSoundness.«Datatype.aLabel» x0)
              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x4)
                (_root_.Geb.Kernel.leaf 0)))
            x7
            (x5 (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e7461696c» x6))
        else
          x7)
      (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x4 (_root_.Geb.Kernel.leaf 0))
      x1
      x2;
    x4

def «Datatype.numOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.numeral»
                                          (_root_.Geb.Kernel.Const.children x0);
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.get» x1
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «Datatype.bindVars» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                          x2;
                                        _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x0
                                          (_root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x1
                                            x3
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                x4
                                                (_root_.Geb.Kernel.leaf 2))))
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                              x4
                                              (_root_.Geb.Kernel.leaf 1))));
    x4

def «Datatype.fieldLet» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
      x0
      (_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 95])).label ≠ 0 then
      x3
    else
      _root_.GebMirror.DatatypeSoundness.«Datatype.sLet» x0 x1 x2 x3);
    x4

def «Datatype.eraseCase» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aS»
      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
      (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x0 (_root_.Geb.Kernel.leaf 1))
      (_root_.GebMirror.DatatypeSoundness.«Datatype.eraseChain»
        _root_.GebMirror.DatatypeSoundness.«Datatype.aS»
        (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x0 (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
          (_root_.Geb.Kernel.leaf 3)
          x0)
        (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
            _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
            (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
            (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
              _root_.GebMirror.DatatypeSoundness.«Datatype.aChildren»
              _root_.GebMirror.DatatypeSoundness.«Datatype.aS»)
            (_root_.GebMirror.DatatypeSoundness.«Datatype.bindVars»
              (fun (x3 : _root_.Geb.Kernel.Tree) (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                  x3
                  _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sHeadOf» _root_.GebMirror.DatatypeSoundness.«Datatype.aC»)
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                    _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sTailOf» _root_.GebMirror.DatatypeSoundness.«Datatype.aC»)
                    x4))
              (fun (x3 : _root_.Geb.Kernel.Tree) (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                  x3
                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                  _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                  x4)
              x1
              x2)));
    x1

def «Datatype.eraseCata» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x0
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                          x0
                                          (_root_.Geb.Kernel.leaf 3);
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.thTy»
                                          x1;
                                        _root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                          (_root_.GebMirror.DatatypeSoundness.«Datatype.sx4»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aPara»
                                            x3
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam2»
                                              _root_.GebMirror.DatatypeSoundness.«Datatype.aO»
                                              _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
                                              _root_.GebMirror.DatatypeSoundness.«Datatype.aK»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» x3)
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam1»
                                                _root_.GebMirror.DatatypeSoundness.«Datatype.aU»
                                                _root_.GebMirror.DatatypeSoundness.«Datatype.aUnit»
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.eraseChain»
                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aO»
                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                      x0
                                                      (_root_.Geb.Kernel.leaf 4)))
                                                  (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e64726f70»
                                                    (_root_.Geb.Kernel.leaf 5)
                                                    x0)
                                                  (fun (x4 : _root_.Geb.Kernel.Tree)
                                                     (x5 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aQ»
                                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.splitTy» x1)
                                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aPair»
                                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam1»
                                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aU»
                                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aUnit»
                                                          x2)
                                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aK»)
                                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aChildren»
                                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aO»)
                                                        (_root_.GebMirror.DatatypeSoundness.«Datatype.bindVars»
                                                          (fun (x6 : _root_.Geb.Kernel.Tree)
                                                             (x7 : _root_.Geb.Kernel.Tree) =>
                                                            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x6)
                                                              (_root_.Geb.Kernel.leaf 0);
                                                            _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                                                              _root_.GebMirror.DatatypeSoundness.«Datatype.aQ»
                                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.splitTy» x1)
                                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.sx6»
                                                                _root_.GebMirror.DatatypeSoundness.«Datatype.aLcase»
                                                                x3
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.splitTy»
                                                                  x1)
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aSnd»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aQ»)
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aPair»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam1»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aU»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aUnit»
                                                                    x2)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aNil»
                                                                    x3))
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam2»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
                                                                  x3
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aTl»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                    x3)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aPair»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aTl»)))
                                                              (if (_root_.GebMirror.DatatypeSoundness.«Datatype.numOf»
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.elems»
                                                                    x6)
                                                                  (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                                _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                                                                  x8
                                                                  x1
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aFst»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aQ»)
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aUnitV»)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sTailOf»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aC»)
                                                                    x7)
                                                              else
                                                                _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                                                                  x8
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sHeadOf»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aC»)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sTailOf»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aC»)
                                                                    x7)))
                                                          (fun (x6 : _root_.Geb.Kernel.Tree)
                                                             (x7 : _root_.Geb.Kernel.Tree) =>
                                                            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x6)
                                                              (_root_.Geb.Kernel.leaf 0);
                                                            if (_root_.GebMirror.DatatypeSoundness.«Datatype.numOf»
                                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x6)
                                                                (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                              _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                                                                x8
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sList» x1)
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sx6»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aFoldr»
                                                                  x3
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                    x1)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sLam2»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
                                                                    x3
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aA»
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                      x1)
                                                                    (_root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aCons»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aH»
                                                                        _root_.GebMirror.DatatypeSoundness.«Datatype.aUnitV»)
                                                                      _root_.GebMirror.DatatypeSoundness.«Datatype.aA»))
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aNil»
                                                                    x1)
                                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aSnd»
                                                                    _root_.GebMirror.DatatypeSoundness.«Datatype.aQ»))
                                                                x7
                                                            else
                                                              _root_.GebMirror.DatatypeSoundness.«Datatype.fieldLet»
                                                                x8
                                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.sList»
                                                                  _root_.GebMirror.DatatypeSoundness.«Datatype.aT»)
                                                                _root_.GebMirror.DatatypeSoundness.«Datatype.aC»
                                                                x7)
                                                          x4
                                                          x5))))))
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                              x0
                                              (_root_.Geb.Kernel.leaf 2)))
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.aUnitV»);
    x1

def «Datatype.eraseExpr» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
         (_ : _root_.Unit) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
          let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
            _root_.Geb.Kernel.leaf 0,
            x2);
          let x5 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
          let x6 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Unit → _root_.Geb.Kernel.Tree)
            (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
            (x4).2
            (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
              ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
            (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
               (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
              (x6, x7));
          let _ : _root_.Geb.Kernel.Tree := (x6).1 ();
          let x8 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x5
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
              x9);
          let x9 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
            _root_.List
              (_root_.Unit →
                _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Unit → _root_.Geb.Kernel.Tree)
            (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
            (x6).2
            (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
              ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
            (fun (x9 : _root_.Unit → _root_.Geb.Kernel.Tree)
               (x10 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
              (x9, x10));
          let x10 : _root_.Geb.Kernel.Tree := (x9).1 ();
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x8
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
              x12);
          x10
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
            let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
              _root_.Geb.Kernel.leaf 0,
              x2);
            let x5 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
            let x6 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Unit → _root_.Geb.Kernel.Tree)
              (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
              (x4).2
              (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
              (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                 (x7 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                (x6, x7));
            let _ : _root_.Geb.Kernel.Tree := (x6).1 ();
            let x8 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x5
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                x9);
            let x9 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
              _root_.List
                (_root_.Unit →
                  _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Unit → _root_.Geb.Kernel.Tree)
              (β := (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree))
              (x6).2
              (fun (_ : _root_.Unit) => _root_.Geb.Kernel.leaf 0,
                ([] : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)))
              (fun (x9 : _root_.Unit → _root_.Geb.Kernel.Tree)
                 (x10 : _root_.List (_root_.Unit → _root_.Geb.Kernel.Tree)) =>
                (x9, x10));
            let x10 : _root_.Geb.Kernel.Tree := (x9).1 ();
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x8
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                x12);
            x10
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x1)
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              let _ : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                _root_.List
                  (_root_.Unit →
                    _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                _root_.Geb.Kernel.leaf 0,
                x2);
              let x5 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
              let x6 : _root_.List _root_.Geb.Kernel.Tree := x5;
              _root_.GebMirror.DatatypeSoundness.«Typing.tAtom» x6
            else
              if (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.label x1)
                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                  _root_.List
                    (_root_.Unit →
                      _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                  _root_.Geb.Kernel.leaf 0,
                  x2);
                let _ : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                let x6 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                  (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                  (β := _root_.List _root_.Geb.Kernel.Tree)
                  (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                     (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                    ((x6 ()) :: x7))
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (x4).2;
                _root_.GebMirror.DatatypeSoundness.«Datatype.eraseCase» x6
              else
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                  let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                    _root_.List
                      (_root_.Unit →
                        _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                    _root_.Geb.Kernel.leaf 0,
                    x2);
                  let _ : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                  let x6 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                    (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                    (β := _root_.List _root_.Geb.Kernel.Tree)
                    (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                       (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                      ((x6 ()) :: x7))
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (x4).2;
                  _root_.GebMirror.DatatypeSoundness.«Datatype.eraseCata» x6
                else
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x1)
                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                    let x4 : (_root_.Unit → _root_.Geb.Kernel.Tree) ×
                      _root_.List
                        (_root_.Unit →
                          _root_.Geb.Kernel.Tree) := (fun (_ : _root_.Unit) =>
                      _root_.Geb.Kernel.leaf 0,
                      x2);
                    let _ : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                    let x6 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                      (α := _root_.Unit → _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      (fun (x6 : _root_.Unit → _root_.Geb.Kernel.Tree)
                         (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                        ((x6 ()) :: x7))
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (x4).2;
                    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                      x6;
                    let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                      x6
                      (_root_.Geb.Kernel.leaf 0);
                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                      (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx» x8 _root_.GebMirror.DatatypeSoundness.«Datatype.kwRep»)
                      (_root_.Geb.Kernel.Const.eq
                        x7
                        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Datatype.sx1»
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 1))
                    else
                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                        (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                          x8
                          _root_.GebMirror.DatatypeSoundness.«Datatype.kwDecode»)
                        (_root_.Geb.Kernel.Const.eq
                          x7
                          (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Datatype.sLet»
                          _root_.GebMirror.DatatypeSoundness.«Datatype.aE»
                          _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
                          (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 2))
                          (_root_.GebMirror.DatatypeSoundness.«Datatype.sIf»
                            (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                              (_root_.GebMirror.DatatypeSoundness.«Datatype.memberAtom»
                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 1)))
                              _root_.GebMirror.DatatypeSoundness.«Datatype.aE»)
                            (_root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                              (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 3))
                              _root_.GebMirror.DatatypeSoundness.«Datatype.aE»)
                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 4)))
                      else
                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                          (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                            x8
                            _root_.GebMirror.DatatypeSoundness.«Datatype.kwDatum»)
                          (_root_.Geb.Kernel.Const.eq
                            x7
                            (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Datatype.sx2»
                            _root_.GebMirror.DatatypeSoundness.«Datatype.aQuote»
                            (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx» x6 (_root_.Geb.Kernel.leaf 2))
                        else
                          _root_.GebMirror.DatatypeSoundness.«Typing.tList» x6
                  else
                    _root_.GebMirror.DatatypeSoundness.«Typing.tx0»)
      x0
      ();
    x1

def «Datatype.eraseForm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aDeftype»
                                            x3
                                            _root_.GebMirror.DatatypeSoundness.«Datatype.aT»
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                            let x2 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x1;
                                            let x3 : _root_.List _root_.Geb.Kernel.Tree := x2;
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e6c656e677468»
                                                  x3)
                                                (_root_.Geb.Kernel.leaf 3))
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.namedTx»
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 0))
                                                _root_.GebMirror.DatatypeSoundness.«Reader.kwDef»)).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Datatype.sx3»
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.eraseExpr»
                                                  (_root_.GebMirror.DatatypeSoundness.«Datatype.nthTx»
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 2)))
                                            else
                                              x0
                                          else
                                            x0);
    x1

def «Datatype.markersFirst» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.List _root_.Geb.Kernel.Tree ×
                                   _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree ×
                                     _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (x1 : _root_.Geb.Kernel.Tree)
                                      (x2 : _root_.List _root_.Geb.Kernel.Tree ×
                                        _root_.List _root_.Geb.Kernel.Tree) =>
                                     let x3 : _root_.Geb.Kernel.Tree := x1;
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.Geb.Kernel.Const.label x3)
                                       (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                       let x4 : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                         x3;
                                       let _ : _root_.List _root_.Geb.Kernel.Tree := x4;
                                       ((x1 :: (x2).1), (x2).2)
                                     else
                                       ((x2).1, (x1 :: (x2).2)))
                                   (([] : _root_.List _root_.Geb.Kernel.Tree),
                                     ([] : _root_.List _root_.Geb.Kernel.Tree))
                                   x0;
                                 _root_.GebMirror.DatatypeSoundness.«$44617461747970652f5478732e617070656e64»
                                   (x1).1
                                   (x1).2);
    x1

def «Datatype.kernelForms» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let _ : _root_.List _root_.Geb.Kernel.Tree := x4; x2
        else
          ((_root_.GebMirror.DatatypeSoundness.«Datatype.eraseForm» x1) :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Datatype.expandChecked» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree ×
                                          _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.expandTyped»
                                          x0;
                                        if ((x1).1).label ≠ 0 then
                                          let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.checkForms»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.markersFirst» (x1).2);
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x2)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x3 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x2;
                                            let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x3
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x4 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x4);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x3
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x6);
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x2;
                                            _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6a757374»
                                              (_root_.GebMirror.DatatypeSoundness.«Typing.tList»
                                                (_root_.GebMirror.DatatypeSoundness.«Datatype.kernelForms» (x1).2))
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«$44617461747970652f4f54782e6e6f7468696e67»);
    x1

def «Datatype.expandProgram» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                                          (_root_.Geb.Kernel.leaf 2)
                                          x0;
                                        if (_root_.GebMirror.DatatypeSoundness.«Typing.Tx.member» x1).label ≠ 0 then
                                          let x2 : _root_.Geb.Kernel.Tree := x1;
                                          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.expandChecked»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x2);
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x3)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x4 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x3;
                                            let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x4
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x5 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x5);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x4
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x7);
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                              (_root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 0)
                                                (_root_.Geb.Kernel.Const.children x5))
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x3;
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»
                                        else
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x1

def «Datatype.typeErrorOfForms» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                                          (_root_.Geb.Kernel.leaf 2)
                                          x0;
                                        if (_root_.GebMirror.DatatypeSoundness.«Typing.Tx.member» x1).label ≠ 0 then
                                          let x2 : _root_.Geb.Kernel.Tree := x1;
                                          let x3 : _root_.Geb.Kernel.Tree ×
                                            _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Datatype.expandTyped»
                                            (_root_.GebMirror.DatatypeSoundness.«Datatype.elems» x2);
                                          if ((x3).1).label ≠ 0 then
                                            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Typing.checkForms»
                                              (_root_.GebMirror.DatatypeSoundness.«Datatype.markersFirst» (x3).2);
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x4)
                                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                              let x5 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x4;
                                              let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.Geb.Kernel.Tree)
                                                x5
                                                (_root_.Geb.Kernel.leaf 0)
                                                (fun (x6 : _root_.Geb.Kernel.Tree)
                                                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                  x6);
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.List _root_.Geb.Kernel.Tree)
                                                x5
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (fun (_ : _root_.Geb.Kernel.Tree)
                                                   (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                  x8);
                                              x6
                                            else
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x4;
                                              _root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 0)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          else
                                            _root_.Geb.Kernel.Const.node
                                              (_root_.Geb.Kernel.leaf 0)
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                        else
                                          _root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Datatype.typeErrorOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.readSExps»
                                          (_root_.Geb.Kernel.Const.children x0);
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Datatype.typeErrorOfForms»
                                            (_root_.Geb.Kernel.Const.children
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1))
                                        else
                                          _root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Recognize.sx» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 2) x0

def «Recognize.s2» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (x0 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1))

def «Recognize.s3» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (x0 :: (x1 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2)))

def «Recognize.s4» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (x0 :: (x1 :: (x2 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x3))))

def «Recognize.num» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.DatatypeSoundness.«Typing.decimalChars» x0)

def «Recognize.rT» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 84]

def «Recognize.rList» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 76,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 116]

def «Recognize.rLam» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 109]

def «Recognize.rLet» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 116]

def «Recognize.rIf» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 102]

def «Recognize.rDef» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 102]

def «Recognize.rFold» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100]

def «Recognize.rFoldr» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 114]

def «Recognize.rIter» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 114]

def «Recognize.rLcase» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 115,
    _root_.Geb.Kernel.leaf 101]

def «Recognize.rNil» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 108]

def «Recognize.rCons» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 115]

def «Recognize.rNode» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 110,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 101]

def «Recognize.rChild» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 99,
    _root_.Geb.Kernel.leaf 104,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100]

def «Recognize.rArity» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 105,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 121]

def «Recognize.rEq» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 101,
    _root_.Geb.Kernel.leaf 113]

def «Recognize.rLt» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 116]

def «Recognize.rAdd» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 97,
    _root_.Geb.Kernel.leaf 100,
    _root_.Geb.Kernel.leaf 100]

def «Recognize.vT» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 116]

def «Recognize.vL» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 108]

def «Recognize.vR» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 114]

def «Recognize.vN» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 110]

def «Recognize.vC» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 99]

def «Recognize.vA» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 97]

def «Recognize.vX» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 120]

def «Recognize.vH» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 104]

def «Recognize.vU» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 117]

def «Recognize.zero» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 48]

def «Recognize.one» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 49]

def «Recognize.tList» :=
  _root_.GebMirror.DatatypeSoundness.«Recognize.s2»
    _root_.GebMirror.DatatypeSoundness.«Recognize.rList»
    _root_.GebMirror.DatatypeSoundness.«Recognize.rT»

def «Recognize.bind1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.s2» x0 x1))

def «Recognize.bind2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      ((_root_.GebMirror.DatatypeSoundness.«Recognize.s2» x0 x1) ::
        (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
          (_root_.GebMirror.DatatypeSoundness.«Recognize.s2» x2 x3)))

def «Recognize.conj» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.equal
      x0
      _root_.GebMirror.DatatypeSoundness.«Recognize.one»).label ≠ 0 then
      x1
    else
      if (_root_.Geb.Kernel.Const.equal
        x1
        _root_.GebMirror.DatatypeSoundness.«Recognize.one»).label ≠ 0 then
        x0
      else
        _root_.GebMirror.DatatypeSoundness.«Recognize.s4»
          _root_.GebMirror.DatatypeSoundness.«Recognize.rIf»
          x0
          x1
          _root_.GebMirror.DatatypeSoundness.«Recognize.zero»

def «Recognize.bitOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.s3»
      _root_.GebMirror.DatatypeSoundness.«Recognize.rChild»
      x0
      (_root_.GebMirror.DatatypeSoundness.«Recognize.num» x1)

def «Recognize.tailE» :=
  _root_.GebMirror.DatatypeSoundness.«Recognize.s3»
    _root_.GebMirror.DatatypeSoundness.«Recognize.rLam»
    (_root_.GebMirror.DatatypeSoundness.«Recognize.bind1»
      _root_.GebMirror.DatatypeSoundness.«Recognize.vX»
      _root_.GebMirror.DatatypeSoundness.«Recognize.tList»)
    (_root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (_root_.GebMirror.DatatypeSoundness.«Recognize.rLcase» ::
        (_root_.GebMirror.DatatypeSoundness.«Recognize.rT» ::
          (_root_.GebMirror.DatatypeSoundness.«Recognize.tList» ::
            (_root_.GebMirror.DatatypeSoundness.«Recognize.vX» ::
              ((_root_.GebMirror.DatatypeSoundness.«Recognize.s2»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rNil»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rT») ::
                (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                  (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                    _root_.GebMirror.DatatypeSoundness.«Recognize.rLam»
                    (_root_.GebMirror.DatatypeSoundness.«Recognize.bind2»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.vH»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.rT»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.vU»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.tList»)
                    _root_.GebMirror.DatatypeSoundness.«Recognize.vU»))))))))

def «Recognize.dropE» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Recognize.sx»
      (_root_.GebMirror.DatatypeSoundness.«Recognize.rIter» ::
        (_root_.GebMirror.DatatypeSoundness.«Recognize.tList» ::
          (_root_.GebMirror.DatatypeSoundness.«Recognize.tailE» ::
            (_root_.GebMirror.DatatypeSoundness.«Recognize.vR» ::
              (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                (_root_.GebMirror.DatatypeSoundness.«Recognize.num» x0))))))

def «Recognize.markers» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
          (x1 :: x2)
        else
          x2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Recognize.markerOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal
          (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))
          x1).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some» x2
        else
          x3)
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      x0

def «Recognize.fieldTypes» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.append»
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 3)))
    else
      _root_.Geb.Kernel.Const.children
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1))

def «Recognize.depsOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x4 : _root_.Geb.Kernel.Tree)
             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
              (_root_.GebMirror.DatatypeSoundness.«Recognize.markerOf» x0 x4)).label ≠ 0 then
              (x4 :: x5)
            else
              x5)
          x3
          (_root_.GebMirror.DatatypeSoundness.«Recognize.fieldTypes» x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.tail» (_root_.Geb.Kernel.Const.children x1))

def «Recognize.addNew» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
          (_root_.GebMirror.DatatypeSoundness.«Reader.indexOf» x2 x3)).label ≠ 0 then
          x3
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.append»
            x3
            (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2))
      x1
      (_root_.GebMirror.DatatypeSoundness.«Prelude.reverse» x0)

def «Recognize.closure» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x3 : _root_.Geb.Kernel.Tree)
             (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
            let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.markerOf»
              x0
              x3;
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x5).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Recognize.addNew»
                (_root_.GebMirror.DatatypeSoundness.«Recognize.depsOf»
                  x0
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x5))
                x4
            else
              x4)
          x2
          x2)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x0)

def «Recognize.fieldTest» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.DatatypeSoundness.«Reader.named»
      x1
      _root_.GebMirror.DatatypeSoundness.«Reader.kwT»).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some» _root_.GebMirror.DatatypeSoundness.«Recognize.one»
    else
      let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.indexOf»
        x1
        x0;
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.GebMirror.DatatypeSoundness.«Recognize.bitOf»
            x2
            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Recognize.ctorTest» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
      (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1));
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.length» x2;
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.child
      x1
      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Recognize.s3»
        _root_.GebMirror.DatatypeSoundness.«Recognize.rLt»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.num» x3)
        (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
          _root_.GebMirror.DatatypeSoundness.«Recognize.rAdd»
          (_root_.GebMirror.DatatypeSoundness.«Recognize.s2»
            _root_.GebMirror.DatatypeSoundness.«Recognize.rArity»
            _root_.GebMirror.DatatypeSoundness.«Recognize.vN»)
          _root_.GebMirror.DatatypeSoundness.«Recognize.one»)
    else
      _root_.GebMirror.DatatypeSoundness.«Recognize.s3»
        _root_.GebMirror.DatatypeSoundness.«Recognize.rEq»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.s2»
          _root_.GebMirror.DatatypeSoundness.«Recognize.rArity»
          _root_.GebMirror.DatatypeSoundness.«Recognize.vN»)
        (_root_.GebMirror.DatatypeSoundness.«Recognize.num» x3));
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
        (fun (x5 : _root_.Geb.Kernel.Tree)
           (x6 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
          (_root_.Geb.Kernel.Const.sub (x6).1 (_root_.Geb.Kernel.leaf 1),
            ((_root_.GebMirror.DatatypeSoundness.«Recognize.fieldTest»
              x0
              x5
              (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rChild»
                _root_.GebMirror.DatatypeSoundness.«Recognize.vN»
                (_root_.GebMirror.DatatypeSoundness.«Recognize.num»
                  (_root_.Geb.Kernel.Const.sub (x6).1 (_root_.Geb.Kernel.leaf 1))))) ::
              (x6).2)))
        (x3, ([] : _root_.List _root_.Geb.Kernel.Tree))
        x2).2;
    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.child
      x1
      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.fieldTest»
        x0
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 3))
        _root_.GebMirror.DatatypeSoundness.«Recognize.vC»;
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x6).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)
          _root_.GebMirror.DatatypeSoundness.«Recognize.one»).label ≠ 0 then
          x6
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.GebMirror.DatatypeSoundness.«Recognize.sx»
              (_root_.GebMirror.DatatypeSoundness.«Recognize.rFoldr» ::
                (_root_.GebMirror.DatatypeSoundness.«Recognize.rT» ::
                  (_root_.GebMirror.DatatypeSoundness.«Recognize.rT» ::
                    ((_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.rLam»
                      (_root_.GebMirror.DatatypeSoundness.«Recognize.bind2»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.vC»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.rT»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.vA»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.rT»)
                      (_root_.GebMirror.DatatypeSoundness.«Recognize.s4»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.rIf»
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)
                        _root_.GebMirror.DatatypeSoundness.«Recognize.vA»
                        _root_.GebMirror.DatatypeSoundness.«Recognize.zero»)) ::
                      (_root_.GebMirror.DatatypeSoundness.«Recognize.one» ::
                        (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                          (_root_.GebMirror.DatatypeSoundness.«Recognize.dropE» x3))))))))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.some» _root_.GebMirror.DatatypeSoundness.«Recognize.one»);
    if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x5 x6).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.conj»
          x4
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            _root_.GebMirror.DatatypeSoundness.«Recognize.conj»
            (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)
            (_root_.Geb.Kernel.Const.children (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x5))))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Recognize.dataTest» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.ctorTest»
          x0
          x2;
        if (_root_.GebMirror.DatatypeSoundness.«Reader.both» x4 x3).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.GebMirror.DatatypeSoundness.«Recognize.s4»
              _root_.GebMirror.DatatypeSoundness.«Recognize.rIf»
              (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rEq»
                _root_.GebMirror.DatatypeSoundness.«Recognize.vL»
                (_root_.GebMirror.DatatypeSoundness.«Recognize.num»
                  (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))))
              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x4)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3))
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.some» _root_.GebMirror.DatatypeSoundness.«Recognize.zero»)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.tail» (_root_.Geb.Kernel.Const.children x1))

def «Recognize.recognizer» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.closure»
      x0
      (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0));
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x3 : _root_.Geb.Kernel.Tree)
           (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.markerOf»
            x0
            x3;
          ((if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x5).label ≠ 0 then
            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.dataTest»
              x2
              (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x5);
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x6).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.GebMirror.DatatypeSoundness.«Recognize.s4»
                  _root_.GebMirror.DatatypeSoundness.«Recognize.rIf»
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x6)
                  _root_.GebMirror.DatatypeSoundness.«Recognize.one»
                  _root_.GebMirror.DatatypeSoundness.«Recognize.zero»)
            else
              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none») ::
            x4))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x2);
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.s3»
        _root_.GebMirror.DatatypeSoundness.«Recognize.rLam»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.bind2»
          _root_.GebMirror.DatatypeSoundness.«Recognize.vL»
          _root_.GebMirror.DatatypeSoundness.«Recognize.rT»
          _root_.GebMirror.DatatypeSoundness.«Recognize.vR»
          _root_.GebMirror.DatatypeSoundness.«Recognize.tList»)
        (_root_.GebMirror.DatatypeSoundness.«Recognize.sx»
          (_root_.GebMirror.DatatypeSoundness.«Recognize.rLet» ::
            (_root_.GebMirror.DatatypeSoundness.«Recognize.vN» ::
              (_root_.GebMirror.DatatypeSoundness.«Recognize.rT» ::
                ((_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                  _root_.GebMirror.DatatypeSoundness.«Recognize.rNode»
                  _root_.GebMirror.DatatypeSoundness.«Recognize.zero»
                  _root_.GebMirror.DatatypeSoundness.«Recognize.vR») ::
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                    (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.rNode»
                      _root_.GebMirror.DatatypeSoundness.«Recognize.zero»
                      (_root_.Geb.Kernel.Const.foldr
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        (fun (x4 : _root_.Geb.Kernel.Tree) (x5 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.DatatypeSoundness.«Recognize.s3» _root_.GebMirror.DatatypeSoundness.«Recognize.rCons» x4 x5)
                        (_root_.GebMirror.DatatypeSoundness.«Recognize.s2»
                          _root_.GebMirror.DatatypeSoundness.«Recognize.rNil»
                          _root_.GebMirror.DatatypeSoundness.«Recognize.rT»)
                        (_root_.Geb.Kernel.Const.children
                          (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3))))))))));
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
          _root_.GebMirror.DatatypeSoundness.«Recognize.rDef»
          (_root_.GebMirror.DatatypeSoundness.«Datatype.memberName»
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.DatatypeSoundness.«Recognize.s3»
            _root_.GebMirror.DatatypeSoundness.«Recognize.rLam»
            (_root_.GebMirror.DatatypeSoundness.«Recognize.bind1»
              _root_.GebMirror.DatatypeSoundness.«Recognize.vT»
              _root_.GebMirror.DatatypeSoundness.«Recognize.rT»)
            (_root_.GebMirror.DatatypeSoundness.«Recognize.bitOf»
              (_root_.GebMirror.DatatypeSoundness.«Recognize.s4»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rFold»
                _root_.GebMirror.DatatypeSoundness.«Recognize.rT»
                x4
                _root_.GebMirror.DatatypeSoundness.«Recognize.vT»)
              (_root_.Geb.Kernel.leaf 0))))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Recognize.occurs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal x2 x0).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          _root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            _root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.Geb.Kernel.leaf 0)
            x3)
      x1

def «Recognize.recognizersAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x2)
      (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x3 : _root_.Geb.Kernel.Tree) (x4 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.GebMirror.DatatypeSoundness.«Recognize.occurs»
              (_root_.GebMirror.DatatypeSoundness.«Datatype.memberName»
                (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0)))
              x3)
            x4)
        (_root_.Geb.Kernel.leaf 0)
        x1).label ≠ 0 then
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.recognizer»
          x0
          x2;
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x3).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.DatatypeSoundness.«Prelude.single» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x3)))
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2))

def «Recognize.insertRecognizers» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Recognize.markers» x0;
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((_root_.GebMirror.DatatypeSoundness.«Recognize.recognizersAt» x1 x0 x2) :: x3))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x0);
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x2).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            (fun (x3 : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                (_root_.Geb.Kernel.Const.children x3)
                x4)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.Geb.Kernel.Const.children (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x2))))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»

def «Subst.mk1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      x0
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1);
    x2

def «Subst.var» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.mk1»
      (_root_.Geb.Kernel.leaf 8)
      x0;
    x1

def «Subst.trTrees» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x1).1 :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Subst.trAll» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (((x2).2 x1) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x2

def «Subst.termNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 10))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 11))
        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 12))
          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
            (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 13))
            (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
              (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 14))
              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 16))
                (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 20)))))));
    x1

def «Subst.trav» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.trTrees» x4;
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.length» x5;
        (_root_.Geb.Kernel.Const.node x3 x5,
          fun (x7 : _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
              (_root_.Geb.Kernel.Const.eq x3 (_root_.Geb.Kernel.leaf 8))
              (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
              x0
                x7
                (_root_.Geb.Kernel.Const.label
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
            else
              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                (_root_.Geb.Kernel.Const.eq x3 (_root_.Geb.Kernel.leaf 9))
                (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Reader.node2»
                  (_root_.Geb.Kernel.leaf 9)
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0))
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
                    (_root_.GebMirror.DatatypeSoundness.«Subst.trAll»
                      x4
                      (_root_.Geb.Kernel.Const.add x7 (_root_.Geb.Kernel.leaf 1)))
                    (_root_.Geb.Kernel.leaf 1))
              else
                if (_root_.GebMirror.DatatypeSoundness.«Subst.termNode» x3).label ≠ 0 then
                  _root_.Geb.Kernel.Const.node x3 (_root_.GebMirror.DatatypeSoundness.«Subst.trAll» x4 x7)
                else
                  _root_.Geb.Kernel.Const.node x3 x5))
      x1).2
      x2;
    x3

def «Subst.wkVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.var»
      (if (_root_.Geb.Kernel.Const.lt x2 x1).label ≠ 0 then
        x2
      else
        _root_.Geb.Kernel.Const.add x2 x0);
    x3

def «Subst.wk» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.trav»
      (_root_.GebMirror.DatatypeSoundness.«Subst.wkVar» x0)
      x1
      (_root_.Geb.Kernel.leaf 0);
    x2

def «Subst.wkAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.trav»
      (_root_.GebMirror.DatatypeSoundness.«Subst.wkVar» x1)
      x2
      x0;
    x3

def «Subst.substVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x2
      x1).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Subst.var» x2
    else
      if (_root_.Geb.Kernel.Const.eq x2 x1).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Subst.wk» x1 x0
      else
        _root_.GebMirror.DatatypeSoundness.«Subst.var»
          (_root_.Geb.Kernel.Const.sub x2 (_root_.Geb.Kernel.leaf 1)));
    x3

def «Subst.subst» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Subst.trav»
      (_root_.GebMirror.DatatypeSoundness.«Subst.substVar» x0)
      x1
      (_root_.Geb.Kernel.leaf 0);
    x2

def «Eval.bindO» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x0)
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x2

def «Eval.mapT» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «Eval.allSomeT» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x1).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
            x2
            (fun (x3 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ((_root_.GebMirror.DatatypeSoundness.«Prelude.get» x1) ::
                    (_root_.Geb.Kernel.Const.children x3))))
        else
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «Eval.valQuote» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 15)
      (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x0);
    x1

def «Eval.valUnit» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 11)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Eval.valPair» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 12)
      (x0 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1));
    x2

def «Eval.valClo» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 26)
      ((_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0) ::
        (x1 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2)));
    x3

def «Eval.valApp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 10)
      (x0 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x1));
    x2

def «Eval.ofList» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 20)
          (x2 :: (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x3)))
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 19)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x0))
      x1;
    x2

def «Eval.unquote» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 15))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x1

def «Eval.listOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 19))
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.arity x1)
            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 0)
              ([] : _root_.List _root_.Geb.Kernel.Tree))
        else
          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x1)
              (_root_.Geb.Kernel.leaf 20))
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.arity x1)
              (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
              (_root_.GebMirror.DatatypeSoundness.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1))
              (fun (x3 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    ((_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)) ::
                      (_root_.Geb.Kernel.Const.children x3))))
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      x0;
    x1

def «Eval.spine» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)) =>
        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 10))
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.arity x1)
            (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
            x2
            (x1, ([] : _root_.List _root_.Geb.Kernel.Tree))
            (fun (x3 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
               (_ : _root_.List
                 (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)) =>
              ((x3).1,
                _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                  (x3).2
                  (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                    (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))))
        else
          (x1, ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «Eval.primArity» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 0))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
          (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 4))
          (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 13))))).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      if (_root_.Geb.Kernel.Const.lt
        x0
        (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 2
      else
        _root_.Geb.Kernel.leaf 0);
    x1

def «Eval.constArity» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity
                                          x0;
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x1
                                              (_root_.Geb.Kernel.leaf 17))
                                            (_root_.Geb.Kernel.Const.eq
                                              x1
                                              (_root_.Geb.Kernel.leaf 25)))
                                          (_root_.Geb.Kernel.Const.eq
                                            x2
                                            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                          _root_.Geb.Kernel.leaf 2
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 18))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 1)))
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 21))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 24)))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                            _root_.Geb.Kernel.leaf 3
                                          else
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 22))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Eval.primArity»
                                                (_root_.Geb.Kernel.Const.label
                                                  (_root_.Geb.Kernel.Const.child
                                                    x0
                                                    (_root_.Geb.Kernel.leaf 0)))
                                            else
                                              _root_.Geb.Kernel.leaf 0);
    x1

def «Eval.primApply» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
      (_root_.GebMirror.DatatypeSoundness.«Eval.allSomeT»
        (_root_.GebMirror.DatatypeSoundness.«Eval.mapT» _root_.GebMirror.DatatypeSoundness.«Eval.unquote» x1))
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.length» x3;
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
          x3
          (_root_.Geb.Kernel.leaf 0);
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
          x3
          (_root_.Geb.Kernel.leaf 1);
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
              (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.label x5))
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.arity x5))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.GebMirror.DatatypeSoundness.«Eval.ofList»
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.GebMirror.DatatypeSoundness.«Eval.mapT»
                      _root_.GebMirror.DatatypeSoundness.«Eval.valQuote»
                      (_root_.Geb.Kernel.Const.children x5)))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                    (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.log2 x5))
                else
                  _root_.GebMirror.DatatypeSoundness.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.child x5 x6))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.add x5 x6))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                    (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.sub x5 x6))
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                    _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                      (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.mul x5 x6))
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                        (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.div x5 x6))
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                          (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.mod x5 x6))
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                            (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.eq x5 x6))
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                              (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» (_root_.Geb.Kernel.Const.lt x5 x6))
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x0
                              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                              _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote»
                                  (_root_.Geb.Kernel.Const.equal x5 x6))
                            else
                              _root_.GebMirror.DatatypeSoundness.«Prelude.none»
          else
            _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x2

def «Eval.primNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
      (_root_.GebMirror.DatatypeSoundness.«Eval.unquote» x0)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
          (_root_.GebMirror.DatatypeSoundness.«Eval.listOf» x1)
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
              (_root_.GebMirror.DatatypeSoundness.«Eval.allSomeT»
                (_root_.GebMirror.DatatypeSoundness.«Eval.mapT»
                  _root_.GebMirror.DatatypeSoundness.«Eval.unquote»
                  (_root_.Geb.Kernel.Const.children x3)))
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                  (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote»
                    (_root_.Geb.Kernel.Const.node
                      x2
                      (_root_.Geb.Kernel.Const.children x4))))));
    x2

def «Eval.foldVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
          (_root_.GebMirror.DatatypeSoundness.«Eval.allSomeT» x5)
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
              (x0
                x2
                (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote»
                  (_root_.Geb.Kernel.Const.node
                    x4
                    ([] : _root_.List _root_.Geb.Kernel.Tree))))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                x0
                  x7
                  (_root_.GebMirror.DatatypeSoundness.«Eval.ofList»
                    x1
                    (_root_.Geb.Kernel.Const.children x6)))))
      x3;
    x4

def «Eval.paraVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
          (_root_.GebMirror.DatatypeSoundness.«Eval.allSomeT» x5)
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
              (x0 x2 (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote» x4))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                x0
                  x7
                  (_root_.GebMirror.DatatypeSoundness.«Eval.ofList»
                    x1
                    (_root_.Geb.Kernel.Const.children x6)))))
      x3;
    x4

def «Eval.iterVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO» x4 (x0 x1))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.some» x2)
      x3;
    x4

def «Eval.foldrVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree) (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
          x5
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
              (x0 x1 x4)
              (fun (x7 : _root_.Geb.Kernel.Tree) => x0 x7 x6)))
      (_root_.GebMirror.DatatypeSoundness.«Prelude.some» x2)
      x3;
    x4

def «Eval.lcaseVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x1)
        (_root_.Geb.Kernel.leaf 19))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x1)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some» x2
    else
      if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 20))
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.arity x1)
          (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
        _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
          (x0 x3 (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)))
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            x0 x4 (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))
      else
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x4

def «Eval.sat» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x1;
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity
                                          x1;
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.length»
                                          x2;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 2);
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 17))
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 1))
                                            (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                            (_root_.GebMirror.DatatypeSoundness.«Eval.unquote» x7)
                                            (_root_.GebMirror.DatatypeSoundness.«Eval.foldVal»
                                              x0
                                              (_root_.Geb.Kernel.Const.child
                                                x1
                                                (_root_.Geb.Kernel.leaf 0))
                                              x6)
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 25))
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x4
                                                (_root_.Geb.Kernel.leaf 1))
                                              (_root_.Geb.Kernel.Const.eq
                                                x5
                                                (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                              (_root_.GebMirror.DatatypeSoundness.«Eval.unquote» x7)
                                              (_root_.GebMirror.DatatypeSoundness.«Eval.paraVal»
                                                x0
                                                (_root_.Geb.Kernel.Const.child
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 0))
                                                x6)
                                          else
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 18))
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                (_root_.GebMirror.DatatypeSoundness.«Eval.unquote» x8)
                                                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.DatatypeSoundness.«Eval.iterVal»
                                                    x0
                                                    x6
                                                    x7
                                                    (_root_.Geb.Kernel.Const.label x9))
                                            else
                                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 21))
                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 2))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                                _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                  (_root_.GebMirror.DatatypeSoundness.«Eval.listOf» x8)
                                                  (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.DatatypeSoundness.«Eval.foldrVal»
                                                      x0
                                                      x6
                                                      x7
                                                      (_root_.Geb.Kernel.Const.children x9))
                                              else
                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 24))
                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 2))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                                  _root_.GebMirror.DatatypeSoundness.«Eval.lcaseVal» x0 x6 x7 x8
                                                else
                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 22))
                                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x4
                                                        (_root_.Geb.Kernel.leaf 1))
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x5
                                                        (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      (_root_.Geb.Kernel.Const.label
                                                        (_root_.Geb.Kernel.Const.child
                                                          x1
                                                          (_root_.Geb.Kernel.leaf 0)))
                                                      (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.primNode» x6 x7
                                                    else
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.primApply»
                                                        (_root_.Geb.Kernel.Const.label
                                                          (_root_.Geb.Kernel.Const.child
                                                            x1
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                        x2
                                                  else
                                                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 22))
                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 1))
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.primApply»
                                                        (_root_.Geb.Kernel.Const.label
                                                          (_root_.Geb.Kernel.Const.child
                                                            x1
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                        x2
                                                    else
                                                      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x3

def «Eval.pairFst» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 12))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x1

def «Eval.pairSnd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 12))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1))
    else
      _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x1

def «Eval.evStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x2;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity
                                          x2;
                                        let x7 : _root_.List _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          x3
                                          (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                          (fun (x7 : _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List
                                               (_root_.List _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree)) =>
                                            x7);
                                        let x8 : _root_.List _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          x3
                                          (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                          (fun (_ : _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List
                                               (_root_.List _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree)) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.List _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree)
                                              x9
                                              (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                              (fun (x10 : _root_.List _root_.Geb.Kernel.Tree →
                                                   _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List
                                                   (_root_.List _root_.Geb.Kernel.Tree →
                                                     _root_.Geb.Kernel.Tree)) =>
                                                x10));
                                        let x9 : _root_.List _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree)
                                          x3
                                          (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                          (fun (_ : _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List
                                               (_root_.List _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree)) =>
                                            _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.List _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree)
                                              x10
                                              (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                              (fun (_ : _root_.List _root_.Geb.Kernel.Tree →
                                                   _root_.Geb.Kernel.Tree)
                                                 (x12 : _root_.List
                                                   (_root_.List _root_.Geb.Kernel.Tree →
                                                     _root_.Geb.Kernel.Tree)) =>
                                                _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.List _root_.Geb.Kernel.Tree →
                                                    _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree →
                                                    _root_.Geb.Kernel.Tree)
                                                  x12
                                                  (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
                                                  (fun (x13 : _root_.List _root_.Geb.Kernel.Tree →
                                                       _root_.Geb.Kernel.Tree)
                                                     (_ : _root_.List
                                                       (_root_.List _root_.Geb.Kernel.Tree →
                                                         _root_.Geb.Kernel.Tree)) =>
                                                    x13)));
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 8))
                                          (_root_.Geb.Kernel.Const.eq
                                            x6
                                            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                          _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
                                            x4
                                            (_root_.Geb.Kernel.Const.label
                                              (_root_.Geb.Kernel.Const.child
                                                x2
                                                (_root_.Geb.Kernel.leaf 0)))
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 9))
                                            (_root_.Geb.Kernel.Const.eq
                                              x6
                                              (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                              (_root_.GebMirror.DatatypeSoundness.«Eval.valClo»
                                                x4
                                                (_root_.Geb.Kernel.Const.child
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.Geb.Kernel.Const.child
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 1)))
                                          else
                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x5
                                                (_root_.Geb.Kernel.leaf 10))
                                              (_root_.Geb.Kernel.Const.eq
                                                x6
                                                (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                              _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                (x7 x4)
                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                    (x8 x4)
                                                    (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                      (x1).2 x10 x11))
                                            else
                                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 11))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x6
                                                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                                _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                  _root_.GebMirror.DatatypeSoundness.«Eval.valUnit»
                                              else
                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 12))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x6
                                                    (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                  _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                    (x7 x4)
                                                    (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                        (x8 x4)
                                                        (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                          _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                            (_root_.GebMirror.DatatypeSoundness.«Eval.valPair»
                                                              x10
                                                              x11)))
                                                else
                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 13))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                    _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                      (x7 x4)
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.pairFst»
                                                  else
                                                    if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x5
                                                        (_root_.Geb.Kernel.leaf 14))
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x6
                                                        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                      _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                        (x7 x4)
                                                        _root_.GebMirror.DatatypeSoundness.«Eval.pairSnd»
                                                    else
                                                      if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 15))
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x6
                                                          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                        _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                          (_root_.GebMirror.DatatypeSoundness.«Eval.valQuote»
                                                            (_root_.Geb.Kernel.Const.child
                                                              x2
                                                              (_root_.Geb.Kernel.leaf 0)))
                                                      else
                                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 16))
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x6
                                                            (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                                          _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                            (x7 x4)
                                                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                              _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                                (_root_.GebMirror.DatatypeSoundness.«Eval.unquote» x10)
                                                                (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                  if (_root_.Geb.Kernel.Const.eq
                                                                    (_root_.Geb.Kernel.Const.label
                                                                      x11)
                                                                    (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                                    x9 x4
                                                                  else
                                                                    x8 x4))
                                                        else
                                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 19))
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x6
                                                              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                              (_root_.Geb.Kernel.Const.node
                                                                (_root_.Geb.Kernel.leaf 19)
                                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                                                  (_root_.Geb.Kernel.Const.child
                                                                    x2
                                                                    (_root_.Geb.Kernel.leaf 0))))
                                                          else
                                                            if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                              (_root_.Geb.Kernel.Const.eq
                                                                x5
                                                                (_root_.Geb.Kernel.leaf 20))
                                                              (_root_.Geb.Kernel.Const.eq
                                                                x6
                                                                (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                              _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                                (x7 x4)
                                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                  _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                                    (x8 x4)
                                                                    (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                      _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                                        (_root_.Geb.Kernel.Const.node
                                                                          (_root_.Geb.Kernel.leaf 20)
                                                                          (x10 ::
                                                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                                                              x11)))))
                                                            else
                                                              if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 17))
                                                                    (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        x5
                                                                        (_root_.Geb.Kernel.leaf 25))
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        x5
                                                                        (_root_.Geb.Kernel.leaf 18))))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 1)))
                                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 21))
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 24)))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                                                _root_.GebMirror.DatatypeSoundness.«Prelude.some» x2
                                                              else
                                                                if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x5
                                                                    (_root_.Geb.Kernel.leaf 22))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                                  _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                                                    (_root_.Geb.Kernel.Const.node
                                                                      (_root_.Geb.Kernel.leaf 22)
                                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.single»
                                                                        (_root_.Geb.Kernel.Const.node
                                                                          (_root_.Geb.Kernel.Const.label
                                                                            (_root_.Geb.Kernel.Const.child
                                                                              x2
                                                                              (_root_.Geb.Kernel.leaf 0)))
                                                                          ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                                                else
                                                                  if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 23))
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x6
                                                                      (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                                    _root_.GebMirror.DatatypeSoundness.«Eval.bindO»
                                                                      (_root_.GebMirror.DatatypeSoundness.«Prelude.nth»
                                                                        x0
                                                                        (_root_.Geb.Kernel.Const.label
                                                                          (_root_.Geb.Kernel.Const.child
                                                                            x2
                                                                            (_root_.Geb.Kernel.leaf 0))))
                                                                      ((x1).1
                                                                        ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                                  else
                                                                    _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x5

def «Eval.apStep» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x1;
                                        if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                          (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 10))
                                          (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 17))
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                              (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 25))
                                              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 18))
                                                (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 21))
                                                  (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 24))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 22)))))))).label ≠ 0 then
                                          let x4 : _root_.Geb.Kernel.Tree ×
                                            _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Eval.spine»
                                            x1;
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Prelude.append»
                                            (x4).2
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.single» x2);
                                          if (_root_.Geb.Kernel.Const.lt
                                            (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x5)
                                            (_root_.GebMirror.DatatypeSoundness.«Eval.constArity»
                                              (x4).1)).label ≠ 0 then
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.some»
                                              (_root_.GebMirror.DatatypeSoundness.«Eval.valApp» x1 x2)
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«Eval.sat» (x0).2 (x4).1 x5
                                        else
                                          if (_root_.GebMirror.DatatypeSoundness.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 26))
                                            (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.arity x1)
                                              (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                            (x0).1
                                              (x2 ::
                                                (_root_.Geb.Kernel.Const.children
                                                  (_root_.Geb.Kernel.Const.child
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 0))))
                                              (_root_.Geb.Kernel.Const.child
                                                x1
                                                (_root_.Geb.Kernel.leaf 2))
                                          else
                                            _root_.GebMirror.DatatypeSoundness.«Prelude.none»);
    x3

def «Eval.next» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree) := (fun (x2 : _root_.List _root_.Geb.Kernel.Tree)
                                        (x3 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.para
        (α := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.DatatypeSoundness.«Eval.evStep» x0 x1)
        x3
        x2,
      _root_.GebMirror.DatatypeSoundness.«Eval.apStep» x1);
    x2

def «Eval.level» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.iter
      (α := (_root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.DatatypeSoundness.«Eval.next» x0)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.DatatypeSoundness.«Prelude.none»,
        fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.DatatypeSoundness.«Prelude.none»)
      x1;
    x2

def «Eval.eval» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.DatatypeSoundness.«Eval.level»
      x0
      x1).1
      x2
      x3;
    x4

def «Eval.apply» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.DatatypeSoundness.«Eval.level»
      x0
      x1).2
      x2
      x3;
    x4

def «wkL» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.typeIn»
      x1
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
        x2
        (_root_.GebMirror.DatatypeSoundness.«Prelude.append» x3 x4))
      (_root_.GebMirror.DatatypeSoundness.«Subst.wkAt»
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x2)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x3)
        x0)

def «wkR» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Check.typeIn»
      x1
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append» x2 x4)
      x0

def «nthL» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append»
        x0
        (_root_.GebMirror.DatatypeSoundness.«Prelude.append» x1 x2))
      (if (_root_.Geb.Kernel.Const.lt
        (_root_.Geb.Kernel.Const.label x3)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x0)).label ≠ 0 then
        _root_.Geb.Kernel.Const.label x3
      else
        _root_.Geb.Kernel.Const.add
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x1))

def «nthR» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append» x0 x2)
      (_root_.Geb.Kernel.Const.label x3)

def «nthS» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.nth»
      (_root_.GebMirror.DatatypeSoundness.«Prelude.append» x0 x1)
      (_root_.Geb.Kernel.Const.add
        (_root_.Geb.Kernel.Const.label x2)
        (_root_.GebMirror.DatatypeSoundness.«Prelude.length» x0))

def «nthT» :=
  fun (_ : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.DatatypeSoundness.«Prelude.nth» x1 (_root_.Geb.Kernel.Const.label x2)

def «charsFixed» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.equal
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 0)
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x2 : _root_.Geb.Kernel.Tree)
             (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
            ((x0 x2) :: x3))
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x1))
      (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x1)

def «srcForm» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
             _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
         (x4 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.List
          (_root_.Geb.Kernel.Tree ×
            _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
          (α := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
            _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
          (β := _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
          (fun (x5 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
               _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
             (x6 : _root_.List
               (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
            ((x5 x4) :: x6))
          ([] : _root_.List (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
          x3;
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x6 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
            ((x6).1 :: x7))
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x5;
        (_root_.Geb.Kernel.Const.node x2 x6,
          if (_root_.Geb.Kernel.Const.eq
            x2
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            _root_.GebMirror.DatatypeSoundness.«charsFixed» x4 x6
          else
            if (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
              (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 2))
              (_root_.GebMirror.DatatypeSoundness.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 13))
                (_root_.Geb.Kernel.Const.eq
                  x2
                  (_root_.Geb.Kernel.leaf 14)))).label ≠ 0 then
              _root_.Geb.Kernel.Const.foldr
                (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                (β := _root_.Geb.Kernel.Tree)
                (fun (x7 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
                   (x8 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.DatatypeSoundness.«Prelude.and» (x7).2 x8)
                (_root_.Geb.Kernel.leaf 1)
                x5
            else
              _root_.Geb.Kernel.leaf 0))
      x1
      x0).2

def «expName» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.DatatypeSoundness.«Reader.lookupAbbrev»
      x1
      x0;
    if (_root_.GebMirror.DatatypeSoundness.«Prelude.isSome» x2).label ≠ 0 then
      _root_.GebMirror.DatatypeSoundness.«Reader.nameOf» (_root_.GebMirror.DatatypeSoundness.«Prelude.get» x2)
    else
      x1

def «implName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.eq
      (_root_.GebMirror.DatatypeSoundness.«Prelude.at»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.leaf 0))
      (_root_.Geb.Kernel.leaf 37)

end GebMirror.DatatypeSoundness

end
