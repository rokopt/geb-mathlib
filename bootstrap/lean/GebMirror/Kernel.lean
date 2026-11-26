module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Kernel

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

def «Prelude.reverseIter» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree ×
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree ×
           _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree ×
            _root_.List _root_.Geb.Kernel.Tree)
          (x1).1
          x1
          (fun (x2 : _root_.Geb.Kernel.Tree)
             (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
            (x3, (x2 :: (x1).2))))
      (x0, ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Kernel.«Prelude.length» x0)).2

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
      (_root_.GebMirror.Kernel.«Prelude.single» x0)

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
      (_root_.GebMirror.Kernel.«Prelude.length» x0)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some» (_root_.GebMirror.Kernel.«Prelude.at» x0 x1)
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
      _root_.GebMirror.Kernel.«Prelude.tail»
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
    _root_.GebMirror.Kernel.«Prelude.reverse»
      (_root_.GebMirror.Kernel.«Prelude.digitsMsb» x0 x1 x2)

def «Reader.both» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Prelude.isSome» x0).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.isSome» x1
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
        (_root_.GebMirror.Kernel.«Reader.both» x1 (x2).1,
          ((_root_.GebMirror.Kernel.«Prelude.get» x1) :: (x2).2)))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    if ((x1).1).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) (x1).2)
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
    _root_.GebMirror.Kernel.«Reader.lexIn»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.leaf 0)

def «Reader.withLen» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node x0 (_root_.GebMirror.Kernel.«Prelude.single» x1)

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
    _root_.GebMirror.Kernel.«Reader.inRange»
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
    if (_root_.GebMirror.Kernel.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 65)
      (_root_.Geb.Kernel.leaf 90)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      if (_root_.GebMirror.Kernel.«Reader.inRange»
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
    if (_root_.GebMirror.Kernel.«Reader.isTokenStart» x0).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.GebMirror.Kernel.«Reader.isDigit» x0

def «Reader.isPlainIn» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.inRange»
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
      (_root_.GebMirror.Kernel.«Prelude.reverseIter» x0)

def «Reader.kwHole» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 104,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 101]

def «Reader.holeToks» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    ((_root_.Geb.Kernel.leaf 2) ::
      ((_root_.GebMirror.Kernel.«Reader.atomTok» x0) ::
        ((_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 3)
          (_root_.Geb.Kernel.Const.children _root_.GebMirror.Kernel.«Reader.kwHole»)) ::
          ((_root_.Geb.Kernel.leaf 1) :: x1))))

def «Reader.idleStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x1
      (_root_.Geb.Kernel.leaf 59)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Reader.lexIn»
        x0
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.Geb.Kernel.leaf 4)
    else
      if (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 40)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Reader.lexIdle» ((_root_.Geb.Kernel.leaf 1) :: x0)
      else
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 41)).label ≠ 0 then
          _root_.GebMirror.Kernel.«Reader.lexIdle» ((_root_.Geb.Kernel.leaf 2) :: x0)
        else
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
            _root_.GebMirror.Kernel.«Reader.lexIn»
              x0
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Kernel.«Reader.withLen»
                (_root_.Geb.Kernel.leaf 5)
                _root_.GebMirror.Kernel.«Prelude.none»)
          else
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 38)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Reader.lexIdle»
                ((_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 3)
                  (_root_.GebMirror.Kernel.«Prelude.single» (_root_.Geb.Kernel.leaf 38))) ::
                  x0)
            else
              if (_root_.Geb.Kernel.Const.eq
                x1
                (_root_.Geb.Kernel.leaf 63)).label ≠ 0 then
                _root_.GebMirror.Kernel.«Reader.lexIn»
                  x0
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.Geb.Kernel.leaf 3)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Reader.lexIn»
                    x0
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Kernel.«Reader.withLen»
                      (_root_.Geb.Kernel.leaf 13)
                      _root_.GebMirror.Kernel.«Prelude.none»)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x1
                    (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
                    _root_.GebMirror.Kernel.«Reader.lexIn»
                      x0
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.Kernel.«Reader.withLen»
                        (_root_.Geb.Kernel.leaf 14)
                        _root_.GebMirror.Kernel.«Prelude.none»)
                  else
                    if (_root_.GebMirror.Kernel.«Reader.isSpace» x1).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Reader.lexIdle» x0
                    else
                      if (_root_.GebMirror.Kernel.«Reader.isDigit» x1).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Reader.lexIn»
                          x0
                          (_root_.GebMirror.Kernel.«Prelude.single» x1)
                          (_root_.Geb.Kernel.leaf 2)
                      else
                        if (_root_.GebMirror.Kernel.«Reader.isTokenStart» x1).label ≠ 0 then
                          _root_.GebMirror.Kernel.«Reader.lexIn»
                            x0
                            (_root_.GebMirror.Kernel.«Prelude.single» x1)
                            (_root_.Geb.Kernel.leaf 1)
                        else
                          _root_.GebMirror.Kernel.«Reader.lexFail»

def «Reader.endAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
      _root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Kernel.«Prelude.get» x1)
        (_root_.GebMirror.Kernel.«Prelude.length» x2)
    else
      _root_.Geb.Kernel.leaf 1).label ≠ 0 then
      _root_.GebMirror.Kernel.«Reader.lexIdle»
        ((_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 3) x2) :: x0)
    else
      _root_.GebMirror.Kernel.«Reader.lexFail»

def «Reader.strStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x3
      (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Reader.endAtom»
        x0
        x2
        (_root_.GebMirror.Kernel.«Prelude.reverseIter» x1)
    else
      if (_root_.Geb.Kernel.Const.eq
        x3
        (_root_.Geb.Kernel.leaf 92)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Reader.lexIn»
          x0
          x1
          (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 6) x2)
      else
        if (_root_.GebMirror.Kernel.«Reader.isPlainIn» x3).label ≠ 0 then
          _root_.GebMirror.Kernel.«Reader.lexIn»
            x0
            (x3 :: x1)
            (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x2)
        else
          _root_.GebMirror.Kernel.«Reader.lexFail»

def «Reader.escChar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 97)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 7)
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 98)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 8)
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 116)).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 9)
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 118)).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 11)
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 110)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 10)
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 102)).label ≠ 0 then
                _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 12)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 114)).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 13)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
                    _root_.GebMirror.Kernel.«Prelude.some» x0
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Prelude.some» x0
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 63)).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Prelude.some» x0
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 92)).label ≠ 0 then
                          _root_.GebMirror.Kernel.«Prelude.some» x0
                        else
                          _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.hexVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.isDigit» x0).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 48))
    else
      if (_root_.GebMirror.Kernel.«Reader.inRange»
        x0
        (_root_.Geb.Kernel.leaf 65)
        (_root_.Geb.Kernel.leaf 70)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 55))
      else
        if (_root_.GebMirror.Kernel.«Reader.inRange»
          x0
          (_root_.Geb.Kernel.leaf 97)
          (_root_.Geb.Kernel.leaf 102)).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.some»
            (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 87))
        else
          _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.decodeHex» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.mod
        (_root_.GebMirror.Kernel.«Prelude.length» x0)
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
          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.hexVal» x1;
          if (if ((x2).1).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.isSome» x3
          else
            _root_.Geb.Kernel.leaf 0).label ≠ 0 then
            if (_root_.GebMirror.Kernel.«Prelude.isSome» ((x2).2).2).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (((_root_.Geb.Kernel.Const.add
                  (_root_.Geb.Kernel.Const.mul
                    (_root_.Geb.Kernel.leaf 16)
                    (_root_.GebMirror.Kernel.«Prelude.get» x3))
                  (_root_.GebMirror.Kernel.«Prelude.get» ((x2).2).2)) ::
                  ((x2).2).1),
                  _root_.GebMirror.Kernel.«Prelude.none»))
            else
              (_root_.Geb.Kernel.leaf 1,
                (((x2).2).1,
                  _root_.GebMirror.Kernel.«Prelude.some» (_root_.GebMirror.Kernel.«Prelude.get» x3)))
          else
            (_root_.Geb.Kernel.leaf 0, (x2).2))
        (_root_.Geb.Kernel.leaf 1,
          (([] : _root_.List _root_.Geb.Kernel.Tree),
            _root_.GebMirror.Kernel.«Prelude.none»))
        x0;
      if ((x1).1).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) ((x1).2).1)
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.base64Val» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.inRange»
      x0
      (_root_.Geb.Kernel.leaf 65)
      (_root_.Geb.Kernel.leaf 90)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 65))
    else
      if (_root_.GebMirror.Kernel.«Reader.inRange»
        x0
        (_root_.Geb.Kernel.leaf 97)
        (_root_.Geb.Kernel.leaf 122)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 71))
      else
        if (_root_.GebMirror.Kernel.«Reader.isDigit» x0).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.some»
            (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 4))
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 43)).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 62)
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 47)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 63)
            else
              _root_.GebMirror.Kernel.«Prelude.none»

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
          _root_.GebMirror.Kernel.«Reader.b64Fail»
      else
        if (_root_.Geb.Kernel.Const.eq
          x5
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.base64Val»
            x1;
          if (_root_.GebMirror.Kernel.«Prelude.isSome» x6).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.lt
              (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 6))
              (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  (_root_.Geb.Kernel.Const.add
                    (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 64) x3)
                    (_root_.GebMirror.Kernel.«Prelude.get» x6),
                    (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 6),
                      _root_.Geb.Kernel.leaf 0))))
            else
              let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 64) x3)
                (_root_.GebMirror.Kernel.«Prelude.get» x6);
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
            _root_.GebMirror.Kernel.«Reader.b64Fail»
        else
          _root_.GebMirror.Kernel.«Reader.b64Fail»
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
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))))
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)))) =>
        _root_.GebMirror.Kernel.«Reader.base64Step» x2 x1)
      (_root_.Geb.Kernel.leaf 1,
        (([] : _root_.List _root_.Geb.Kernel.Tree),
          (_root_.Geb.Kernel.leaf 0,
            (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0))))
      (_root_.GebMirror.Kernel.«Prelude.reverseIter» x0);
    if (if ((x1).1).label ≠ 0 then
      _root_.Geb.Kernel.Const.lt
        ((((x1).2).2).2).1
        (_root_.Geb.Kernel.leaf 6)
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Kernel.«Prelude.reverseIter» ((x1).2).1))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.lengthStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.reverseIter» x1;
    if (if (_root_.Geb.Kernel.Const.lt
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Kernel.«Prelude.length» x3)).label ≠ 0 then
      _root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Kernel.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.leaf 48)
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      _root_.GebMirror.Kernel.«Reader.lexFail»
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
          _root_.GebMirror.Kernel.«Reader.lexIdle»
            ((_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 3)
              ([] : _root_.List _root_.Geb.Kernel.Tree)) ::
              x0)
        else
          _root_.GebMirror.Kernel.«Reader.lexIn»
            x0
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 12)
              (_root_.GebMirror.Kernel.«Prelude.single» x4))
      else
        if (_root_.Geb.Kernel.Const.eq
          x2
          (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
          _root_.GebMirror.Kernel.«Reader.lexIn»
            x0
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Kernel.«Reader.withLen»
              (_root_.Geb.Kernel.leaf 5)
              (_root_.GebMirror.Kernel.«Prelude.some» x4))
        else
          if (_root_.Geb.Kernel.Const.eq
            x2
            (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
            _root_.GebMirror.Kernel.«Reader.lexIn»
              x0
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Kernel.«Reader.withLen»
                (_root_.Geb.Kernel.leaf 13)
                (_root_.GebMirror.Kernel.«Prelude.some» x4))
          else
            if (_root_.Geb.Kernel.Const.eq
              x2
              (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Reader.lexIn»
                x0
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Kernel.«Reader.withLen»
                  (_root_.Geb.Kernel.leaf 14)
                  (_root_.GebMirror.Kernel.«Prelude.some» x4))
            else
              _root_.GebMirror.Kernel.«Reader.lexFail»

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
      _root_.GebMirror.Kernel.«Reader.idleStep» x2 x1
    else
      if (_root_.Geb.Kernel.Const.eq
        x5
        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          _root_.GebMirror.Kernel.«Reader.lexIdle» x2
        else
          x0
      else
        if (_root_.Geb.Kernel.Const.eq
          x5
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          if (_root_.GebMirror.Kernel.«Reader.isTokenChar» x1).label ≠ 0 then
            _root_.GebMirror.Kernel.«Reader.lexIn» x2 (x1 :: x3) x4
          else
            _root_.GebMirror.Kernel.«Reader.idleStep»
              ((_root_.GebMirror.Kernel.«Reader.atomTok» x3) :: x2)
              x1
        else
          if (_root_.Geb.Kernel.Const.eq
            x5
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            if (_root_.GebMirror.Kernel.«Reader.isDigit» x1).label ≠ 0 then
              _root_.GebMirror.Kernel.«Reader.lexIn» x2 (x1 :: x3) x4
            else
              if (if (_root_.GebMirror.Kernel.«Reader.isTokenChar» x1).label ≠ 0 then
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
                _root_.GebMirror.Kernel.«Reader.lengthStep» x2 x3 x1
              else
                _root_.GebMirror.Kernel.«Reader.idleStep»
                  ((_root_.GebMirror.Kernel.«Reader.atomTok» x3) :: x2)
                  x1
          else
            if (_root_.Geb.Kernel.Const.eq
              x5
              (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
              if (if (_root_.GebMirror.Kernel.«Reader.isTokenChar» x1).label ≠ 0 then
                if (_root_.GebMirror.Kernel.«Reader.nonEmpty» x3).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  if (_root_.GebMirror.Kernel.«Reader.isDigit» x1).label ≠ 0 then
                    _root_.Geb.Kernel.leaf 0
                  else
                    _root_.Geb.Kernel.leaf 1
              else
                _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                _root_.GebMirror.Kernel.«Reader.lexIn» x2 (x1 :: x3) x4
              else
                if (_root_.GebMirror.Kernel.«Reader.nonEmpty» x3).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Reader.idleStep»
                    (_root_.GebMirror.Kernel.«Reader.holeToks» x3 x2)
                    x1
                else
                  _root_.GebMirror.Kernel.«Reader.lexFail»
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
                    _root_.GebMirror.Kernel.«Reader.lexIdle»
                      ((_root_.GebMirror.Kernel.«Reader.atomTok» (x1 :: x3)) :: x2)
                  else
                    _root_.GebMirror.Kernel.«Reader.lexIn»
                      x2
                      (x1 :: x3)
                      (_root_.Geb.Kernel.Const.node
                        (_root_.Geb.Kernel.leaf 12)
                        (_root_.GebMirror.Kernel.«Prelude.single»
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
                    _root_.GebMirror.Kernel.«Reader.strStep» x2 x3 x6 x1
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x5
                      (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.escChar» x1;
                      if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Reader.lexIn»
                          x2
                          ((_root_.GebMirror.Kernel.«Prelude.get» x7) :: x3)
                          (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x1
                          (_root_.Geb.Kernel.leaf 120)).label ≠ 0 then
                          _root_.GebMirror.Kernel.«Reader.lexIn»
                            x2
                            x3
                            (_root_.Geb.Kernel.Const.node
                              (_root_.Geb.Kernel.leaf 9)
                              (x6 ::
                                ((_root_.Geb.Kernel.leaf 0) ::
                                  (_root_.GebMirror.Kernel.«Prelude.single» (_root_.Geb.Kernel.leaf 0)))))
                        else
                          if (_root_.GebMirror.Kernel.«Reader.inRange»
                            x1
                            (_root_.Geb.Kernel.leaf 48)
                            (_root_.Geb.Kernel.leaf 55)).label ≠ 0 then
                            _root_.GebMirror.Kernel.«Reader.lexIn»
                              x2
                              x3
                              (_root_.Geb.Kernel.Const.node
                                (_root_.Geb.Kernel.leaf 10)
                                (x6 ::
                                  ((_root_.Geb.Kernel.leaf 1) ::
                                    (_root_.GebMirror.Kernel.«Prelude.single»
                                      (_root_.Geb.Kernel.Const.sub
                                        x1
                                        (_root_.Geb.Kernel.leaf 48))))))
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x1
                              (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                              _root_.GebMirror.Kernel.«Reader.lexIn»
                                x2
                                x3
                                (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 7) x6)
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x1
                                (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                _root_.GebMirror.Kernel.«Reader.lexIn»
                                  x2
                                  x3
                                  (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 8) x6)
                              else
                                _root_.GebMirror.Kernel.«Reader.lexFail»
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x5
                        (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                        if (_root_.Geb.Kernel.Const.eq
                          x1
                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                          _root_.GebMirror.Kernel.«Reader.lexIn»
                            x2
                            x3
                            (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                        else
                          _root_.GebMirror.Kernel.«Reader.strStep» x2 x3 x6 x1
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x5
                          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.eq
                            x1
                            (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                            _root_.GebMirror.Kernel.«Reader.lexIn»
                              x2
                              x3
                              (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                          else
                            _root_.GebMirror.Kernel.«Reader.strStep» x2 x3 x6 x1
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x5
                            (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.hexVal» x1;
                            if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                              if (_root_.Geb.Kernel.Const.eq
                                (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 1))
                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                _root_.GebMirror.Kernel.«Reader.lexIn»
                                  x2
                                  ((_root_.Geb.Kernel.Const.add
                                    (_root_.Geb.Kernel.Const.mul
                                      (_root_.Geb.Kernel.leaf 16)
                                      (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 2)))
                                    (_root_.GebMirror.Kernel.«Prelude.get» x7)) ::
                                    x3)
                                  (_root_.GebMirror.Kernel.«Reader.withLen» (_root_.Geb.Kernel.leaf 5) x6)
                              else
                                _root_.GebMirror.Kernel.«Reader.lexIn»
                                  x2
                                  x3
                                  (_root_.Geb.Kernel.Const.node
                                    (_root_.Geb.Kernel.leaf 9)
                                    (x6 ::
                                      ((_root_.Geb.Kernel.leaf 1) ::
                                        (_root_.GebMirror.Kernel.«Prelude.single»
                                          (_root_.GebMirror.Kernel.«Prelude.get» x7)))))
                            else
                              _root_.GebMirror.Kernel.«Reader.lexFail»
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x5
                              (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                              if (_root_.GebMirror.Kernel.«Reader.inRange»
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
                                    _root_.GebMirror.Kernel.«Reader.lexIn»
                                      x2
                                      (x7 :: x3)
                                      (_root_.GebMirror.Kernel.«Reader.withLen»
                                        (_root_.Geb.Kernel.leaf 5)
                                        x6)
                                  else
                                    _root_.GebMirror.Kernel.«Reader.lexFail»
                                else
                                  _root_.GebMirror.Kernel.«Reader.lexIn»
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
                                          (_root_.GebMirror.Kernel.«Prelude.single» x7))))
                              else
                                _root_.GebMirror.Kernel.«Reader.lexFail»
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x5
                                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                if (_root_.GebMirror.Kernel.«Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (_root_.GebMirror.Kernel.«Prelude.isSome»
                                    (_root_.GebMirror.Kernel.«Reader.hexVal» x1)).label ≠ 0 then
                                    _root_.GebMirror.Kernel.«Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 35)).label ≠ 0 then
                                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.decodeHex»
                                        (_root_.GebMirror.Kernel.«Prelude.reverseIter» x3);
                                      if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                                        _root_.GebMirror.Kernel.«Reader.endAtom»
                                          x2
                                          x6
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.Kernel.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.Kernel.«Reader.lexFail»
                                    else
                                      _root_.GebMirror.Kernel.«Reader.lexFail»
                              else
                                if (_root_.GebMirror.Kernel.«Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (if (_root_.GebMirror.Kernel.«Prelude.isSome»
                                    (_root_.GebMirror.Kernel.«Reader.base64Val» x1)).label ≠ 0 then
                                    _root_.Geb.Kernel.leaf 1
                                  else
                                    _root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 61)).label ≠ 0 then
                                    _root_.GebMirror.Kernel.«Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x1
                                      (_root_.Geb.Kernel.leaf 124)).label ≠ 0 then
                                      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.decodeBase64»
                                        (_root_.GebMirror.Kernel.«Prelude.reverseIter» x3);
                                      if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                                        _root_.GebMirror.Kernel.«Reader.endAtom»
                                          x2
                                          x6
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.Kernel.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.Kernel.«Reader.lexFail»
                                    else
                                      _root_.GebMirror.Kernel.«Reader.lexFail»

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
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Kernel.«Prelude.reverseIter» x1))
    else
      if (if (_root_.Geb.Kernel.Const.eq
        x3
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 1
      else
        _root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            (_root_.GebMirror.Kernel.«Prelude.reverseIter»
              ((_root_.GebMirror.Kernel.«Reader.atomTok» x2) :: x1)))
      else
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
          if (_root_.GebMirror.Kernel.«Reader.nonEmpty» x2).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some»
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Kernel.«Prelude.reverseIter»
                  (_root_.GebMirror.Kernel.«Reader.holeToks» x2 x1)))
          else
            _root_.GebMirror.Kernel.«Prelude.none»
        else
          _root_.GebMirror.Kernel.«Prelude.none»

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
      _root_.GebMirror.Kernel.«Reader.lexEnd»
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree ×
            (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
          (fun (x1 : _root_.Geb.Kernel.Tree)
             (x2 : _root_.List _root_.Geb.Kernel.Tree ×
               (_root_.List _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
            _root_.GebMirror.Kernel.«Reader.lexStep» x2 x1)
          (_root_.GebMirror.Kernel.«Reader.lexIdle»
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          (_root_.GebMirror.Kernel.«Prelude.reverseIter» x0))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
        _root_.GebMirror.Kernel.«Reader.fail»
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
                _root_.GebMirror.Kernel.«Reader.fail»
                (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
                   (x5 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                  (_root_.Geb.Kernel.leaf 1,
                    (((_root_.Geb.Kernel.Const.node
                      (_root_.Geb.Kernel.leaf 2)
                      (_root_.GebMirror.Kernel.«Prelude.reverseIter» x2)) ::
                      x4) ::
                      x5))))
    else
      x0

def «Reader.readSExps» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.tokenize»
      x0;
    if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree ×
        _root_.List
          (_root_.List
            _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree ×
          _root_.List (_root_.List _root_.Geb.Kernel.Tree))
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.Geb.Kernel.Tree ×
             _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
          _root_.GebMirror.Kernel.«Reader.parseStep» x3 x2)
        (_root_.Geb.Kernel.leaf 1,
          (([] : _root_.List _root_.Geb.Kernel.Tree) ::
            ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))))
        (_root_.GebMirror.Kernel.«Prelude.reverseIter»
          (_root_.Geb.Kernel.Const.children (_root_.GebMirror.Kernel.«Prelude.get» x1)));
      if ((x2).1).label ≠ 0 then
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.List _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          (x2).2
          _root_.GebMirror.Kernel.«Prelude.none»
          (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
             (x4 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.List _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x4
              (_root_.GebMirror.Kernel.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  (_root_.GebMirror.Kernel.«Prelude.reverseIter» x3)))
              (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
                 (_ : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                _root_.GebMirror.Kernel.«Prelude.none»))
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
    if (_root_.GebMirror.Kernel.«Reader.isAtom» x0).label ≠ 0 then
      _root_.Geb.Kernel.Const.equal (_root_.GebMirror.Kernel.«Reader.nameOf» x0) x1
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
          _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
        else
          if (_root_.GebMirror.Kernel.«Prelude.isSome» x3).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some»
              (_root_.Geb.Kernel.Const.add
                (_root_.GebMirror.Kernel.«Prelude.get» x3)
                (_root_.Geb.Kernel.leaf 1))
          else
            _root_.GebMirror.Kernel.«Prelude.none»)
      _root_.GebMirror.Kernel.«Prelude.none»
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
          _root_.GebMirror.Kernel.«Prelude.some»
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1))
        else
          x3)
      _root_.GebMirror.Kernel.«Prelude.none»
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
    if (_root_.GebMirror.Kernel.«Reader.nonEmpty» x0).label ≠ 0 then
      if ((x1).1).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some» ((x1).2).1
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.expandNums» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node x2 x3;
        if (_root_.GebMirror.Kernel.«Reader.isAtom» x4).label ≠ 0 then
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.lookupAbbrev»
            (_root_.GebMirror.Kernel.«Reader.nameOf» x4)
            x0;
          if (_root_.GebMirror.Kernel.«Prelude.isSome» x5).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.get» x5
          else
            x4
        else
          x4)
      x1

def «Reader.numOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.expandNums»
      x0
      x1;
    if (_root_.GebMirror.Kernel.«Reader.isAtom» x2).label ≠ 0 then
      if (_root_.GebMirror.Kernel.«Prelude.isSome»
        (_root_.GebMirror.Kernel.«Reader.numeral»
          (_root_.Geb.Kernel.Const.children x2))).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some» x2
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
      (x1 :: (_root_.GebMirror.Kernel.«Prelude.single» x2))

def «Reader.some2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.both» x1 x2).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.GebMirror.Kernel.«Reader.node2»
          x0
          (_root_.GebMirror.Kernel.«Prelude.get» x1)
          (_root_.GebMirror.Kernel.«Prelude.get» x2))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

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
          (_root_.GebMirror.Kernel.«Reader.rtTrees» x3);
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rtValues» x3;
        (x4,
          if (_root_.GebMirror.Kernel.«Reader.isAtom» x4).label ≠ 0 then
            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.nameOf» x4;
            if (_root_.Geb.Kernel.Const.equal
              x6
              _root_.GebMirror.Kernel.«Reader.kwT»).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
            else
              if (_root_.Geb.Kernel.Const.equal
                x6
                _root_.GebMirror.Kernel.«Reader.kwUnit»).label ≠ 0 then
                _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 1)
              else
                _root_.GebMirror.Kernel.«Reader.lookupAbbrev» x6 x0
          else
            if (_root_.GebMirror.Kernel.«Reader.isList» x4).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
                (_root_.Geb.Kernel.Const.children x4)
                (_root_.Geb.Kernel.leaf 0);
              let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x4;
              if (_root_.GebMirror.Kernel.«Reader.named»
                x6
                _root_.GebMirror.Kernel.«Reader.kwProd»).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.eq
                  x7
                  (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Reader.some2»
                    (_root_.Geb.Kernel.leaf 2)
                    (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1))
                    (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 2))
                else
                  _root_.GebMirror.Kernel.«Prelude.none»
              else
                if (_root_.GebMirror.Kernel.«Reader.named»
                  x6
                  _root_.GebMirror.Kernel.«Reader.kwArrow»).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.eq
                    x7
                    (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                    _root_.GebMirror.Kernel.«Reader.some2»
                      (_root_.Geb.Kernel.leaf 3)
                      (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1))
                      (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 2))
                  else
                    _root_.GebMirror.Kernel.«Prelude.none»
                else
                  if (_root_.GebMirror.Kernel.«Reader.named»
                    x6
                    _root_.GebMirror.Kernel.«Reader.kwList»).label ≠ 0 then
                    if (_root_.Geb.Kernel.Const.eq
                      x7
                      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                      if (_root_.GebMirror.Kernel.«Prelude.isSome»
                        (_root_.GebMirror.Kernel.«Prelude.at»
                          x5
                          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Prelude.some»
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 4)
                            (_root_.GebMirror.Kernel.«Prelude.single»
                              (_root_.GebMirror.Kernel.«Prelude.get»
                                (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))))
                      else
                        _root_.GebMirror.Kernel.«Prelude.none»
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»
                  else
                    _root_.GebMirror.Kernel.«Prelude.none»
            else
              _root_.GebMirror.Kernel.«Prelude.none»))
      x1).2

def «Reader.readDatum» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.isAtom» x0).label ≠ 0 then
      let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.numeral»
        (_root_.Geb.Kernel.Const.children x0);
      if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.GebMirror.Kernel.«Prelude.get» x1)
            ([] : _root_.List _root_.Geb.Kernel.Tree))
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      let x1 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.fold
        (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
        (fun (x1 : _root_.Geb.Kernel.Tree)
           (x2 : _root_.List
             (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
          let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
            x1
            (_root_.GebMirror.Kernel.«Reader.rtTrees» x2);
          (x3,
            if (_root_.GebMirror.Kernel.«Reader.isAtom» x3).label ≠ 0 then
              let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.numeral»
                (_root_.Geb.Kernel.Const.children x3);
              if (_root_.GebMirror.Kernel.«Prelude.isSome» x4).label ≠ 0 then
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.GebMirror.Kernel.«Prelude.single»
                      (_root_.Geb.Kernel.Const.node
                        (_root_.GebMirror.Kernel.«Prelude.get» x4)
                        ([] : _root_.List _root_.Geb.Kernel.Tree))))
              else
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.Geb.Kernel.Const.children x3))
            else
              if (_root_.GebMirror.Kernel.«Reader.isList» x3).label ≠ 0 then
                _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.Geb.Kernel.Tree)
                  (_root_.Geb.Kernel.Const.children x3)
                  _root_.GebMirror.Kernel.«Prelude.none»
                  (fun (x4 : _root_.Geb.Kernel.Tree)
                     (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Reader.isAtom»
                      x4).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Reader.numeral» (_root_.Geb.Kernel.Const.children x4)
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»);
                    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.allSome»
                      (_root_.GebMirror.Kernel.«Prelude.tail» (_root_.GebMirror.Kernel.«Reader.rtValues» x2));
                    if (_root_.GebMirror.Kernel.«Reader.both» x6 x7).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Prelude.some»
                        (_root_.Geb.Kernel.Const.node
                          (_root_.Geb.Kernel.leaf 0)
                          (_root_.GebMirror.Kernel.«Prelude.single»
                            (_root_.Geb.Kernel.Const.node
                              (_root_.GebMirror.Kernel.«Prelude.get» x6)
                              (_root_.Geb.Kernel.Const.foldr
                                (α := _root_.Geb.Kernel.Tree)
                                (β := _root_.List _root_.Geb.Kernel.Tree)
                                (fun (x8 : _root_.Geb.Kernel.Tree)
                                   (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Kernel.«Prelude.append»
                                    (_root_.Geb.Kernel.Const.children x8)
                                    x9)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.Geb.Kernel.Const.children
                                  (_root_.GebMirror.Kernel.«Prelude.get» x7))))))
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»)
              else
                _root_.GebMirror.Kernel.«Prelude.none»))
        x0).2;
      if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.child
            (_root_.GebMirror.Kernel.«Prelude.get» x1)
            (_root_.Geb.Kernel.leaf 0))
      else
        _root_.GebMirror.Kernel.«Prelude.none»

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

def «$284c697374732e7461696c202850726f64205420284172726f7720284c6973742054292054292929» :=
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
        _root_.GebMirror.Kernel.«$284c697374732e7461696c202850726f64205420284172726f7720284c6973742054292054292929»
        x0
        x1)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Kernel.«Prelude.none»)
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (_ : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        (x3).2)
      x2

def «Reader.app» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Reader.node2» (_root_.Geb.Kernel.leaf 10) x0 x1

def «Reader.apps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Kernel.«Reader.app» x3 x2)
      x0
      (_root_.GebMirror.Kernel.«Prelude.reverse» x1)

def «Reader.some1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          x0
          (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x1)))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.argsOf» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Reader.allSome»
      (_root_.GebMirror.Kernel.«Reader.rrApply»
        (_root_.Geb.Kernel.Const.iter
          (α := _root_.List
            (_root_.Geb.Kernel.Tree ×
              (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
          _root_.GebMirror.Kernel.«$284c697374732e7461696c202850726f64205420284172726f7720284c6973742054292054292929»
          x0
          x1)
        x2)

def «Reader.mkArgs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          x0
          (_root_.Geb.Kernel.Const.children (_root_.GebMirror.Kernel.«Prelude.get» x1)))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.appsOpt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.both» x0 x1).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.GebMirror.Kernel.«Reader.apps»
          (_root_.GebMirror.Kernel.«Prelude.get» x0)
          (_root_.Geb.Kernel.Const.children (_root_.GebMirror.Kernel.«Prelude.get» x1)))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Reader.binders» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Reader.isList» x0).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
        if (_root_.GebMirror.Kernel.«Reader.isAtom»
          (_root_.Geb.Kernel.Const.child
            x0
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.single» x0
        else
          _root_.Geb.Kernel.Const.children x0
      else
        _root_.Geb.Kernel.Const.children x0
    else
      ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Reader.readBinders» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((if (_root_.GebMirror.Kernel.«Reader.isList» x2).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.arity x2)
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              if (_root_.GebMirror.Kernel.«Reader.isAtom»
                (_root_.Geb.Kernel.Const.child
                  x2
                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
                  x0
                  (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1));
                if (_root_.GebMirror.Kernel.«Prelude.isSome» x4).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Prelude.some»
                    (_root_.GebMirror.Kernel.«Reader.node2»
                      (_root_.Geb.Kernel.leaf 0)
                      (_root_.GebMirror.Kernel.«Reader.nameOf»
                        (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0)))
                      (_root_.GebMirror.Kernel.«Prelude.get» x4))
                else
                  _root_.GebMirror.Kernel.«Prelude.none»
              else
                _root_.GebMirror.Kernel.«Prelude.none»
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none») ::
            x3))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x1)

def «Reader.resolveAtom» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.numeral»
      (_root_.Geb.Kernel.Const.children x1);
    if (_root_.GebMirror.Kernel.«Prelude.isSome» x3).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x3)))
    else
      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.nameOf» x1;
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.indexOf»
        x4
        x2;
      if (_root_.GebMirror.Kernel.«Prelude.isSome» x5).label ≠ 0 then
        _root_.GebMirror.Kernel.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 8)
            (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x5)))
      else
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.indexOf»
          x4
          x0;
        if (_root_.GebMirror.Kernel.«Prelude.isSome» x6).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.some»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 23)
              (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x6)))
        else
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.indexOf»
            x4
            _root_.GebMirror.Kernel.«Reader.primNames»;
          if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some»
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 22)
                (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x7)))
          else
            if (_root_.Geb.Kernel.Const.equal
              x4
              _root_.GebMirror.Kernel.«Reader.kwUnitValue»).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 11)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
            else
              _root_.GebMirror.Kernel.«Prelude.none»

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
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
      x4
      (_root_.Geb.Kernel.leaf 0);
    if (_root_.Geb.Kernel.Const.eq
      x5
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.none»
    else
      if (if (_root_.GebMirror.Kernel.«Reader.named»
        x6
        _root_.GebMirror.Kernel.«Reader.kwLam»).label ≠ 0 then
        _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 3)
      else
        _root_.Geb.Kernel.leaf 0).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readBinders»
          x0
          (_root_.GebMirror.Kernel.«Reader.binders»
            (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)));
        if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
          let x8 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
            (_root_.GebMirror.Kernel.«Prelude.get» x7);
          if (_root_.GebMirror.Kernel.«Reader.nonEmpty» x8).label ≠ 0 then
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 2)
              (_root_.GebMirror.Kernel.«Prelude.append»
                (_root_.GebMirror.Kernel.«Prelude.reverse»
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
            if (_root_.GebMirror.Kernel.«Prelude.isSome» x9).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.Geb.Kernel.Const.foldr
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.Geb.Kernel.Tree)
                  (fun (x10 : _root_.Geb.Kernel.Tree) (x11 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Kernel.«Reader.node2»
                      (_root_.Geb.Kernel.leaf 9)
                      (_root_.Geb.Kernel.Const.child x10 (_root_.Geb.Kernel.leaf 1))
                      x11)
                  (_root_.GebMirror.Kernel.«Prelude.get» x9)
                  x8)
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none»
        else
          _root_.GebMirror.Kernel.«Prelude.none»
      else
        if (if (_root_.GebMirror.Kernel.«Reader.named»
          x6
          _root_.GebMirror.Kernel.«Reader.kwLet»).label ≠ 0 then
          _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 5)
        else
          _root_.Geb.Kernel.leaf 0).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
            x4
            (_root_.Geb.Kernel.leaf 1);
          if (_root_.GebMirror.Kernel.«Reader.isAtom» x7).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
              x0
              (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2));
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 4)
              ((_root_.GebMirror.Kernel.«Reader.nameOf» x7) :: x3);
            let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 3)
              x3;
            if (_root_.GebMirror.Kernel.«Reader.both»
              x8
              (_root_.GebMirror.Kernel.«Reader.both» x9 x10)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.GebMirror.Kernel.«Reader.app»
                  (_root_.GebMirror.Kernel.«Reader.node2»
                    (_root_.Geb.Kernel.leaf 9)
                    (_root_.GebMirror.Kernel.«Prelude.get» x8)
                    (_root_.GebMirror.Kernel.«Prelude.get» x9))
                  (_root_.GebMirror.Kernel.«Prelude.get» x10))
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none»
        else
          if (_root_.GebMirror.Kernel.«Reader.named»
            x6
            _root_.GebMirror.Kernel.«Reader.kwPair»).label ≠ 0 then
            _root_.GebMirror.Kernel.«Reader.mkArgs»
              (_root_.Geb.Kernel.leaf 12)
              (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
          else
            if (_root_.GebMirror.Kernel.«Reader.named»
              x6
              _root_.GebMirror.Kernel.«Reader.kwFst»).label ≠ 0 then
              _root_.GebMirror.Kernel.«Reader.mkArgs»
                (_root_.Geb.Kernel.leaf 13)
                (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
            else
              if (_root_.GebMirror.Kernel.«Reader.named»
                x6
                _root_.GebMirror.Kernel.«Reader.kwSnd»).label ≠ 0 then
                _root_.GebMirror.Kernel.«Reader.mkArgs»
                  (_root_.Geb.Kernel.leaf 14)
                  (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
              else
                if (_root_.GebMirror.Kernel.«Reader.named»
                  x6
                  _root_.GebMirror.Kernel.«Reader.kwIf»).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Reader.mkArgs»
                    (_root_.Geb.Kernel.leaf 16)
                    (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
                else
                  if (_root_.GebMirror.Kernel.«Reader.named»
                    x6
                    _root_.GebMirror.Kernel.«Reader.kwCons»).label ≠ 0 then
                    _root_.GebMirror.Kernel.«Reader.mkArgs»
                      (_root_.Geb.Kernel.leaf 20)
                      (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 1) x3)
                  else
                    if (if (_root_.GebMirror.Kernel.«Reader.named»
                      x6
                      _root_.GebMirror.Kernel.«Reader.kwQuote»).label ≠ 0 then
                      _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 2)
                    else
                      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Reader.some1»
                        (_root_.Geb.Kernel.leaf 15)
                        (_root_.GebMirror.Kernel.«Reader.readDatum»
                          (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                    else
                      if (if (_root_.GebMirror.Kernel.«Reader.named»
                        x6
                        _root_.GebMirror.Kernel.«Reader.kwNil»).label ≠ 0 then
                        _root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 2)
                      else
                        _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Reader.some1»
                          (_root_.Geb.Kernel.leaf 19)
                          (_root_.GebMirror.Kernel.«Reader.readType»
                            x0
                            (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                      else
                        if (if (_root_.GebMirror.Kernel.«Reader.named»
                          x6
                          _root_.GebMirror.Kernel.«Reader.kwFold»).label ≠ 0 then
                          _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                        else
                          _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
                            x0
                            (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                          if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                            _root_.GebMirror.Kernel.«Reader.appsOpt»
                              (_root_.GebMirror.Kernel.«Prelude.some»
                                (_root_.Geb.Kernel.Const.node
                                  (_root_.Geb.Kernel.leaf 17)
                                  (_root_.GebMirror.Kernel.«Prelude.single»
                                    (_root_.GebMirror.Kernel.«Prelude.get» x7))))
                              (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                          else
                            _root_.GebMirror.Kernel.«Prelude.none»
                        else
                          if (if (_root_.GebMirror.Kernel.«Reader.named»
                            x6
                            _root_.GebMirror.Kernel.«Reader.kwPara»).label ≠ 0 then
                            _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                          else
                            _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
                              x0
                              (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                            if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                              _root_.GebMirror.Kernel.«Reader.appsOpt»
                                (_root_.GebMirror.Kernel.«Prelude.some»
                                  (_root_.Geb.Kernel.Const.node
                                    (_root_.Geb.Kernel.leaf 25)
                                    (_root_.GebMirror.Kernel.«Prelude.single»
                                      (_root_.GebMirror.Kernel.«Prelude.get» x7))))
                                (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                            else
                              _root_.GebMirror.Kernel.«Prelude.none»
                          else
                            if (if (_root_.GebMirror.Kernel.«Reader.named»
                              x6
                              _root_.GebMirror.Kernel.«Reader.kwIter»).label ≠ 0 then
                              _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5
                            else
                              _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                              let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
                                x0
                                (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1));
                              if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                                _root_.GebMirror.Kernel.«Reader.appsOpt»
                                  (_root_.GebMirror.Kernel.«Prelude.some»
                                    (_root_.Geb.Kernel.Const.node
                                      (_root_.Geb.Kernel.leaf 18)
                                      (_root_.GebMirror.Kernel.«Prelude.single»
                                        (_root_.GebMirror.Kernel.«Prelude.get» x7))))
                                  (_root_.GebMirror.Kernel.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x3)
                              else
                                _root_.GebMirror.Kernel.«Prelude.none»
                            else
                              if (if (_root_.GebMirror.Kernel.«Reader.named»
                                x6
                                _root_.GebMirror.Kernel.«Reader.kwFoldr»).label ≠ 0 then
                                _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 2) x5
                              else
                                _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                                let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.some2»
                                  (_root_.Geb.Kernel.leaf 21)
                                  (_root_.GebMirror.Kernel.«Reader.readType»
                                    x0
                                    (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                                  (_root_.GebMirror.Kernel.«Reader.readType»
                                    x0
                                    (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2)));
                                if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                                  _root_.GebMirror.Kernel.«Reader.appsOpt»
                                    x7
                                    (_root_.GebMirror.Kernel.«Reader.argsOf»
                                      x2
                                      (_root_.Geb.Kernel.leaf 3)
                                      x3)
                                else
                                  _root_.GebMirror.Kernel.«Prelude.none»
                              else
                                if (if (_root_.GebMirror.Kernel.«Reader.named»
                                  x6
                                  _root_.GebMirror.Kernel.«Reader.kwLcase»).label ≠ 0 then
                                  _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 2) x5
                                else
                                  _root_.Geb.Kernel.leaf 0).label ≠ 0 then
                                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.some2»
                                    (_root_.Geb.Kernel.leaf 24)
                                    (_root_.GebMirror.Kernel.«Reader.readType»
                                      x0
                                      (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                                    (_root_.GebMirror.Kernel.«Reader.readType»
                                      x0
                                      (_root_.GebMirror.Kernel.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2)));
                                  if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                                    _root_.GebMirror.Kernel.«Reader.appsOpt»
                                      x7
                                      (_root_.GebMirror.Kernel.«Reader.argsOf»
                                        x2
                                        (_root_.Geb.Kernel.leaf 3)
                                        x3)
                                  else
                                    _root_.GebMirror.Kernel.«Prelude.none»
                                else
                                  _root_.GebMirror.Kernel.«Reader.appsOpt»
                                    (_root_.GebMirror.Kernel.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 0) x3)
                                    (_root_.GebMirror.Kernel.«Reader.argsOf»
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
          (_root_.GebMirror.Kernel.«Reader.rrTrees» x5);
        (x6,
          fun (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.Kernel.«Reader.isAtom» x6).label ≠ 0 then
              _root_.GebMirror.Kernel.«Reader.resolveAtom» x1 x6 x7
            else
              if (_root_.GebMirror.Kernel.«Reader.isList» x6).label ≠ 0 then
                _root_.GebMirror.Kernel.«Reader.resolveList» x0 x6 x5 x7
              else
                _root_.GebMirror.Kernel.«Prelude.none»))
      x2).2
      x3

def «Reader.reservedNames» :=
  _root_.GebMirror.Kernel.«Prelude.append»
    (_root_.GebMirror.Kernel.«Reader.kwLam» ::
      (_root_.GebMirror.Kernel.«Reader.kwLet» ::
        (_root_.GebMirror.Kernel.«Reader.kwPair» ::
          (_root_.GebMirror.Kernel.«Reader.kwFst» ::
            (_root_.GebMirror.Kernel.«Reader.kwSnd» ::
              (_root_.GebMirror.Kernel.«Reader.kwIf» ::
                (_root_.GebMirror.Kernel.«Reader.kwQuote» ::
                  (_root_.GebMirror.Kernel.«Reader.kwCons» ::
                    (_root_.GebMirror.Kernel.«Reader.kwNil» ::
                      (_root_.GebMirror.Kernel.«Reader.kwFold» ::
                        (_root_.GebMirror.Kernel.«Reader.kwPara» ::
                          (_root_.GebMirror.Kernel.«Reader.kwIter» ::
                            (_root_.GebMirror.Kernel.«Reader.kwFoldr» ::
                              (_root_.GebMirror.Kernel.«Reader.kwLcase» ::
                                (_root_.GebMirror.Kernel.«Reader.kwUnitValue» ::
                                  (_root_.GebMirror.Kernel.«Reader.kwDef» ::
                                    (_root_.GebMirror.Kernel.«Reader.kwDeftype» ::
                                      (_root_.GebMirror.Kernel.«Reader.kwDefnum» ::
                                        (_root_.GebMirror.Kernel.«Reader.kwHole» ::
                                          ((_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 42,
                                            _root_.Geb.Kernel.leaf 97,
                                            _root_.Geb.Kernel.leaf 110,
                                            _root_.Geb.Kernel.leaf 110]) ::
                                            ((_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 42,
                                              _root_.Geb.Kernel.leaf 100,
                                              _root_.Geb.Kernel.leaf 111,
                                              _root_.Geb.Kernel.leaf 99]) ::
                                              (_root_.GebMirror.Kernel.«Reader.kwT» ::
                                                (_root_.GebMirror.Kernel.«Reader.kwUnit» ::
                                                  (_root_.GebMirror.Kernel.«Reader.kwProd» ::
                                                    (_root_.GebMirror.Kernel.«Reader.kwArrow» ::
                                                      (_root_.GebMirror.Kernel.«Prelude.single»
                                                        _root_.GebMirror.Kernel.«Reader.kwList»))))))))))))))))))))))))))
    _root_.GebMirror.Kernel.«Reader.primNames»

def «Reader.isFresh» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Kernel.«Prelude.isSome»
      (_root_.GebMirror.Kernel.«Reader.indexOf»
        x3
        _root_.GebMirror.Kernel.«Reader.reservedNames»)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      if (_root_.GebMirror.Kernel.«Prelude.isSome»
        (_root_.GebMirror.Kernel.«Reader.indexOf» x3 x2)).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        if (_root_.GebMirror.Kernel.«Prelude.isSome»
          (_root_.GebMirror.Kernel.«Reader.lookupAbbrev» x3 x0)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 0
        else
          if (_root_.GebMirror.Kernel.«Prelude.isSome»
            (_root_.GebMirror.Kernel.«Reader.lookupAbbrev» x3 x1)).label ≠ 0 then
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
      if (_root_.GebMirror.Kernel.«Reader.isList» x1).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.arity x1)
          (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
          if (_root_.GebMirror.Kernel.«Reader.isAtom»
            (_root_.Geb.Kernel.Const.child
              x1
              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
            _root_.GebMirror.Kernel.«Reader.isFresh»
              x2
              x3
              x4
              (_root_.GebMirror.Kernel.«Reader.nameOf»
                (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))
          else
            _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 0
      else
        _root_.Geb.Kernel.leaf 0
    else
      _root_.Geb.Kernel.leaf 0).label ≠ 0 then
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.nameOf»
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1));
      if (_root_.GebMirror.Kernel.«Reader.named»
        (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
        _root_.GebMirror.Kernel.«Reader.kwDef»).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.resolve»
          x2
          x4
          (_root_.GebMirror.Kernel.«Reader.expandNums»
            x3
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2)))
          ([] : _root_.List _root_.Geb.Kernel.Tree);
        if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
          (_root_.Geb.Kernel.leaf 1,
            (x2,
              (x3,
                (_root_.GebMirror.Kernel.«Prelude.append»
                  x4
                  (_root_.GebMirror.Kernel.«Prelude.single» x6),
                  _root_.GebMirror.Kernel.«Prelude.append»
                    x5
                    (_root_.GebMirror.Kernel.«Prelude.single»
                      (_root_.GebMirror.Kernel.«Prelude.get» x7))))))
        else
          (_root_.Geb.Kernel.leaf 0, (x0).2)
      else
        if (_root_.GebMirror.Kernel.«Reader.named»
          (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.Kernel.«Reader.kwDeftype»).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.readType»
            x2
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2));
          if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
            (_root_.Geb.Kernel.leaf 1,
              (((_root_.GebMirror.Kernel.«Reader.node2»
                (_root_.Geb.Kernel.leaf 0)
                x6
                (_root_.GebMirror.Kernel.«Prelude.get» x7)) ::
                x2),
                ((x0).2).2))
          else
            (_root_.Geb.Kernel.leaf 0, (x0).2)
        else
          if (_root_.GebMirror.Kernel.«Reader.named»
            (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Kernel.«Reader.kwDefnum»).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.numOf»
              x3
              (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 2));
            if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  (((_root_.GebMirror.Kernel.«Reader.node2»
                    (_root_.Geb.Kernel.leaf 0)
                    x6
                    (_root_.GebMirror.Kernel.«Prelude.get» x7)) ::
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
        x2 (_root_.GebMirror.Kernel.«Reader.progStep» x3 x1))
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
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.GebMirror.Kernel.«Reader.node2»
          (_root_.Geb.Kernel.leaf 100)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 101)
            ((((x1).2).2).2).2)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 102)
            ((((x1).2).2).2).1))
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Check.tyArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Reader.node2» (_root_.Geb.Kernel.leaf 3) x0 x1

def «Check.tyList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (_root_.GebMirror.Kernel.«Prelude.single» x0)

def «Check.isTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.length» x2;
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
            _root_.GebMirror.Kernel.«Prelude.and»
              (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 4))
              (_root_.GebMirror.Kernel.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
          else
            if (_root_.Geb.Kernel.Const.eq
              x3
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.and»
                (if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 1
                else
                  _root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 3))
                (_root_.GebMirror.Kernel.«Prelude.and»
                  (_root_.GebMirror.Kernel.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
                  (_root_.GebMirror.Kernel.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)))
            else
              _root_.Geb.Kernel.leaf 0)
      x0

def «Check.isProd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))

def «Check.isArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 3))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))

def «Check.isListTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 4))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 1))

def «Check.foldTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Check.tyArrow»
      (_root_.GebMirror.Kernel.«Check.tyArrow»
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.Kernel.«Check.tyArrow»
          (_root_.GebMirror.Kernel.«Check.tyList» x0)
          x0))
      (_root_.GebMirror.Kernel.«Check.tyArrow» (_root_.Geb.Kernel.leaf 0) x0)

def «Check.iterTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Check.tyArrow»
      (_root_.GebMirror.Kernel.«Check.tyArrow» x0 x0)
      (_root_.GebMirror.Kernel.«Check.tyArrow»
        x0
        (_root_.GebMirror.Kernel.«Check.tyArrow» (_root_.Geb.Kernel.leaf 0) x0))

def «Check.foldrTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Check.tyArrow»
      (_root_.GebMirror.Kernel.«Check.tyArrow»
        x0
        (_root_.GebMirror.Kernel.«Check.tyArrow» x1 x1))
      (_root_.GebMirror.Kernel.«Check.tyArrow»
        x1
        (_root_.GebMirror.Kernel.«Check.tyArrow»
          (_root_.GebMirror.Kernel.«Check.tyList» x0)
          x1))

def «Check.lcaseTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Check.tyArrow»
      (_root_.GebMirror.Kernel.«Check.tyList» x0)
      (_root_.GebMirror.Kernel.«Check.tyArrow»
        x1
        (_root_.GebMirror.Kernel.«Check.tyArrow»
          (_root_.GebMirror.Kernel.«Check.tyArrow»
            x0
            (_root_.GebMirror.Kernel.«Check.tyArrow»
              (_root_.GebMirror.Kernel.«Check.tyList» x0)
              x1))
          x1))

def «Check.primTypes» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Check.tyArrow»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0);
  let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Check.tyArrow»
    (_root_.Geb.Kernel.leaf 0)
    x0;
  _root_.GebMirror.Kernel.«Prelude.append»
    (x0 ::
      (x0 ::
        (x1 ::
          ((_root_.GebMirror.Kernel.«Check.tyArrow»
            (_root_.Geb.Kernel.leaf 0)
            (_root_.GebMirror.Kernel.«Check.tyArrow»
              (_root_.GebMirror.Kernel.«Check.tyList» (_root_.Geb.Kernel.leaf 0))
              (_root_.Geb.Kernel.leaf 0))) ::
            ((_root_.GebMirror.Kernel.«Check.tyArrow»
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.Kernel.«Check.tyList» (_root_.Geb.Kernel.leaf 0))) ::
              ([] : _root_.List _root_.Geb.Kernel.Tree))))))
    (_root_.GebMirror.Kernel.«Prelude.append»
      (_root_.GebMirror.Kernel.«Prelude.replicate» (_root_.Geb.Kernel.leaf 8) x1)
      (_root_.GebMirror.Kernel.«Prelude.single» x0))

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
        _root_.GebMirror.Kernel.«Prelude.nth»
          x3
          (_root_.Geb.Kernel.Const.label
            (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
      else
        _root_.GebMirror.Kernel.«Prelude.none»
    else
      if (_root_.Geb.Kernel.Const.eq
        x4
        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x6
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
            x5
            (_root_.Geb.Kernel.leaf 0);
          if (_root_.GebMirror.Kernel.«Check.isTy» x7).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 1)
              (x7 :: x3);
            if (_root_.GebMirror.Kernel.«Prelude.isSome» x8).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.GebMirror.Kernel.«Check.tyArrow» x7 (_root_.GebMirror.Kernel.«Prelude.get» x8))
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none»
        else
          _root_.GebMirror.Kernel.«Prelude.none»
      else
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x6
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 0)
              x3;
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
              x2
              (_root_.Geb.Kernel.leaf 1)
              x3;
            if (_root_.GebMirror.Kernel.«Reader.both» x7 x8).label ≠ 0 then
              if (_root_.GebMirror.Kernel.«Check.isArrow»
                (_root_.GebMirror.Kernel.«Prelude.get» x7)).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Kernel.«Prelude.get» x8)
                  (_root_.Geb.Kernel.Const.child
                    (_root_.GebMirror.Kernel.«Prelude.get» x7)
                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Prelude.some»
                    (_root_.Geb.Kernel.Const.child
                      (_root_.GebMirror.Kernel.«Prelude.get» x7)
                      (_root_.Geb.Kernel.leaf 1))
                else
                  _root_.GebMirror.Kernel.«Prelude.none»
              else
                _root_.GebMirror.Kernel.«Prelude.none»
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 1)
            else
              _root_.GebMirror.Kernel.«Prelude.none»
          else
            if (_root_.Geb.Kernel.Const.eq
              x4
              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
              if (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                _root_.GebMirror.Kernel.«Reader.some2»
                  (_root_.Geb.Kernel.leaf 2)
                  (_root_.GebMirror.Kernel.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 0) x3)
                  (_root_.GebMirror.Kernel.«Reader.rrAt» x2 (_root_.Geb.Kernel.leaf 1) x3)
              else
                _root_.GebMirror.Kernel.«Prelude.none»
            else
              if (_root_.Geb.Kernel.Const.eq
                x4
                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                    x2
                    (_root_.Geb.Kernel.leaf 0)
                    x3;
                  if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                    if (_root_.GebMirror.Kernel.«Check.isProd»
                      (_root_.GebMirror.Kernel.«Prelude.get» x7)).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Prelude.some»
                        (_root_.Geb.Kernel.Const.child
                          (_root_.GebMirror.Kernel.«Prelude.get» x7)
                          (_root_.Geb.Kernel.leaf 0))
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»
                  else
                    _root_.GebMirror.Kernel.«Prelude.none»
                else
                  _root_.GebMirror.Kernel.«Prelude.none»
              else
                if (_root_.Geb.Kernel.Const.eq
                  x4
                  (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                  if (_root_.Geb.Kernel.Const.eq
                    x6
                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                      x2
                      (_root_.Geb.Kernel.leaf 0)
                      x3;
                    if (_root_.GebMirror.Kernel.«Prelude.isSome» x7).label ≠ 0 then
                      if (_root_.GebMirror.Kernel.«Check.isProd»
                        (_root_.GebMirror.Kernel.«Prelude.get» x7)).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Prelude.some»
                          (_root_.Geb.Kernel.Const.child
                            (_root_.GebMirror.Kernel.«Prelude.get» x7)
                            (_root_.Geb.Kernel.leaf 1))
                      else
                        _root_.GebMirror.Kernel.«Prelude.none»
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»
                  else
                    _root_.GebMirror.Kernel.«Prelude.none»
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x4
                    (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                    if (_root_.Geb.Kernel.Const.eq
                      x6
                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
                    else
                      _root_.GebMirror.Kernel.«Prelude.none»
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x4
                      (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                      if (_root_.Geb.Kernel.Const.eq
                        x6
                        (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 0)
                          x3;
                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 1)
                          x3;
                        let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                          x2
                          (_root_.Geb.Kernel.leaf 2)
                          x3;
                        if (_root_.GebMirror.Kernel.«Reader.both»
                          x7
                          (_root_.GebMirror.Kernel.«Reader.both» x8 x9)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.equal
                            (_root_.GebMirror.Kernel.«Prelude.get» x7)
                            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                            if (_root_.Geb.Kernel.Const.equal
                              (_root_.GebMirror.Kernel.«Prelude.get» x9)
                              (_root_.GebMirror.Kernel.«Prelude.get» x8)).label ≠ 0 then
                              x8
                            else
                              _root_.GebMirror.Kernel.«Prelude.none»
                          else
                            _root_.GebMirror.Kernel.«Prelude.none»
                        else
                          _root_.GebMirror.Kernel.«Prelude.none»
                      else
                        _root_.GebMirror.Kernel.«Prelude.none»
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x4
                        (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                        if (_root_.Geb.Kernel.Const.eq
                          x6
                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                          if (_root_.GebMirror.Kernel.«Check.isTy»
                            (_root_.GebMirror.Kernel.«Prelude.at»
                              x5
                              (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                            _root_.GebMirror.Kernel.«Prelude.some»
                              (_root_.GebMirror.Kernel.«Check.foldTy»
                                (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                          else
                            _root_.GebMirror.Kernel.«Prelude.none»
                        else
                          _root_.GebMirror.Kernel.«Prelude.none»
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x4
                          (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                          if (_root_.Geb.Kernel.Const.eq
                            x6
                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                            if (_root_.GebMirror.Kernel.«Check.isTy»
                              (_root_.GebMirror.Kernel.«Prelude.at»
                                x5
                                (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                              _root_.GebMirror.Kernel.«Prelude.some»
                                (_root_.GebMirror.Kernel.«Check.foldTy»
                                  (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                            else
                              _root_.GebMirror.Kernel.«Prelude.none»
                          else
                            _root_.GebMirror.Kernel.«Prelude.none»
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x4
                            (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                            if (_root_.Geb.Kernel.Const.eq
                              x6
                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                              if (_root_.GebMirror.Kernel.«Check.isTy»
                                (_root_.GebMirror.Kernel.«Prelude.at»
                                  x5
                                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                _root_.GebMirror.Kernel.«Prelude.some»
                                  (_root_.GebMirror.Kernel.«Check.iterTy»
                                    (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                              else
                                _root_.GebMirror.Kernel.«Prelude.none»
                            else
                              _root_.GebMirror.Kernel.«Prelude.none»
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x4
                              (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                              if (_root_.Geb.Kernel.Const.eq
                                x6
                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                if (_root_.GebMirror.Kernel.«Check.isTy»
                                  (_root_.GebMirror.Kernel.«Prelude.at»
                                    x5
                                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                  _root_.GebMirror.Kernel.«Prelude.some»
                                    (_root_.GebMirror.Kernel.«Check.tyList»
                                      (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                                else
                                  _root_.GebMirror.Kernel.«Prelude.none»
                              else
                                _root_.GebMirror.Kernel.«Prelude.none»
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x4
                                (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                                if (_root_.Geb.Kernel.Const.eq
                                  x6
                                  (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                  let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                                    x2
                                    (_root_.Geb.Kernel.leaf 0)
                                    x3;
                                  let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Reader.rrAt»
                                    x2
                                    (_root_.Geb.Kernel.leaf 1)
                                    x3;
                                  if (_root_.GebMirror.Kernel.«Reader.both» x7 x8).label ≠ 0 then
                                    if (_root_.GebMirror.Kernel.«Check.isListTy»
                                      (_root_.GebMirror.Kernel.«Prelude.get» x8)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.equal
                                        (_root_.GebMirror.Kernel.«Prelude.get» x7)
                                        (_root_.Geb.Kernel.Const.child
                                          (_root_.GebMirror.Kernel.«Prelude.get» x8)
                                          (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                        _root_.GebMirror.Kernel.«Prelude.some»
                                          (_root_.GebMirror.Kernel.«Check.tyList»
                                            (_root_.GebMirror.Kernel.«Prelude.get» x7))
                                      else
                                        _root_.GebMirror.Kernel.«Prelude.none»
                                    else
                                      _root_.GebMirror.Kernel.«Prelude.none»
                                  else
                                    _root_.GebMirror.Kernel.«Prelude.none»
                                else
                                  _root_.GebMirror.Kernel.«Prelude.none»
                              else
                                if (_root_.Geb.Kernel.Const.eq
                                  x4
                                  (_root_.Geb.Kernel.leaf 21)).label ≠ 0 then
                                  if (_root_.Geb.Kernel.Const.eq
                                    x6
                                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                    if (_root_.GebMirror.Kernel.«Prelude.and»
                                      (_root_.GebMirror.Kernel.«Check.isTy»
                                        (_root_.GebMirror.Kernel.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
                                      (_root_.GebMirror.Kernel.«Check.isTy»
                                        (_root_.GebMirror.Kernel.«Prelude.at»
                                          x5
                                          (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                      _root_.GebMirror.Kernel.«Prelude.some»
                                        (_root_.GebMirror.Kernel.«Check.foldrTy»
                                          (_root_.GebMirror.Kernel.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 0))
                                          (_root_.GebMirror.Kernel.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 1)))
                                    else
                                      _root_.GebMirror.Kernel.«Prelude.none»
                                  else
                                    _root_.GebMirror.Kernel.«Prelude.none»
                                else
                                  if (_root_.Geb.Kernel.Const.eq
                                    x4
                                    (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                    if (_root_.Geb.Kernel.Const.eq
                                      x6
                                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                      _root_.GebMirror.Kernel.«Prelude.nth»
                                        _root_.GebMirror.Kernel.«Check.primTypes»
                                        (_root_.Geb.Kernel.Const.label
                                          (_root_.GebMirror.Kernel.«Prelude.at»
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)))
                                    else
                                      _root_.GebMirror.Kernel.«Prelude.none»
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x4
                                      (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
                                      if (_root_.Geb.Kernel.Const.eq
                                        x6
                                        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                        _root_.GebMirror.Kernel.«Prelude.nth»
                                          x0
                                          (_root_.Geb.Kernel.Const.label
                                            (_root_.GebMirror.Kernel.«Prelude.at»
                                              x5
                                              (_root_.Geb.Kernel.leaf 0)))
                                      else
                                        _root_.GebMirror.Kernel.«Prelude.none»
                                    else
                                      if (_root_.Geb.Kernel.Const.eq
                                        x4
                                        (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                                        if (_root_.Geb.Kernel.Const.eq
                                          x6
                                          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                          if (_root_.GebMirror.Kernel.«Prelude.and»
                                            (_root_.GebMirror.Kernel.«Check.isTy»
                                              (_root_.GebMirror.Kernel.«Prelude.at»
                                                x5
                                                (_root_.Geb.Kernel.leaf 0)))
                                            (_root_.GebMirror.Kernel.«Check.isTy»
                                              (_root_.GebMirror.Kernel.«Prelude.at»
                                                x5
                                                (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                            _root_.GebMirror.Kernel.«Prelude.some»
                                              (_root_.GebMirror.Kernel.«Check.lcaseTy»
                                                (_root_.GebMirror.Kernel.«Prelude.at»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Kernel.«Prelude.at»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 1)))
                                          else
                                            _root_.GebMirror.Kernel.«Prelude.none»
                                        else
                                          _root_.GebMirror.Kernel.«Prelude.none»
                                      else
                                        _root_.GebMirror.Kernel.«Prelude.none»

def «Check.typeInStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      x1
      (_root_.GebMirror.Kernel.«Reader.rrTrees» x2);
    (x3,
      fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Kernel.«Check.checkNode» x0 x3 x2 x4)

def «Check.typeIn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Kernel.«Check.typeInStep» x0)
      x2).2
      x1

def «Check.typeOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Kernel.«Check.typeIn»
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
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Check.typeOf»
              (x3).2
              x1;
            if (_root_.GebMirror.Kernel.«Prelude.isSome» x4).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                _root_.GebMirror.Kernel.«Prelude.append»
                  (x3).2
                  (_root_.GebMirror.Kernel.«Prelude.single» (_root_.GebMirror.Kernel.«Prelude.get» x4)))
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
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) (x1).2)
    else
      _root_.GebMirror.Kernel.«Prelude.none»

def «Eval.bindO» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.Kernel.«Prelude.get» x0)
    else
      _root_.GebMirror.Kernel.«Prelude.none»);
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
        if (_root_.GebMirror.Kernel.«Prelude.isSome» x1).label ≠ 0 then
          _root_.GebMirror.Kernel.«Eval.bindO»
            x2
            (fun (x3 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ((_root_.GebMirror.Kernel.«Prelude.get» x1) ::
                    (_root_.Geb.Kernel.Const.children x3))))
        else
          _root_.GebMirror.Kernel.«Prelude.none»)
      (_root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «Eval.valQuote» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 15)
      (_root_.GebMirror.Kernel.«Prelude.single» x0);
    x1

def «Eval.valUnit» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 11)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Eval.valPair» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 12)
      (x0 :: (_root_.GebMirror.Kernel.«Prelude.single» x1));
    x2

def «Eval.valClo» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 26)
      ((_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0) ::
        (x1 :: (_root_.GebMirror.Kernel.«Prelude.single» x2)));
    x3

def «Eval.valApp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 10)
      (x0 :: (_root_.GebMirror.Kernel.«Prelude.single» x1));
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
          (x2 :: (_root_.GebMirror.Kernel.«Prelude.single» x3)))
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 19)
        (_root_.GebMirror.Kernel.«Prelude.single» x0))
      x1;
    x2

def «Eval.unquote» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 15))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
    else
      _root_.GebMirror.Kernel.«Prelude.none»);
    x1

def «Eval.listOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Kernel.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 19))
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.arity x1)
            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
          _root_.GebMirror.Kernel.«Prelude.some»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 0)
              ([] : _root_.List _root_.Geb.Kernel.Tree))
        else
          if (_root_.GebMirror.Kernel.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x1)
              (_root_.Geb.Kernel.leaf 20))
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.arity x1)
              (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
            _root_.GebMirror.Kernel.«Eval.bindO»
              (_root_.GebMirror.Kernel.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1))
              (fun (x3 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    ((_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)) ::
                      (_root_.Geb.Kernel.Const.children x3))))
          else
            _root_.GebMirror.Kernel.«Prelude.none»)
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
        if (_root_.GebMirror.Kernel.«Prelude.and»
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
                _root_.GebMirror.Kernel.«Prelude.append»
                  (x3).2
                  (_root_.GebMirror.Kernel.«Prelude.single»
                    (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))))
        else
          (x1, ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «Eval.primArity» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 0))
      (_root_.GebMirror.Kernel.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Kernel.«Prelude.or»
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
                                        if (_root_.GebMirror.Kernel.«Prelude.and»
                                          (_root_.GebMirror.Kernel.«Prelude.or»
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
                                          if (_root_.GebMirror.Kernel.«Prelude.or»
                                            (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 18))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 1)))
                                            (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.GebMirror.Kernel.«Prelude.or»
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
                                            if (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 22))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                              _root_.GebMirror.Kernel.«Eval.primArity»
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
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Eval.bindO»
      (_root_.GebMirror.Kernel.«Eval.allSomeT»
        (_root_.GebMirror.Kernel.«Eval.mapT» _root_.GebMirror.Kernel.«Eval.unquote» x1))
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.length» x3;
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
          x3
          (_root_.Geb.Kernel.leaf 0);
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
          x3
          (_root_.Geb.Kernel.leaf 1);
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.Kernel.«Prelude.some»
              (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.label x5))
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.arity x5))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.GebMirror.Kernel.«Eval.ofList»
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.GebMirror.Kernel.«Eval.mapT»
                      _root_.GebMirror.Kernel.«Eval.valQuote»
                      (_root_.Geb.Kernel.Const.children x5)))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Prelude.some»
                    (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.log2 x5))
                else
                  _root_.GebMirror.Kernel.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              _root_.GebMirror.Kernel.«Prelude.some»
                (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.child x5 x6))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.add x5 x6))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                  _root_.GebMirror.Kernel.«Prelude.some»
                    (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.sub x5 x6))
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                    _root_.GebMirror.Kernel.«Prelude.some»
                      (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.mul x5 x6))
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                      _root_.GebMirror.Kernel.«Prelude.some»
                        (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.div x5 x6))
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                        _root_.GebMirror.Kernel.«Prelude.some»
                          (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.mod x5 x6))
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                          _root_.GebMirror.Kernel.«Prelude.some»
                            (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.eq x5 x6))
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                            _root_.GebMirror.Kernel.«Prelude.some»
                              (_root_.GebMirror.Kernel.«Eval.valQuote» (_root_.Geb.Kernel.Const.lt x5 x6))
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x0
                              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                              _root_.GebMirror.Kernel.«Prelude.some»
                                (_root_.GebMirror.Kernel.«Eval.valQuote»
                                  (_root_.Geb.Kernel.Const.equal x5 x6))
                            else
                              _root_.GebMirror.Kernel.«Prelude.none»
          else
            _root_.GebMirror.Kernel.«Prelude.none»);
    x2

def «Eval.primNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Eval.bindO»
      (_root_.GebMirror.Kernel.«Eval.unquote» x0)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Kernel.«Eval.bindO»
          (_root_.GebMirror.Kernel.«Eval.listOf» x1)
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Kernel.«Eval.bindO»
              (_root_.GebMirror.Kernel.«Eval.allSomeT»
                (_root_.GebMirror.Kernel.«Eval.mapT»
                  _root_.GebMirror.Kernel.«Eval.unquote»
                  (_root_.Geb.Kernel.Const.children x3)))
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Kernel.«Prelude.some»
                  (_root_.GebMirror.Kernel.«Eval.valQuote»
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
        _root_.GebMirror.Kernel.«Eval.bindO»
          (_root_.GebMirror.Kernel.«Eval.allSomeT» x5)
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Kernel.«Eval.bindO»
              (x0
                x2
                (_root_.GebMirror.Kernel.«Eval.valQuote»
                  (_root_.Geb.Kernel.Const.node
                    x4
                    ([] : _root_.List _root_.Geb.Kernel.Tree))))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                x0
                  x7
                  (_root_.GebMirror.Kernel.«Eval.ofList»
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
        _root_.GebMirror.Kernel.«Eval.bindO»
          (_root_.GebMirror.Kernel.«Eval.allSomeT» x5)
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Kernel.«Eval.bindO»
              (x0 x2 (_root_.GebMirror.Kernel.«Eval.valQuote» x4))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                x0
                  x7
                  (_root_.GebMirror.Kernel.«Eval.ofList»
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
        _root_.GebMirror.Kernel.«Eval.bindO» x4 (x0 x1))
      (_root_.GebMirror.Kernel.«Prelude.some» x2)
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
        _root_.GebMirror.Kernel.«Eval.bindO»
          x5
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Kernel.«Eval.bindO»
              (x0 x1 x4)
              (fun (x7 : _root_.Geb.Kernel.Tree) => x0 x7 x6)))
      (_root_.GebMirror.Kernel.«Prelude.some» x2)
      x3;
    x4

def «Eval.lcaseVal» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x1)
        (_root_.Geb.Kernel.leaf 19))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x1)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some» x2
    else
      if (_root_.GebMirror.Kernel.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          (_root_.Geb.Kernel.leaf 20))
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.arity x1)
          (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
        _root_.GebMirror.Kernel.«Eval.bindO»
          (x0 x3 (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)))
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            x0 x4 (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 1)))
      else
        _root_.GebMirror.Kernel.«Prelude.none»);
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
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.length»
                                          x2;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.at»
                                          x2
                                          (_root_.Geb.Kernel.leaf 2);
                                        if (_root_.GebMirror.Kernel.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 17))
                                          (_root_.GebMirror.Kernel.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 1))
                                            (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                          _root_.GebMirror.Kernel.«Eval.bindO»
                                            (_root_.GebMirror.Kernel.«Eval.unquote» x7)
                                            (_root_.GebMirror.Kernel.«Eval.foldVal»
                                              x0
                                              (_root_.Geb.Kernel.Const.child
                                                x1
                                                (_root_.Geb.Kernel.leaf 0))
                                              x6)
                                        else
                                          if (_root_.GebMirror.Kernel.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 25))
                                            (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x4
                                                (_root_.Geb.Kernel.leaf 1))
                                              (_root_.Geb.Kernel.Const.eq
                                                x5
                                                (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                            _root_.GebMirror.Kernel.«Eval.bindO»
                                              (_root_.GebMirror.Kernel.«Eval.unquote» x7)
                                              (_root_.GebMirror.Kernel.«Eval.paraVal»
                                                x0
                                                (_root_.Geb.Kernel.Const.child
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 0))
                                                x6)
                                          else
                                            if (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 18))
                                              (_root_.GebMirror.Kernel.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                              _root_.GebMirror.Kernel.«Eval.bindO»
                                                (_root_.GebMirror.Kernel.«Eval.unquote» x8)
                                                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Kernel.«Eval.iterVal»
                                                    x0
                                                    x6
                                                    x7
                                                    (_root_.Geb.Kernel.Const.label x9))
                                            else
                                              if (_root_.GebMirror.Kernel.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 21))
                                                (_root_.GebMirror.Kernel.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 2))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                                _root_.GebMirror.Kernel.«Eval.bindO»
                                                  (_root_.GebMirror.Kernel.«Eval.listOf» x8)
                                                  (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Kernel.«Eval.foldrVal»
                                                      x0
                                                      x6
                                                      x7
                                                      (_root_.Geb.Kernel.Const.children x9))
                                              else
                                                if (_root_.GebMirror.Kernel.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 24))
                                                  (_root_.GebMirror.Kernel.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 2))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 3)))).label ≠ 0 then
                                                  _root_.GebMirror.Kernel.«Eval.lcaseVal» x0 x6 x7 x8
                                                else
                                                  if (_root_.GebMirror.Kernel.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 22))
                                                    (_root_.GebMirror.Kernel.«Prelude.and»
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
                                                      _root_.GebMirror.Kernel.«Eval.primNode» x6 x7
                                                    else
                                                      _root_.GebMirror.Kernel.«Eval.primApply»
                                                        (_root_.Geb.Kernel.Const.label
                                                          (_root_.Geb.Kernel.Const.child
                                                            x1
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                        x2
                                                  else
                                                    if (_root_.GebMirror.Kernel.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 22))
                                                      (_root_.GebMirror.Kernel.«Prelude.and»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 1))
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
                                                      _root_.GebMirror.Kernel.«Eval.primApply»
                                                        (_root_.Geb.Kernel.Const.label
                                                          (_root_.Geb.Kernel.Const.child
                                                            x1
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                        x2
                                                    else
                                                      _root_.GebMirror.Kernel.«Prelude.none»);
    x3

def «Eval.pairFst» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 12))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
    else
      _root_.GebMirror.Kernel.«Prelude.none»);
    x1

def «Eval.pairSnd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Kernel.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 12))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.Kernel.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1))
    else
      _root_.GebMirror.Kernel.«Prelude.none»);
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
                                            _root_.GebMirror.Kernel.«Prelude.none»)
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
                                            _root_.GebMirror.Kernel.«Prelude.none»)
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
                                                _root_.GebMirror.Kernel.«Prelude.none»)
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
                                            _root_.GebMirror.Kernel.«Prelude.none»)
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
                                                _root_.GebMirror.Kernel.«Prelude.none»)
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
                                                    _root_.GebMirror.Kernel.«Prelude.none»)
                                                  (fun (x13 : _root_.List _root_.Geb.Kernel.Tree →
                                                       _root_.Geb.Kernel.Tree)
                                                     (_ : _root_.List
                                                       (_root_.List _root_.Geb.Kernel.Tree →
                                                         _root_.Geb.Kernel.Tree)) =>
                                                    x13)));
                                        if (_root_.GebMirror.Kernel.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 8))
                                          (_root_.Geb.Kernel.Const.eq
                                            x6
                                            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                          _root_.GebMirror.Kernel.«Prelude.nth»
                                            x4
                                            (_root_.Geb.Kernel.Const.label
                                              (_root_.Geb.Kernel.Const.child
                                                x2
                                                (_root_.Geb.Kernel.leaf 0)))
                                        else
                                          if (_root_.GebMirror.Kernel.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 9))
                                            (_root_.Geb.Kernel.Const.eq
                                              x6
                                              (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                            _root_.GebMirror.Kernel.«Prelude.some»
                                              (_root_.GebMirror.Kernel.«Eval.valClo»
                                                x4
                                                (_root_.Geb.Kernel.Const.child
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.Geb.Kernel.Const.child
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 1)))
                                          else
                                            if (_root_.GebMirror.Kernel.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                x5
                                                (_root_.Geb.Kernel.leaf 10))
                                              (_root_.Geb.Kernel.Const.eq
                                                x6
                                                (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                              _root_.GebMirror.Kernel.«Eval.bindO»
                                                (x7 x4)
                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Kernel.«Eval.bindO»
                                                    (x8 x4)
                                                    (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                      (x1).2 x10 x11))
                                            else
                                              if (_root_.GebMirror.Kernel.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 11))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x6
                                                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                                _root_.GebMirror.Kernel.«Prelude.some»
                                                  _root_.GebMirror.Kernel.«Eval.valUnit»
                                              else
                                                if (_root_.GebMirror.Kernel.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 12))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x6
                                                    (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                  _root_.GebMirror.Kernel.«Eval.bindO»
                                                    (x7 x4)
                                                    (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Kernel.«Eval.bindO»
                                                        (x8 x4)
                                                        (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                          _root_.GebMirror.Kernel.«Prelude.some»
                                                            (_root_.GebMirror.Kernel.«Eval.valPair»
                                                              x10
                                                              x11)))
                                                else
                                                  if (_root_.GebMirror.Kernel.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 13))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                    _root_.GebMirror.Kernel.«Eval.bindO»
                                                      (x7 x4)
                                                      _root_.GebMirror.Kernel.«Eval.pairFst»
                                                  else
                                                    if (_root_.GebMirror.Kernel.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x5
                                                        (_root_.Geb.Kernel.leaf 14))
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x6
                                                        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                      _root_.GebMirror.Kernel.«Eval.bindO»
                                                        (x7 x4)
                                                        _root_.GebMirror.Kernel.«Eval.pairSnd»
                                                    else
                                                      if (_root_.GebMirror.Kernel.«Prelude.and»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 15))
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x6
                                                          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                        _root_.GebMirror.Kernel.«Prelude.some»
                                                          (_root_.GebMirror.Kernel.«Eval.valQuote»
                                                            (_root_.Geb.Kernel.Const.child
                                                              x2
                                                              (_root_.Geb.Kernel.leaf 0)))
                                                      else
                                                        if (_root_.GebMirror.Kernel.«Prelude.and»
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 16))
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x6
                                                            (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                                          _root_.GebMirror.Kernel.«Eval.bindO»
                                                            (x7 x4)
                                                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                              _root_.GebMirror.Kernel.«Eval.bindO»
                                                                (_root_.GebMirror.Kernel.«Eval.unquote» x10)
                                                                (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                  if (_root_.Geb.Kernel.Const.eq
                                                                    (_root_.Geb.Kernel.Const.label
                                                                      x11)
                                                                    (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                                    x9 x4
                                                                  else
                                                                    x8 x4))
                                                        else
                                                          if (_root_.GebMirror.Kernel.«Prelude.and»
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 19))
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x6
                                                              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                            _root_.GebMirror.Kernel.«Prelude.some»
                                                              (_root_.Geb.Kernel.Const.node
                                                                (_root_.Geb.Kernel.leaf 19)
                                                                (_root_.GebMirror.Kernel.«Prelude.single»
                                                                  (_root_.Geb.Kernel.Const.child
                                                                    x2
                                                                    (_root_.Geb.Kernel.leaf 0))))
                                                          else
                                                            if (_root_.GebMirror.Kernel.«Prelude.and»
                                                              (_root_.Geb.Kernel.Const.eq
                                                                x5
                                                                (_root_.Geb.Kernel.leaf 20))
                                                              (_root_.Geb.Kernel.Const.eq
                                                                x6
                                                                (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                              _root_.GebMirror.Kernel.«Eval.bindO»
                                                                (x7 x4)
                                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                  _root_.GebMirror.Kernel.«Eval.bindO»
                                                                    (x8 x4)
                                                                    (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                      _root_.GebMirror.Kernel.«Prelude.some»
                                                                        (_root_.Geb.Kernel.Const.node
                                                                          (_root_.Geb.Kernel.leaf 20)
                                                                          (x10 ::
                                                                            (_root_.GebMirror.Kernel.«Prelude.single»
                                                                              x11)))))
                                                            else
                                                              if (_root_.GebMirror.Kernel.«Prelude.or»
                                                                (_root_.GebMirror.Kernel.«Prelude.and»
                                                                  (_root_.GebMirror.Kernel.«Prelude.or»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 17))
                                                                    (_root_.GebMirror.Kernel.«Prelude.or»
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        x5
                                                                        (_root_.Geb.Kernel.leaf 25))
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        x5
                                                                        (_root_.Geb.Kernel.leaf 18))))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 1)))
                                                                (_root_.GebMirror.Kernel.«Prelude.and»
                                                                  (_root_.GebMirror.Kernel.«Prelude.or»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 21))
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 24)))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                                                _root_.GebMirror.Kernel.«Prelude.some» x2
                                                              else
                                                                if (_root_.GebMirror.Kernel.«Prelude.and»
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x5
                                                                    (_root_.Geb.Kernel.leaf 22))
                                                                  (_root_.Geb.Kernel.Const.eq
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                                  _root_.GebMirror.Kernel.«Prelude.some»
                                                                    (_root_.Geb.Kernel.Const.node
                                                                      (_root_.Geb.Kernel.leaf 22)
                                                                      (_root_.GebMirror.Kernel.«Prelude.single»
                                                                        (_root_.Geb.Kernel.Const.node
                                                                          (_root_.Geb.Kernel.Const.label
                                                                            (_root_.Geb.Kernel.Const.child
                                                                              x2
                                                                              (_root_.Geb.Kernel.leaf 0)))
                                                                          ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                                                else
                                                                  if (_root_.GebMirror.Kernel.«Prelude.and»
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 23))
                                                                    (_root_.Geb.Kernel.Const.eq
                                                                      x6
                                                                      (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                                                    _root_.GebMirror.Kernel.«Eval.bindO»
                                                                      (_root_.GebMirror.Kernel.«Prelude.nth»
                                                                        x0
                                                                        (_root_.Geb.Kernel.Const.label
                                                                          (_root_.Geb.Kernel.Const.child
                                                                            x2
                                                                            (_root_.Geb.Kernel.leaf 0))))
                                                                      ((x1).1
                                                                        ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                                  else
                                                                    _root_.GebMirror.Kernel.«Prelude.none»);
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
                                        if (_root_.GebMirror.Kernel.«Prelude.or»
                                          (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 10))
                                          (_root_.GebMirror.Kernel.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 17))
                                            (_root_.GebMirror.Kernel.«Prelude.or»
                                              (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 25))
                                              (_root_.GebMirror.Kernel.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 18))
                                                (_root_.GebMirror.Kernel.«Prelude.or»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 21))
                                                  (_root_.GebMirror.Kernel.«Prelude.or»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 24))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 22)))))))).label ≠ 0 then
                                          let x4 : _root_.Geb.Kernel.Tree ×
                                            _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Eval.spine»
                                            x1;
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Kernel.«Prelude.append»
                                            (x4).2
                                            (_root_.GebMirror.Kernel.«Prelude.single» x2);
                                          if (_root_.Geb.Kernel.Const.lt
                                            (_root_.GebMirror.Kernel.«Prelude.length» x5)
                                            (_root_.GebMirror.Kernel.«Eval.constArity»
                                              (x4).1)).label ≠ 0 then
                                            _root_.GebMirror.Kernel.«Prelude.some»
                                              (_root_.GebMirror.Kernel.«Eval.valApp» x1 x2)
                                          else
                                            _root_.GebMirror.Kernel.«Eval.sat» (x0).2 (x4).1 x5
                                        else
                                          if (_root_.GebMirror.Kernel.«Prelude.and»
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
                                            _root_.GebMirror.Kernel.«Prelude.none»);
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
        (_root_.GebMirror.Kernel.«Eval.evStep» x0 x1)
        x3
        x2,
      _root_.GebMirror.Kernel.«Eval.apStep» x1);
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
      (_root_.GebMirror.Kernel.«Eval.next» x0)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Kernel.«Prelude.none»,
        fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Kernel.«Prelude.none»)
      x1;
    x2

def «Eval.eval» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.Kernel.«Eval.level»
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
    let x4 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.Kernel.«Eval.level»
      x0
      x1).2
      x2
      x3;
    x4

end GebMirror.Kernel

end
