module

public import GebMirror.Metalogic.Combinator

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Datatype.sx1» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)

def «Datatype.sx2» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (_root_.GebMirror.Metalogic.«Prelude.single» x1))

def «Datatype.sx3» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: (_root_.GebMirror.Metalogic.«Prelude.single» x2)))

def «Datatype.sx4» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: (x2 :: (_root_.GebMirror.Metalogic.«Prelude.single» x3))))

def «Datatype.sx5» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: (x2 :: (x3 :: (_root_.GebMirror.Metalogic.«Prelude.single» x4)))))

def «Datatype.sx6» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 ::
        (x1 :: (x2 :: (x3 :: (x4 :: (_root_.GebMirror.Metalogic.«Prelude.single» x5))))))

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

def «Datatype.aFold» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 102,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 108,
    _root_.Geb.Kernel.leaf 100]

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
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 115]

def «Datatype.aL» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 108]

def «Datatype.aRs» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 114,
    _root_.Geb.Kernel.leaf 115]

def «Datatype.aO» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 111]

def «Datatype.aP» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 112]

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
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 117]

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

def «Datatype.aE» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aQuote» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 113,
    _root_.Geb.Kernel.leaf 117,
    _root_.Geb.Kernel.leaf 111,
    _root_.Geb.Kernel.leaf 116,
    _root_.Geb.Kernel.leaf 101]

def «Datatype.aK» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 107]

def «Datatype.aC» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 99]

def «Datatype.aQ» :=
  _root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 37,
    _root_.Geb.Kernel.leaf 113]

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

def «Datatype.kwAmp» :=
  _root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 38]

def «Datatype.decimalChars» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.single» (_root_.Geb.Kernel.leaf 48)
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
        (_root_.GebMirror.Metalogic.«Prelude.digitsMsb» (_root_.Geb.Kernel.leaf 10) x0 x1)

def «Datatype.numAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Datatype.decimalChars» x0)

def «Datatype.memberName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Prelude.append»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.Const.children
          (_root_.Geb.Kernel.mk 1 [_root_.Geb.Kernel.leaf 46,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 109,
            _root_.Geb.Kernel.leaf 98,
            _root_.Geb.Kernel.leaf 101,
            _root_.Geb.Kernel.leaf 114])))

def «Datatype.fieldAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      ((_root_.Geb.Kernel.leaf 37) ::
        ((_root_.Geb.Kernel.leaf 102) ::
          (_root_.GebMirror.Metalogic.«Datatype.decimalChars» x0)))

def «Datatype.sList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx2» _root_.GebMirror.Metalogic.«Datatype.aList» x0

def «Datatype.sProd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx3» _root_.GebMirror.Metalogic.«Datatype.aProd» x0 x1

def «Datatype.sArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx3» _root_.GebMirror.Metalogic.«Datatype.aArrow» x0 x1

def «Datatype.sLet» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx5»
      _root_.GebMirror.Metalogic.«Datatype.aLet»
      x0
      x1
      x2
      x3

def «Datatype.sIf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx4» _root_.GebMirror.Metalogic.«Datatype.aIf» x0 x1 x2

def «Datatype.sLam1» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx3»
      _root_.GebMirror.Metalogic.«Datatype.aLam»
      (_root_.GebMirror.Metalogic.«Datatype.sx1» (_root_.GebMirror.Metalogic.«Datatype.sx2» x0 x1))
      x2

def «Datatype.sLam2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx3»
      _root_.GebMirror.Metalogic.«Datatype.aLam»
      (_root_.GebMirror.Metalogic.«Datatype.sx2»
        (_root_.GebMirror.Metalogic.«Datatype.sx2» x0 x1)
        (_root_.GebMirror.Metalogic.«Datatype.sx2» x2 x3))
      x4

def «Datatype.sTail» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sLam1»
      _root_.GebMirror.Metalogic.«Datatype.aX»
      (_root_.GebMirror.Metalogic.«Datatype.sList» x0)
      (_root_.GebMirror.Metalogic.«Datatype.sx6»
        _root_.GebMirror.Metalogic.«Datatype.aLcase»
        x0
        (_root_.GebMirror.Metalogic.«Datatype.sList» x0)
        _root_.GebMirror.Metalogic.«Datatype.aX»
        (_root_.GebMirror.Metalogic.«Datatype.sx2» _root_.GebMirror.Metalogic.«Datatype.aNil» x0)
        (_root_.GebMirror.Metalogic.«Datatype.sLam2»
          _root_.GebMirror.Metalogic.«Datatype.aH»
          x0
          _root_.GebMirror.Metalogic.«Datatype.aTl»
          (_root_.GebMirror.Metalogic.«Datatype.sList» x0)
          _root_.GebMirror.Metalogic.«Datatype.aTl»))

def «Datatype.sHeadOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx6»
      _root_.GebMirror.Metalogic.«Datatype.aLcase»
      _root_.GebMirror.Metalogic.«Datatype.aT»
      _root_.GebMirror.Metalogic.«Datatype.aT»
      x0
      _root_.GebMirror.Metalogic.«Datatype.aZero»
      (_root_.GebMirror.Metalogic.«Datatype.sLam2»
        _root_.GebMirror.Metalogic.«Datatype.aH»
        _root_.GebMirror.Metalogic.«Datatype.aT»
        _root_.GebMirror.Metalogic.«Datatype.aTl»
        (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
        _root_.GebMirror.Metalogic.«Datatype.aH»)

def «Datatype.sTailOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sx6»
      _root_.GebMirror.Metalogic.«Datatype.aLcase»
      _root_.GebMirror.Metalogic.«Datatype.aT»
      (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
      x0
      (_root_.GebMirror.Metalogic.«Datatype.sx2»
        _root_.GebMirror.Metalogic.«Datatype.aNil»
        _root_.GebMirror.Metalogic.«Datatype.aT»)
      (_root_.GebMirror.Metalogic.«Datatype.sLam2»
        _root_.GebMirror.Metalogic.«Datatype.aH»
        _root_.GebMirror.Metalogic.«Datatype.aT»
        _root_.GebMirror.Metalogic.«Datatype.aTl»
        (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
        _root_.GebMirror.Metalogic.«Datatype.aTl»)

def «Datatype.dropLast» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Prelude.reverse»
      (_root_.GebMirror.Metalogic.«Prelude.tail» (_root_.GebMirror.Metalogic.«Prelude.reverse» x0))

def «Datatype.zipTs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x1;
    (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        (_root_.Geb.Kernel.Const.add (x4).1 (_root_.Geb.Kernel.leaf 1),
          ((_root_.GebMirror.Metalogic.«Reader.node2»
            (_root_.Geb.Kernel.leaf 0)
            x3
            (_root_.GebMirror.Metalogic.«Prelude.at»
              x1
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x2 (_root_.Geb.Kernel.leaf 1))
                (x4).1))) ::
            (x4).2)))
      (_root_.Geb.Kernel.leaf 0, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0).2

def «Datatype.allTrue» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and» x1 x2)
      (_root_.Geb.Kernel.leaf 1)
      x0

def «Datatype.findCtor» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 5))
          (_root_.Geb.Kernel.Const.equal
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))
            x0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some» x2
        else
          x3)
      _root_.GebMirror.Metalogic.«Prelude.none»
      x1

def «Datatype.isData» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 6))
          (_root_.Geb.Kernel.Const.equal
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))
            x0)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          x3)
      (_root_.Geb.Kernel.leaf 0)
      x1

def «Datatype.findAlias» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 7))
          (_root_.Geb.Kernel.Const.equal
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))
            x0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1))
        else
          x3)
      _root_.GebMirror.Metalogic.«Prelude.none»
      x1

def «Datatype.ctorsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 5))
          (_root_.Geb.Kernel.Const.equal
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 2))
            x0)).label ≠ 0 then
          (x2 :: x3)
        else
          x3)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1

def «Datatype.expandAliases» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node x2 x3;
        if (_root_.GebMirror.Metalogic.«Reader.isAtom» x4).label ≠ 0 then
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.findAlias»
            (_root_.GebMirror.Metalogic.«Reader.nameOf» x4)
            x0;
          if (_root_.GebMirror.Metalogic.«Prelude.isSome» x5).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.get» x5
          else
            x4
        else
          x4)
      x1

def «Datatype.defaultOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          x1
          (_root_.GebMirror.Metalogic.«Reader.rtTrees» x2);
        let x4 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rtValues» x2;
        (x3,
          if (_root_.GebMirror.Metalogic.«Reader.isAtom» x3).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.equal
              (_root_.GebMirror.Metalogic.«Reader.nameOf» x3)
              _root_.GebMirror.Metalogic.«Reader.kwUnit»).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Datatype.aUnitV»
            else
              _root_.GebMirror.Metalogic.«Datatype.aZero»
          else
            let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x3)
              (_root_.Geb.Kernel.leaf 0);
            if (_root_.GebMirror.Metalogic.«Reader.named»
              x5
              _root_.GebMirror.Metalogic.«Reader.kwProd»).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Datatype.sx3»
                _root_.GebMirror.Metalogic.«Datatype.aPair»
                (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1))
                (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2))
            else
              if (_root_.GebMirror.Metalogic.«Reader.named»
                x5
                _root_.GebMirror.Metalogic.«Reader.kwArrow»).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Datatype.sLam1»
                  _root_.GebMirror.Metalogic.«Datatype.aD»
                  (_root_.GebMirror.Metalogic.«Prelude.at»
                    (_root_.Geb.Kernel.Const.children x3)
                    (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2))
              else
                if (_root_.GebMirror.Metalogic.«Reader.named»
                  x5
                  _root_.GebMirror.Metalogic.«Reader.kwList»).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Datatype.sx2»
                    _root_.GebMirror.Metalogic.«Datatype.aNil»
                    (_root_.GebMirror.Metalogic.«Prelude.at»
                      (_root_.Geb.Kernel.Const.children x3)
                      (_root_.Geb.Kernel.leaf 1))
                else
                  _root_.GebMirror.Metalogic.«Datatype.aZero»))
      x0).2

def «Datatype.bindWith» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
      (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 3));
    let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x3
      (_root_.Geb.Kernel.leaf 4);
    let x8 : _root_.List
      _root_.Geb.Kernel.Tree := (if (x7).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.append»
        (_root_.GebMirror.Metalogic.«Datatype.dropLast»
          (_root_.GebMirror.Metalogic.«Datatype.dropLast» x4))
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Prelude.at»
            x4
            (_root_.Geb.Kernel.Const.sub
              (_root_.GebMirror.Metalogic.«Prelude.length» x4)
              (_root_.Geb.Kernel.leaf 1))))
    else
      x4);
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x4)
        (_root_.Geb.Kernel.Const.add
          (_root_.GebMirror.Metalogic.«Prelude.length» x6)
          (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 2) x7)))
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (if (x7).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Reader.named»
            (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.GebMirror.Metalogic.«Prelude.length» x6))
            _root_.GebMirror.Metalogic.«Datatype.kwAmp»
        else
          _root_.Geb.Kernel.leaf 1)
        (_root_.GebMirror.Metalogic.«Datatype.allTrue»
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            (fun (x9 : _root_.Geb.Kernel.Tree)
               (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
              ((_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.GebMirror.Metalogic.«Reader.isAtom» x9)
                (if (_root_.GebMirror.Metalogic.«Reader.named»
                  x9
                  _root_.GebMirror.Metalogic.«Datatype.kwAmp»).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 0
                else
                  _root_.Geb.Kernel.leaf 1)) ::
                x10))
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            x8)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (x2
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            (fun (x9 : _root_.Geb.Kernel.Tree) (x10 : _root_.Geb.Kernel.Tree) =>
              x0
                (_root_.Geb.Kernel.Const.child x9 (_root_.Geb.Kernel.leaf 1))
                (_root_.Geb.Kernel.Const.child x9 (_root_.Geb.Kernel.leaf 0))
                x10)
            (if (x7).label ≠ 0 then
              x1
                (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 5))
                (_root_.GebMirror.Metalogic.«Prelude.at» x8 (_root_.GebMirror.Metalogic.«Prelude.length» x6))
                x5
            else
              x5)
            (_root_.GebMirror.Metalogic.«Datatype.zipTs»
              (if (x7).label ≠ 0 then _root_.GebMirror.Metalogic.«Datatype.dropLast» x8 else x8)
              x6)))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.clauseCtor» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Reader.isList» x1).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
        x1
        (_root_.Geb.Kernel.leaf 0);
      if (_root_.GebMirror.Metalogic.«Reader.isList» x2).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Datatype.findCtor»
          (_root_.GebMirror.Metalogic.«Reader.nameOf»
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0)))
          x0
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.testChain» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree ×
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree))
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)) =>
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
          x4
          (_root_.Geb.Kernel.leaf 0);
        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
          x4
          (_root_.Geb.Kernel.leaf 1);
        let x8 : _root_.Geb.Kernel.Tree := x3
          x7
          (_root_.GebMirror.Metalogic.«Prelude.tail»
            (_root_.Geb.Kernel.Const.children
              (_root_.Geb.Kernel.Const.child x6 (_root_.Geb.Kernel.leaf 0))))
          (_root_.Geb.Kernel.Const.child
            (_root_.Geb.Kernel.Const.child x4 (_root_.Geb.Kernel.leaf 2))
            (_root_.Geb.Kernel.leaf 1));
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (x5).1
          (_root_.GebMirror.Metalogic.«Prelude.isSome» x8)).label ≠ 0 then
          (_root_.Geb.Kernel.leaf 1,
            (_root_.Geb.Kernel.leaf 1,
              if (((x5).2).1).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Datatype.sIf»
                  (_root_.GebMirror.Metalogic.«Datatype.sx3»
                    _root_.GebMirror.Metalogic.«Datatype.aEq»
                    (_root_.GebMirror.Metalogic.«Datatype.sx2» _root_.GebMirror.Metalogic.«Datatype.aLabel» x0)
                    (_root_.GebMirror.Metalogic.«Datatype.numAtom»
                      (_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 1))))
                  (_root_.GebMirror.Metalogic.«Prelude.get» x8)
                  ((x5).2).2
              else
                _root_.GebMirror.Metalogic.«Prelude.get» x8))
        else
          (_root_.Geb.Kernel.leaf 0,
            (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0)))
      (if (_root_.GebMirror.Metalogic.«Prelude.isSome» x2).label ≠ 0 then
        (_root_.Geb.Kernel.leaf 1,
          (_root_.Geb.Kernel.leaf 1, _root_.GebMirror.Metalogic.«Prelude.get» x2))
      else
        (_root_.Geb.Kernel.leaf 1,
          (_root_.Geb.Kernel.leaf 0, _root_.Geb.Kernel.leaf 0)))
      x1;
    if (_root_.GebMirror.Metalogic.«Prelude.and» (x4).1 ((x4).2).1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some» ((x4).2).2
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.clauseChain» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Prelude.isSome» x3)
      (_root_.GebMirror.Metalogic.«Reader.nonEmpty» x2)).label ≠ 0 then
      let x6 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
        (_root_.GebMirror.Metalogic.«Prelude.get» x3);
      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x2;
      let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
        x2
        (_root_.Geb.Kernel.Const.sub x7 (_root_.Geb.Kernel.leaf 1));
      let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Reader.isList» x8)
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.arity x8)
            (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Reader.named»
            (_root_.Geb.Kernel.Const.child x8 (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Datatype.kwElse»));
      let x10 : _root_.List
        _root_.Geb.Kernel.Tree := (if (x9).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Datatype.dropLast» x2
      else
        x2);
      let x11 : _root_.List
        _root_.Geb.Kernel.Tree := (if (x9).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Datatype.dropLast» x6
      else
        x6);
      let x12 : _root_.Geb.Kernel.Tree := (if (x9).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.Geb.Kernel.Const.child
            (_root_.GebMirror.Metalogic.«Prelude.at»
              x6
              (_root_.Geb.Kernel.Const.sub x7 (_root_.Geb.Kernel.leaf 1)))
            (_root_.Geb.Kernel.leaf 1))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
      let x13 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x13 : _root_.Geb.Kernel.Tree)
           (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((_root_.GebMirror.Metalogic.«Datatype.clauseCtor» x0 x13) :: x14))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x10;
      let x14 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
        x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.get» x1
      else
        if (_root_.GebMirror.Metalogic.«Reader.nonEmpty» x13).label ≠ 0 then
          if (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Prelude.at»
              x13
              (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
            _root_.Geb.Kernel.Const.child
              (_root_.GebMirror.Metalogic.«Prelude.get»
                (_root_.GebMirror.Metalogic.«Prelude.at» x13 (_root_.Geb.Kernel.leaf 0)))
              (_root_.Geb.Kernel.leaf 2)
          else
            _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 0);
      let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.allTrue»
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x15 : _root_.Geb.Kernel.Tree)
             (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
            ((_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.arity x15)
                (_root_.Geb.Kernel.leaf 2))
              (let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.clauseCtor»
                 x0
                 x15;
               _root_.GebMirror.Metalogic.«Prelude.and»
                 (_root_.GebMirror.Metalogic.«Prelude.isSome» x17)
                 (_root_.Geb.Kernel.Const.equal
                   (_root_.Geb.Kernel.Const.child
                     (_root_.GebMirror.Metalogic.«Prelude.get» x17)
                     (_root_.Geb.Kernel.leaf 2))
                   x14))) ::
              x16))
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x10);
      let x16 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x16 : _root_.Geb.Kernel.Tree)
           (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((_root_.Geb.Kernel.Const.child
            (_root_.GebMirror.Metalogic.«Prelude.get» x16)
            (_root_.Geb.Kernel.leaf 0)) ::
            x17))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x13;
      let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.or»
        x9
        (_root_.GebMirror.Metalogic.«Datatype.allTrue»
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            (fun (x17 : _root_.Geb.Kernel.Tree)
               (x18 : _root_.List _root_.Geb.Kernel.Tree) =>
              ((_root_.GebMirror.Metalogic.«Prelude.isSome»
                (_root_.GebMirror.Metalogic.«Reader.indexOf»
                  (_root_.Geb.Kernel.Const.child x17 (_root_.Geb.Kernel.leaf 0))
                  x16)) ::
                x18))
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Datatype.ctorsOf» x14 x0)));
      if (_root_.GebMirror.Metalogic.«Prelude.and» x15 x17).label ≠ 0 then
        let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
          x10;
        _root_.GebMirror.Metalogic.«Datatype.testChain»
          x4
          (_root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
            (fun (x19 : _root_.Geb.Kernel.Tree)
               (x20 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
              let x21 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x18 (_root_.Geb.Kernel.leaf 1))
                (x20).1;
              (_root_.Geb.Kernel.Const.add (x20).1 (_root_.Geb.Kernel.leaf 1),
                ((_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  (x19 ::
                    ((_root_.GebMirror.Metalogic.«Prelude.get»
                      (_root_.GebMirror.Metalogic.«Prelude.at» x13 x21)) ::
                      (_root_.GebMirror.Metalogic.«Prelude.single»
                        (_root_.GebMirror.Metalogic.«Prelude.at» x11 x21))))) ::
                  (x20).2)))
            (_root_.Geb.Kernel.leaf 0, ([] : _root_.List _root_.Geb.Kernel.Tree))
            x10).2
          x12
          x5
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.fieldLet» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Reader.named»
      x0
      (_root_.Geb.Kernel.mk 0 [_root_.Geb.Kernel.leaf 95])).label ≠ 0 then
      x3
    else
      _root_.GebMirror.Metalogic.«Datatype.sLet» x0 x1 x2 x3

def «Datatype.caseField» :=
  fun (_ : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.fieldLet»
      x1
      _root_.GebMirror.Metalogic.«Datatype.aT»
      (_root_.GebMirror.Metalogic.«Datatype.sHeadOf» _root_.GebMirror.Metalogic.«Datatype.aC»)
      (_root_.GebMirror.Metalogic.«Datatype.sLet»
        _root_.GebMirror.Metalogic.«Datatype.aC»
        (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
        (_root_.GebMirror.Metalogic.«Datatype.sTailOf» _root_.GebMirror.Metalogic.«Datatype.aC»)
        x2)

def «Datatype.caseRest» :=
  fun (_ : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.fieldLet»
      x1
      (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
      _root_.GebMirror.Metalogic.«Datatype.aC»
      x2

def «Datatype.caseStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sLet»
      _root_.GebMirror.Metalogic.«Datatype.aC»
      (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
      (_root_.GebMirror.Metalogic.«Datatype.sx2»
        _root_.GebMirror.Metalogic.«Datatype.aChildren»
        _root_.GebMirror.Metalogic.«Datatype.aS»)
      x0

def «Datatype.expandCase» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rrAt»
      x2
      (_root_.Geb.Kernel.leaf 1)
      x0;
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.clauseChain»
      x0
      _root_.GebMirror.Metalogic.«Prelude.none»
      (_root_.GebMirror.Metalogic.«Prelude.drop»
        (_root_.Geb.Kernel.leaf 2)
        (_root_.Geb.Kernel.Const.children x1))
      (_root_.GebMirror.Metalogic.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 2) x0)
      _root_.GebMirror.Metalogic.«Datatype.aS»
      (_root_.GebMirror.Metalogic.«Datatype.bindWith»
        _root_.GebMirror.Metalogic.«Datatype.caseField»
        _root_.GebMirror.Metalogic.«Datatype.caseRest»
        _root_.GebMirror.Metalogic.«Datatype.caseStart»);
    if (_root_.GebMirror.Metalogic.«Reader.both» x3 x4).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Datatype.sLet»
          _root_.GebMirror.Metalogic.«Datatype.aS»
          _root_.GebMirror.Metalogic.«Datatype.aT»
          (_root_.GebMirror.Metalogic.«Prelude.get» x3)
          (_root_.GebMirror.Metalogic.«Prelude.get» x4))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.thTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sArrow» _root_.GebMirror.Metalogic.«Datatype.aUnit» x0

def «Datatype.splitTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sProd»
      (_root_.GebMirror.Metalogic.«Datatype.thTy» x0)
      (_root_.GebMirror.Metalogic.«Datatype.sList» (_root_.GebMirror.Metalogic.«Datatype.thTy» x0))

def «Datatype.cataField» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sLet»
      _root_.GebMirror.Metalogic.«Datatype.aQ»
      (_root_.GebMirror.Metalogic.«Datatype.splitTy» x1)
      (_root_.GebMirror.Metalogic.«Datatype.sx6»
        _root_.GebMirror.Metalogic.«Datatype.aLcase»
        (_root_.GebMirror.Metalogic.«Datatype.thTy» x1)
        (_root_.GebMirror.Metalogic.«Datatype.splitTy» x1)
        (_root_.GebMirror.Metalogic.«Datatype.sx2»
          _root_.GebMirror.Metalogic.«Datatype.aSnd»
          _root_.GebMirror.Metalogic.«Datatype.aQ»)
        (_root_.GebMirror.Metalogic.«Datatype.sx3»
          _root_.GebMirror.Metalogic.«Datatype.aPair»
          (_root_.GebMirror.Metalogic.«Datatype.sLam1»
            _root_.GebMirror.Metalogic.«Datatype.aU»
            _root_.GebMirror.Metalogic.«Datatype.aUnit»
            x2)
          (_root_.GebMirror.Metalogic.«Datatype.sx2»
            _root_.GebMirror.Metalogic.«Datatype.aNil»
            (_root_.GebMirror.Metalogic.«Datatype.thTy» x1)))
        (_root_.GebMirror.Metalogic.«Datatype.sLam2»
          _root_.GebMirror.Metalogic.«Datatype.aH»
          (_root_.GebMirror.Metalogic.«Datatype.thTy» x1)
          _root_.GebMirror.Metalogic.«Datatype.aTl»
          (_root_.GebMirror.Metalogic.«Datatype.sList» (_root_.GebMirror.Metalogic.«Datatype.thTy» x1))
          (_root_.GebMirror.Metalogic.«Datatype.sx3»
            _root_.GebMirror.Metalogic.«Datatype.aPair»
            _root_.GebMirror.Metalogic.«Datatype.aH»
            _root_.GebMirror.Metalogic.«Datatype.aTl»)))
      (if (_root_.GebMirror.Metalogic.«Reader.named» x3 x0).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Datatype.fieldLet»
          x4
          x1
          (_root_.GebMirror.Metalogic.«Datatype.sx2»
            (_root_.GebMirror.Metalogic.«Datatype.sx2»
              _root_.GebMirror.Metalogic.«Datatype.aFst»
              _root_.GebMirror.Metalogic.«Datatype.aQ»)
            _root_.GebMirror.Metalogic.«Datatype.aUnitV»)
          (_root_.GebMirror.Metalogic.«Datatype.sLet»
            _root_.GebMirror.Metalogic.«Datatype.aC»
            (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
            (_root_.GebMirror.Metalogic.«Datatype.sTailOf» _root_.GebMirror.Metalogic.«Datatype.aC»)
            x5)
      else
        _root_.GebMirror.Metalogic.«Datatype.fieldLet»
          x4
          _root_.GebMirror.Metalogic.«Datatype.aT»
          (_root_.GebMirror.Metalogic.«Datatype.sHeadOf» _root_.GebMirror.Metalogic.«Datatype.aC»)
          (_root_.GebMirror.Metalogic.«Datatype.sLet»
            _root_.GebMirror.Metalogic.«Datatype.aC»
            (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
            (_root_.GebMirror.Metalogic.«Datatype.sTailOf» _root_.GebMirror.Metalogic.«Datatype.aC»)
            x5))

def «Datatype.cataRest» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Reader.named» x2 x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Datatype.fieldLet»
        x3
        (_root_.GebMirror.Metalogic.«Datatype.sList» x1)
        (_root_.GebMirror.Metalogic.«Datatype.sx6»
          _root_.GebMirror.Metalogic.«Datatype.aFoldr»
          (_root_.GebMirror.Metalogic.«Datatype.thTy» x1)
          (_root_.GebMirror.Metalogic.«Datatype.sList» x1)
          (_root_.GebMirror.Metalogic.«Datatype.sLam2»
            _root_.GebMirror.Metalogic.«Datatype.aH»
            (_root_.GebMirror.Metalogic.«Datatype.thTy» x1)
            _root_.GebMirror.Metalogic.«Datatype.aA»
            (_root_.GebMirror.Metalogic.«Datatype.sList» x1)
            (_root_.GebMirror.Metalogic.«Datatype.sx3»
              _root_.GebMirror.Metalogic.«Datatype.aCons»
              (_root_.GebMirror.Metalogic.«Datatype.sx2»
                _root_.GebMirror.Metalogic.«Datatype.aH»
                _root_.GebMirror.Metalogic.«Datatype.aUnitV»)
              _root_.GebMirror.Metalogic.«Datatype.aA»))
          (_root_.GebMirror.Metalogic.«Datatype.sx2» _root_.GebMirror.Metalogic.«Datatype.aNil» x1)
          (_root_.GebMirror.Metalogic.«Datatype.sx2»
            _root_.GebMirror.Metalogic.«Datatype.aSnd»
            _root_.GebMirror.Metalogic.«Datatype.aQ»))
        x4
    else
      _root_.GebMirror.Metalogic.«Datatype.fieldLet»
        x3
        (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
        _root_.GebMirror.Metalogic.«Datatype.aC»
        x4

def «Datatype.cataStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Datatype.sLet»
      _root_.GebMirror.Metalogic.«Datatype.aQ»
      (_root_.GebMirror.Metalogic.«Datatype.splitTy» x0)
      (_root_.GebMirror.Metalogic.«Datatype.sx3»
        _root_.GebMirror.Metalogic.«Datatype.aPair»
        (_root_.GebMirror.Metalogic.«Datatype.sLam1»
          _root_.GebMirror.Metalogic.«Datatype.aU»
          _root_.GebMirror.Metalogic.«Datatype.aUnit»
          x1)
        _root_.GebMirror.Metalogic.«Datatype.aK»)
      (_root_.GebMirror.Metalogic.«Datatype.sLet»
        _root_.GebMirror.Metalogic.«Datatype.aC»
        (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)
        (_root_.GebMirror.Metalogic.«Datatype.sx2»
          _root_.GebMirror.Metalogic.«Datatype.aChildren»
          _root_.GebMirror.Metalogic.«Datatype.aO»)
        x2)

def «Datatype.expandCata» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.nameOf»
      (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 1));
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
      x3
      (_root_.Geb.Kernel.leaf 2);
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.defaultOf»
      (_root_.GebMirror.Metalogic.«Datatype.expandAliases» x0 x5);
    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rrAt»
      x2
      (_root_.Geb.Kernel.leaf 3)
      x0;
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Reader.isAtom»
        (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Datatype.isData» x4 x0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Datatype.clauseChain»
        x0
        (_root_.GebMirror.Metalogic.«Prelude.some» x4)
        (_root_.GebMirror.Metalogic.«Prelude.drop» (_root_.Geb.Kernel.leaf 4) x3)
        (_root_.GebMirror.Metalogic.«Reader.argsOf» x2 (_root_.Geb.Kernel.leaf 4) x0)
        _root_.GebMirror.Metalogic.«Datatype.aO»
        (_root_.GebMirror.Metalogic.«Datatype.bindWith»
          (_root_.GebMirror.Metalogic.«Datatype.cataField» x4 x5 x6)
          (_root_.GebMirror.Metalogic.«Datatype.cataRest» x4 x5)
          (_root_.GebMirror.Metalogic.«Datatype.cataStart» x5 x6))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    if (_root_.GebMirror.Metalogic.«Reader.both» x7 x8).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Datatype.sx2»
          (_root_.GebMirror.Metalogic.«Datatype.sx4»
            _root_.GebMirror.Metalogic.«Datatype.aPara»
            (_root_.GebMirror.Metalogic.«Datatype.thTy» x5)
            (_root_.GebMirror.Metalogic.«Datatype.sLam2»
              _root_.GebMirror.Metalogic.«Datatype.aO»
              _root_.GebMirror.Metalogic.«Datatype.aT»
              _root_.GebMirror.Metalogic.«Datatype.aK»
              (_root_.GebMirror.Metalogic.«Datatype.sList» (_root_.GebMirror.Metalogic.«Datatype.thTy» x5))
              (_root_.GebMirror.Metalogic.«Datatype.sLam1»
                _root_.GebMirror.Metalogic.«Datatype.aU»
                _root_.GebMirror.Metalogic.«Datatype.aUnit»
                (_root_.GebMirror.Metalogic.«Prelude.get» x8)))
            (_root_.GebMirror.Metalogic.«Prelude.get» x7))
          _root_.GebMirror.Metalogic.«Datatype.aUnitV»)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.expandDecode» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
      (_root_.Geb.Kernel.Const.children x1)
      (_root_.Geb.Kernel.leaf 1);
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rrAt»
      x2
      (_root_.Geb.Kernel.leaf 2)
      x0;
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rrAt»
      x2
      (_root_.Geb.Kernel.leaf 3)
      x0;
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.rrAt»
      x2
      (_root_.Geb.Kernel.leaf 4)
      x0;
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Reader.isAtom» x3)
      (_root_.GebMirror.Metalogic.«Reader.both»
        x4
        (_root_.GebMirror.Metalogic.«Reader.both» x5 x6))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Datatype.sLet»
          _root_.GebMirror.Metalogic.«Datatype.aE»
          _root_.GebMirror.Metalogic.«Datatype.aT»
          (_root_.GebMirror.Metalogic.«Prelude.get» x4)
          (_root_.GebMirror.Metalogic.«Datatype.sIf»
            (_root_.GebMirror.Metalogic.«Datatype.sx2»
              (_root_.GebMirror.Metalogic.«Datatype.memberName» x3)
              _root_.GebMirror.Metalogic.«Datatype.aE»)
            (_root_.GebMirror.Metalogic.«Datatype.sx2»
              (_root_.GebMirror.Metalogic.«Prelude.get» x5)
              _root_.GebMirror.Metalogic.«Datatype.aE»)
            (_root_.GebMirror.Metalogic.«Prelude.get» x6)))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.expandExpr» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          x2
          (_root_.GebMirror.Metalogic.«Reader.rrTrees» x3);
        (x4,
          fun (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.Metalogic.«Reader.isList» x4).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                (_root_.Geb.Kernel.Const.children x4)
                (_root_.Geb.Kernel.leaf 0);
              let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x4;
              if (_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.GebMirror.Metalogic.«Reader.named» x6 _root_.GebMirror.Metalogic.«Datatype.kwCase»)
                (_root_.Geb.Kernel.Const.lt
                  (_root_.Geb.Kernel.leaf 2)
                  x7)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Datatype.expandCase» x5 x4 x3
              else
                if (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.GebMirror.Metalogic.«Reader.named» x6 _root_.GebMirror.Metalogic.«Datatype.kwCata»)
                  (_root_.Geb.Kernel.Const.lt
                    (_root_.Geb.Kernel.leaf 4)
                    x7)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Datatype.expandCata» x5 x4 x3
                else
                  if (_root_.GebMirror.Metalogic.«Prelude.and»
                    (_root_.GebMirror.Metalogic.«Reader.named» x6 _root_.GebMirror.Metalogic.«Datatype.kwRep»)
                    (_root_.Geb.Kernel.Const.eq
                      x7
                      (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«Reader.rrAt» x3 (_root_.Geb.Kernel.leaf 1) x5
                  else
                    if (_root_.GebMirror.Metalogic.«Prelude.and»
                      (_root_.GebMirror.Metalogic.«Reader.named» x6 _root_.GebMirror.Metalogic.«Datatype.kwDecode»)
                      (_root_.Geb.Kernel.Const.eq
                        x7
                        (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«Datatype.expandDecode» x5 x4 x3
                    else
                      if (_root_.GebMirror.Metalogic.«Prelude.and»
                        (_root_.GebMirror.Metalogic.«Reader.named» x6 _root_.GebMirror.Metalogic.«Datatype.kwDatum»)
                        (_root_.Geb.Kernel.Const.eq
                          x7
                          (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                        _root_.GebMirror.Metalogic.«Prelude.some»
                          (_root_.GebMirror.Metalogic.«Datatype.sx2»
                            _root_.GebMirror.Metalogic.«Datatype.aQuote»
                            (_root_.GebMirror.Metalogic.«Prelude.at»
                              (_root_.Geb.Kernel.Const.children x4)
                              (_root_.Geb.Kernel.leaf 2)))
                      else
                        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.allSome»
                          (_root_.GebMirror.Metalogic.«Reader.rrApply» x3 x5);
                        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x8).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Prelude.some»
                            (_root_.Geb.Kernel.Const.node
                              (_root_.Geb.Kernel.leaf 2)
                              (_root_.Geb.Kernel.Const.children (_root_.GebMirror.Metalogic.«Prelude.get» x8)))
                        else
                          _root_.GebMirror.Metalogic.«Prelude.none»
            else
              _root_.GebMirror.Metalogic.«Prelude.some» x4))
      x1).2
      x0

def «Datatype.ctorDecl» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.tail» x3;
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x4;
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x5)
      (_root_.GebMirror.Metalogic.«Reader.named»
        (_root_.GebMirror.Metalogic.«Prelude.at»
          x4
          (_root_.Geb.Kernel.Const.sub x5 (_root_.Geb.Kernel.leaf 2)))
        _root_.GebMirror.Metalogic.«Datatype.kwAmp»);
    let x7 : _root_.List
      _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Datatype.dropLast»
        (_root_.GebMirror.Metalogic.«Datatype.dropLast» x4)
    else
      x4);
    let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x7;
    let x9 : _root_.List
      _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x10 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        (_root_.Geb.Kernel.Const.add (x10).1 (_root_.Geb.Kernel.leaf 1),
          ((_root_.GebMirror.Metalogic.«Datatype.sx2»
            (_root_.GebMirror.Metalogic.«Datatype.fieldAtom»
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x8 (_root_.Geb.Kernel.leaf 1))
                (x10).1))
            _root_.GebMirror.Metalogic.«Datatype.aT») ::
            (x10).2)))
      (_root_.Geb.Kernel.leaf 0, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x7).2;
    let x10 : _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Datatype.aRest»
    else
      _root_.GebMirror.Metalogic.«Datatype.sx2»
        _root_.GebMirror.Metalogic.«Datatype.aNil»
        _root_.GebMirror.Metalogic.«Datatype.aT»);
    let x11 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x12 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
        (_root_.Geb.Kernel.Const.add (x12).1 (_root_.Geb.Kernel.leaf 1),
          _root_.GebMirror.Metalogic.«Datatype.sx3»
            _root_.GebMirror.Metalogic.«Datatype.aCons»
            (_root_.GebMirror.Metalogic.«Datatype.fieldAtom»
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x8 (_root_.Geb.Kernel.leaf 1))
                (x12).1))
            (x12).2))
      (_root_.Geb.Kernel.leaf 0, x10)
      x7).2;
    let x12 : _root_.List
      _root_.Geb.Kernel.Tree := (if (x6).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.append»
        x9
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Datatype.sx2»
            _root_.GebMirror.Metalogic.«Datatype.aRest»
            (_root_.GebMirror.Metalogic.«Datatype.sList» _root_.GebMirror.Metalogic.«Datatype.aT»)))
    else
      x9);
    let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.sx3»
      _root_.GebMirror.Metalogic.«Datatype.aNode»
      (_root_.GebMirror.Metalogic.«Datatype.numAtom» x1)
      x11;
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Reader.isList» x2)
      (_root_.GebMirror.Metalogic.«Reader.isAtom»
        (_root_.GebMirror.Metalogic.«Prelude.at»
          x3
          (_root_.Geb.Kernel.leaf 0)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Reader.node2»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 5)
            ((_root_.GebMirror.Metalogic.«Reader.nameOf»
              (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))) ::
              (x1 ::
                (x0 ::
                  ((_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x7) ::
                    (x6 ::
                      (_root_.GebMirror.Metalogic.«Prelude.single»
                        (if (x6).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Prelude.at»
                            x4
                            (_root_.Geb.Kernel.Const.sub x5 (_root_.Geb.Kernel.leaf 1))
                        else
                          _root_.Geb.Kernel.leaf 0))))))))
          (_root_.GebMirror.Metalogic.«Datatype.sx3»
            _root_.GebMirror.Metalogic.«Datatype.aDef»
            (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))
            (if (_root_.GebMirror.Metalogic.«Reader.nonEmpty» x12).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Datatype.sx3»
                _root_.GebMirror.Metalogic.«Datatype.aLam»
                (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 2) x12)
                x13
            else
              x13)))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.dataDecl» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x0;
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.nameOf»
      (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1));
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.drop»
      (_root_.Geb.Kernel.leaf 2)
      x1;
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x3;
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.allSome»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
        (fun (x5 : _root_.Geb.Kernel.Tree)
           (x6 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
          (_root_.Geb.Kernel.Const.add (x6).1 (_root_.Geb.Kernel.leaf 1),
            ((_root_.GebMirror.Metalogic.«Datatype.ctorDecl»
              x2
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x4 (_root_.Geb.Kernel.leaf 1))
                (x6).1)
              x5) ::
              (x6).2)))
        (_root_.Geb.Kernel.leaf 0, ([] : _root_.List _root_.Geb.Kernel.Tree))
        x3).2;
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Reader.isAtom»
        (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Prelude.isSome» x5)).label ≠ 0 then
      let x6 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
        (_root_.GebMirror.Metalogic.«Prelude.get» x5);
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Reader.node2»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ((_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 6)
              (_root_.GebMirror.Metalogic.«Prelude.single» x2)) ::
              (_root_.Geb.Kernel.Const.foldr
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                (fun (x7 : _root_.Geb.Kernel.Tree)
                   (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                  ((_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 0)) :: x8))
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                x6)))
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ((_root_.GebMirror.Metalogic.«Datatype.sx3»
              _root_.GebMirror.Metalogic.«Datatype.aDeftype»
              (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1))
              _root_.GebMirror.Metalogic.«Datatype.aT») ::
              (_root_.Geb.Kernel.Const.foldr
                (α := _root_.Geb.Kernel.Tree)
                (β := _root_.List _root_.Geb.Kernel.Tree)
                (fun (x7 : _root_.Geb.Kernel.Tree)
                   (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                  ((_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 1)) :: x8))
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                x6))))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Datatype.marker» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 9)
      (x1 ::
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x3 : _root_.Geb.Kernel.Tree)
             (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x3)
              (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
              ((_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                ((_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 1)) ::
                  ((_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.Geb.Kernel.Const.foldr
                      (α := _root_.Geb.Kernel.Tree)
                      (β := _root_.List _root_.Geb.Kernel.Tree)
                      (fun (x5 : _root_.Geb.Kernel.Tree)
                         (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                        ((_root_.GebMirror.Metalogic.«Datatype.expandAliases» x0 x5) :: x6))
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.Geb.Kernel.Const.children
                        (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 3))))) ::
                    ((_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 4)) ::
                      (_root_.GebMirror.Metalogic.«Prelude.single»
                        (_root_.GebMirror.Metalogic.«Datatype.expandAliases»
                          x0
                          (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 5)))))))) ::
                x4)
            else
              x4)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x2))

def «Datatype.xpFail» :=
  (_root_.Geb.Kernel.leaf 0,
    (([] : _root_.List _root_.Geb.Kernel.Tree),
      ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Datatype.xpStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree ×
      (_root_.List _root_.Geb.Kernel.Tree ×
        _root_.List _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Prelude.and»
      (x0).1
      (_root_.GebMirror.Metalogic.«Reader.isList» x1)).label ≠ 0 then
      let x2 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).1;
      let x3 : _root_.List _root_.Geb.Kernel.Tree := ((x0).2).2;
      let x4 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
        x4
        (_root_.Geb.Kernel.leaf 0);
      let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity x1;
      if (_root_.GebMirror.Metalogic.«Reader.named»
        x5
        _root_.GebMirror.Metalogic.«Datatype.kwData»).label ≠ 0 then
        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.dataDecl»
          x1;
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x7).label ≠ 0 then
          let x8 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child
              (_root_.GebMirror.Metalogic.«Prelude.get» x7)
              (_root_.Geb.Kernel.leaf 0));
          (_root_.Geb.Kernel.leaf 1,
            (_root_.GebMirror.Metalogic.«Prelude.append» x2 x8,
              _root_.GebMirror.Metalogic.«Prelude.append»
                (_root_.GebMirror.Metalogic.«Prelude.reverse»
                  (_root_.GebMirror.Metalogic.«Prelude.append»
                    (_root_.Geb.Kernel.Const.children
                      (_root_.Geb.Kernel.Const.child
                        (_root_.GebMirror.Metalogic.«Prelude.get» x7)
                        (_root_.Geb.Kernel.leaf 1)))
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Datatype.marker»
                        x2
                        (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1))
                        x8))))
                x3))
        else
          _root_.GebMirror.Metalogic.«Datatype.xpFail»
      else
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Reader.named» x5 _root_.GebMirror.Metalogic.«Datatype.kwDefn»)
          (_root_.Geb.Kernel.Const.eq
            x6
            (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.expandExpr»
            x2
            (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 4));
          if (_root_.GebMirror.Metalogic.«Prelude.isSome» x7).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.sLet»
              _root_.GebMirror.Metalogic.«Datatype.aR»
              (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 3))
              (_root_.GebMirror.Metalogic.«Prelude.get» x7)
              _root_.GebMirror.Metalogic.«Datatype.aR»;
            (_root_.Geb.Kernel.leaf 1,
              (x2,
                ((_root_.GebMirror.Metalogic.«Datatype.sx3»
                  _root_.GebMirror.Metalogic.«Datatype.aDef»
                  (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1))
                  (if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.arity
                      (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2)))
                    (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                    x8
                  else
                    _root_.GebMirror.Metalogic.«Datatype.sx3»
                      _root_.GebMirror.Metalogic.«Datatype.aLam»
                      (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2))
                      x8)) ::
                  x3)))
          else
            _root_.GebMirror.Metalogic.«Datatype.xpFail»
        else
          if (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.GebMirror.Metalogic.«Reader.named» x5 _root_.GebMirror.Metalogic.«Reader.kwDef»)
            (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Datatype.expandExpr»
              x2
              (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2));
            if (_root_.GebMirror.Metalogic.«Prelude.isSome» x7).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (x2,
                  ((_root_.GebMirror.Metalogic.«Datatype.sx3»
                    _root_.GebMirror.Metalogic.«Datatype.aDef»
                    (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1))
                    (_root_.GebMirror.Metalogic.«Prelude.get» x7)) ::
                    x3)))
            else
              _root_.GebMirror.Metalogic.«Datatype.xpFail»
          else
            if (_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.GebMirror.Metalogic.«Reader.named» x5 _root_.GebMirror.Metalogic.«Reader.kwDeftype»)
              (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
              (_root_.Geb.Kernel.leaf 1,
                (_root_.GebMirror.Metalogic.«Prelude.append»
                  x2
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.GebMirror.Metalogic.«Reader.node2»
                      (_root_.Geb.Kernel.leaf 7)
                      (_root_.GebMirror.Metalogic.«Reader.nameOf»
                        (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 1)))
                      (_root_.GebMirror.Metalogic.«Datatype.expandAliases»
                        x2
                        (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 2))))),
                  (x1 :: x3)))
            else
              if (_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.GebMirror.Metalogic.«Reader.named» x5 _root_.GebMirror.Metalogic.«Reader.kwDefnum»)
                (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                (_root_.Geb.Kernel.leaf 1, (x2, (x1 :: x3)))
              else
                if (_root_.GebMirror.Metalogic.«Reader.named»
                  x5
                  _root_.GebMirror.Metalogic.«Datatype.kwGeneric»).label ≠ 0 then
                  (_root_.Geb.Kernel.leaf 1, (x2, x3))
                else
                  _root_.GebMirror.Metalogic.«Datatype.xpFail»
    else
      _root_.GebMirror.Metalogic.«Datatype.xpFail»

def «Datatype.expandProgram» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
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
        x2 (_root_.GebMirror.Metalogic.«Datatype.xpStep» x3 x1))
      (fun (x1 : _root_.Geb.Kernel.Tree ×
           (_root_.List _root_.Geb.Kernel.Tree ×
             _root_.List _root_.Geb.Kernel.Tree)) =>
        x1)
      x0
      (_root_.Geb.Kernel.leaf 1,
        (([] : _root_.List _root_.Geb.Kernel.Tree),
          ([] : _root_.List _root_.Geb.Kernel.Tree)));
    if ((x1).1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Metalogic.«Prelude.reverse» ((x1).2).2))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»

def «Printer.atomOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.Const.children x0)

def «Printer.listOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 2) x0

def «Printer.numAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Datatype.decimalChars» x0)

def «Printer.binderAtom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      ((_root_.Geb.Kernel.leaf 95) ::
        (_root_.GebMirror.Metalogic.«Datatype.decimalChars» x0))

def «Printer.nameAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Printer.atomOf» (_root_.GebMirror.Metalogic.«Prelude.at» x0 x1)

def «Printer.printType» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwT»
        else
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwUnit»
          else
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Printer.listOf»
                ((_root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwProd») ::
                  x2)
            else
              if (_root_.Geb.Kernel.Const.eq
                x1
                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Printer.listOf»
                  ((_root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwArrow») ::
                    x2)
              else
                _root_.GebMirror.Metalogic.«Printer.listOf»
                  ((_root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwList») ::
                    x2))
      x0

def «Printer.printTypes» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((_root_.GebMirror.Metalogic.«Printer.printType» x1) :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0

def «Printer.printDatum» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Reader.nonEmpty» x2).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Printer.listOf»
            ((_root_.GebMirror.Metalogic.«Printer.numAtom» x1) :: x2)
        else
          _root_.GebMirror.Metalogic.«Printer.numAtom» x1)
      x0

def «Printer.kwList1» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Printer.listOf»
      ((_root_.GebMirror.Metalogic.«Printer.atomOf» x0) :: x1)

def «Printer.printStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x1;
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
    let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
      (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0));
    if (_root_.Geb.Kernel.Const.eq
      x4
      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Printer.binderAtom»
        (_root_.Geb.Kernel.Const.sub
          (_root_.Geb.Kernel.Const.sub x3 (_root_.Geb.Kernel.leaf 1))
          x6)
    else
      if (_root_.Geb.Kernel.Const.eq
        x4
        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Printer.kwList1»
          _root_.GebMirror.Metalogic.«Reader.kwLam»
          ((_root_.GebMirror.Metalogic.«Printer.listOf»
            ((_root_.GebMirror.Metalogic.«Printer.binderAtom» x3) ::
              (_root_.GebMirror.Metalogic.«Prelude.single»
                (_root_.GebMirror.Metalogic.«Printer.printType»
                  (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))))) ::
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1))))
      else
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Printer.listOf» x2
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Printer.atomOf» _root_.GebMirror.Metalogic.«Reader.kwUnitValue»
          else
            if (_root_.Geb.Kernel.Const.eq
              x4
              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Printer.kwList1» _root_.GebMirror.Metalogic.«Reader.kwPair» x2
            else
              if (_root_.Geb.Kernel.Const.eq
                x4
                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Printer.kwList1» _root_.GebMirror.Metalogic.«Reader.kwFst» x2
              else
                if (_root_.Geb.Kernel.Const.eq
                  x4
                  (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Printer.kwList1» _root_.GebMirror.Metalogic.«Reader.kwSnd» x2
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x4
                    (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«Printer.kwList1» _root_.GebMirror.Metalogic.«Reader.kwIf» x2
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x4
                      (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«Printer.kwList1» _root_.GebMirror.Metalogic.«Reader.kwCons» x2
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x4
                        (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                          x5
                          (_root_.Geb.Kernel.leaf 0);
                        if (_root_.GebMirror.Metalogic.«Reader.nonEmpty»
                          (_root_.Geb.Kernel.Const.children x7)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Printer.kwList1»
                            _root_.GebMirror.Metalogic.«Reader.kwQuote»
                            (_root_.GebMirror.Metalogic.«Prelude.single»
                              (_root_.GebMirror.Metalogic.«Printer.printDatum» x7))
                        else
                          _root_.GebMirror.Metalogic.«Printer.numAtom» (_root_.Geb.Kernel.Const.label x7)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x4
                          (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Printer.kwList1»
                            _root_.GebMirror.Metalogic.«Reader.kwNil»
                            (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x4
                            (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                            _root_.GebMirror.Metalogic.«Printer.kwList1»
                              _root_.GebMirror.Metalogic.«Reader.kwFold»
                              (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x4
                              (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«Printer.kwList1»
                                _root_.GebMirror.Metalogic.«Reader.kwPara»
                                (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x4
                                (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                                _root_.GebMirror.Metalogic.«Printer.kwList1»
                                  _root_.GebMirror.Metalogic.«Reader.kwIter»
                                  (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                              else
                                if (_root_.Geb.Kernel.Const.eq
                                  x4
                                  (_root_.Geb.Kernel.leaf 21)).label ≠ 0 then
                                  _root_.GebMirror.Metalogic.«Printer.kwList1»
                                    _root_.GebMirror.Metalogic.«Reader.kwFoldr»
                                    (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                                else
                                  if (_root_.Geb.Kernel.Const.eq
                                    x4
                                    (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                                    _root_.GebMirror.Metalogic.«Printer.kwList1»
                                      _root_.GebMirror.Metalogic.«Reader.kwLcase»
                                      (_root_.GebMirror.Metalogic.«Printer.printTypes» x5)
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x4
                                      (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                      _root_.GebMirror.Metalogic.«Printer.nameAt»
                                        _root_.GebMirror.Metalogic.«Reader.primNames»
                                        x6
                                    else
                                      _root_.GebMirror.Metalogic.«Printer.nameAt» x0 x6

def «Printer.printTerm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x3;
        let x6 : _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
          (fun (x6 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
             (x7 : _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
             (x8 : _root_.Geb.Kernel.Tree)
             (x9 : _root_.Geb.Kernel.Tree) =>
            ((x6
              (if (_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 9))
                (_root_.Geb.Kernel.Const.eq
                  x9
                  (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                _root_.Geb.Kernel.Const.add x8 (_root_.Geb.Kernel.leaf 1)
              else
                x8)) ::
              (x7 x8 (_root_.Geb.Kernel.Const.add x9 (_root_.Geb.Kernel.leaf 1)))))
          (fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          x4;
        fun (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Printer.printStep»
            x0
            x3
            (x6 x7 (_root_.Geb.Kernel.leaf 0))
            x7)
      x1
      x2;
    x3

def «Printer.readBack» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.resolve»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0
      x1
      x2;
    x3

def «Printer.leafBelow» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      (_root_.GebMirror.Metalogic.«Prelude.length» x0)
      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
      if (_root_.GebMirror.Metalogic.«Reader.nonEmpty»
        (_root_.Geb.Kernel.Const.children
          (_root_.GebMirror.Metalogic.«Prelude.at»
            x0
            (_root_.Geb.Kernel.leaf 0)))).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        _root_.Geb.Kernel.Const.lt
          (_root_.Geb.Kernel.Const.label
            (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 0)))
          x1
    else
      _root_.Geb.Kernel.leaf 0

def «Printer.allAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        if (x1).label ≠ 0 then x2 else _root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      x0

def «Printer.tysOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (_root_.Geb.Kernel.Const.eq
      (_root_.GebMirror.Metalogic.«Prelude.length» x1)
      x0).label ≠ 0 then
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«Check.isTy» x2).label ≠ 0 then
            x3
          else
            _root_.Geb.Kernel.leaf 0)
        (_root_.Geb.Kernel.leaf 1)
        x1
    else
      _root_.Geb.Kernel.leaf 0

def «Printer.wfStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x1;
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
    if (_root_.Geb.Kernel.Const.eq
      x4
      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Printer.leafBelow» x5 x3
    else
      if (_root_.Geb.Kernel.Const.eq
        x4
        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x5)
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          if (_root_.GebMirror.Metalogic.«Check.isTy»
            (_root_.GebMirror.Metalogic.«Prelude.at»
              x5
              (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)
          else
            _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 0
      else
        if (_root_.Geb.Kernel.Const.eq
          x4
          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length» x5)
            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Printer.allAt» x2
          else
            _root_.Geb.Kernel.leaf 0
        else
          if (_root_.Geb.Kernel.Const.eq
            x4
            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
            if (_root_.GebMirror.Metalogic.«Reader.nonEmpty» x5).label ≠ 0 then
              _root_.Geb.Kernel.leaf 0
            else
              _root_.Geb.Kernel.leaf 1
          else
            if (_root_.Geb.Kernel.Const.eq
              x4
              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Printer.allAt» x2
            else
              if (_root_.Geb.Kernel.Const.eq
                x4
                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Printer.allAt» x2
              else
                if (_root_.Geb.Kernel.Const.eq
                  x4
                  (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Printer.allAt» x2
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x4
                    (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«Printer.allAt» x2
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x4
                      (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«Printer.allAt» x2
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x4
                        (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                        _root_.Geb.Kernel.Const.eq
                          (_root_.GebMirror.Metalogic.«Prelude.length» x5)
                          (_root_.Geb.Kernel.leaf 1)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x4
                          (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 1) x5
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x4
                            (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                            _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 1) x5
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x4
                              (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 1) x5
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x4
                                (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                                _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 1) x5
                              else
                                if (_root_.Geb.Kernel.Const.eq
                                  x4
                                  (_root_.Geb.Kernel.leaf 21)).label ≠ 0 then
                                  _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 2) x5
                                else
                                  if (_root_.Geb.Kernel.Const.eq
                                    x4
                                    (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                                    _root_.GebMirror.Metalogic.«Printer.tysOf» (_root_.Geb.Kernel.leaf 2) x5
                                  else
                                    if (_root_.Geb.Kernel.Const.eq
                                      x4
                                      (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                      _root_.GebMirror.Metalogic.«Printer.leafBelow»
                                        x5
                                        (_root_.GebMirror.Metalogic.«Prelude.length»
                                          _root_.GebMirror.Metalogic.«Reader.primNames»)
                                    else
                                      if (_root_.Geb.Kernel.Const.eq
                                        x4
                                        (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
                                        _root_.GebMirror.Metalogic.«Printer.leafBelow» x5 x0
                                      else
                                        _root_.Geb.Kernel.leaf 0

def «Printer.termWf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x3;
        let x6 : _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
          (fun (x6 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
             (x7 : _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
             (x8 : _root_.Geb.Kernel.Tree)
             (x9 : _root_.Geb.Kernel.Tree) =>
            ((if (_root_.Geb.Kernel.Const.eq
              x5
              (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
              if (_root_.Geb.Kernel.Const.eq
                x9
                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                x6 (_root_.Geb.Kernel.Const.add x8 (_root_.Geb.Kernel.leaf 1))
              else
                _root_.Geb.Kernel.leaf 0
            else
              if (_root_.GebMirror.Metalogic.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 10))
                (_root_.GebMirror.Metalogic.«Prelude.or»
                  (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 12))
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 13))
                    (_root_.GebMirror.Metalogic.«Prelude.or»
                      (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 14))
                      (_root_.GebMirror.Metalogic.«Prelude.or»
                        (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 16))
                        (_root_.Geb.Kernel.Const.eq
                          x5
                          (_root_.Geb.Kernel.leaf 20))))))).label ≠ 0 then
                x6 x8
              else
                _root_.Geb.Kernel.leaf 0) ::
              (x7 x8 (_root_.Geb.Kernel.Const.add x9 (_root_.Geb.Kernel.leaf 1)))))
          (fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          x4;
        fun (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Printer.wfStep»
            x0
            x3
            (x6 x7 (_root_.Geb.Kernel.leaf 0))
            x7)
      x1
      x2

def «Printer.isBinderName» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Reader.numeral»
      (_root_.GebMirror.Metalogic.«Prelude.tail» (_root_.Geb.Kernel.Const.children x0));
    if (_root_.GebMirror.Metalogic.«Prelude.isSome» x1).label ≠ 0 then
      _root_.Geb.Kernel.Const.equal
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          ((_root_.Geb.Kernel.leaf 95) ::
            (_root_.GebMirror.Metalogic.«Datatype.decimalChars»
              (_root_.GebMirror.Metalogic.«Prelude.get» x1))))
        x0
    else
      _root_.Geb.Kernel.leaf 0

def «Printer.nameOk» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      (_root_.GebMirror.Metalogic.«Reader.numeral»
        (_root_.Geb.Kernel.Const.children x0))).label ≠ 0 then
      _root_.Geb.Kernel.leaf 0
    else
      if (_root_.GebMirror.Metalogic.«Printer.isBinderName» x0).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        if (_root_.GebMirror.Metalogic.«Prelude.isSome»
          (_root_.GebMirror.Metalogic.«Reader.indexOf»
            x0
            _root_.GebMirror.Metalogic.«Reader.reservedNames»)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 0
        else
          _root_.Geb.Kernel.leaf 1

def «Printer.distinct» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        (if ((x2).1).label ≠ 0 then
          if (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Reader.indexOf» x1 (x2).2)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 0
          else
            _root_.Geb.Kernel.leaf 1
        else
          _root_.Geb.Kernel.leaf 0,
          (x1 :: (x2).2)))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0).1

def «Printer.namesOk» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    if (_root_.GebMirror.Metalogic.«Printer.distinct» x0).label ≠ 0 then
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«Printer.nameOk» x1).label ≠ 0 then
            x2
          else
            _root_.Geb.Kernel.leaf 0)
        (_root_.Geb.Kernel.leaf 1)
        x0
    else
      _root_.Geb.Kernel.leaf 0

def «Printer.printTermOpt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Printer.namesOk»
      x0).label ≠ 0 then
      if (_root_.GebMirror.Metalogic.«Printer.termWf»
        (_root_.GebMirror.Metalogic.«Prelude.length» x0)
        x1
        x2).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Printer.printTerm» x0 x1 x2)
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x3

def «Printer.printProgram» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
      (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1));
    _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
          x1
          (_root_.GebMirror.Metalogic.«Prelude.length» x4);
        if (_root_.GebMirror.Metalogic.«Printer.nameOk» x5).label ≠ 0 then
          if (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Reader.indexOf» x5 x4)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.none»
          else
            if (_root_.GebMirror.Metalogic.«Printer.termWf»
              (_root_.GebMirror.Metalogic.«Prelude.length» x4)
              x2
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := x3
                (_root_.GebMirror.Metalogic.«Prelude.append»
                  x4
                  (_root_.GebMirror.Metalogic.«Prelude.single» x5));
              if (_root_.GebMirror.Metalogic.«Prelude.isSome» x6).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Prelude.some»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    ((_root_.GebMirror.Metalogic.«Printer.kwList1»
                      _root_.GebMirror.Metalogic.«Reader.kwDef»
                      ((_root_.GebMirror.Metalogic.«Printer.atomOf» x5) ::
                        (_root_.GebMirror.Metalogic.«Prelude.single»
                          (_root_.GebMirror.Metalogic.«Printer.printTerm»
                            x4
                            x2
                            (_root_.Geb.Kernel.leaf 0))))) ::
                      (_root_.Geb.Kernel.Const.children (_root_.GebMirror.Metalogic.«Prelude.get» x6))))
              else
                _root_.GebMirror.Metalogic.«Prelude.none»
            else
              _root_.GebMirror.Metalogic.«Prelude.none»
        else
          _root_.GebMirror.Metalogic.«Prelude.none»)
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree)))
      (_root_.Geb.Kernel.Const.children
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)))
      ([] : _root_.List _root_.Geb.Kernel.Tree)

end GebMirror.Metalogic

end
