module

public import GebMirror.Metalogic.Checker

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Translation.bitTy» :=
  _root_.GebMirror.Metalogic.«Theory.coprod»
    _root_.GebMirror.Metalogic.«Theory.one»
    _root_.GebMirror.Metalogic.«Theory.one»

def «Translation.bitsTy» :=
  _root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.bitTy»

def «Translation.treeTy» :=
  _root_.GebMirror.Metalogic.«Theory.lrose» _root_.GebMirror.Metalogic.«Translation.bitsTy»

def «Translation.ordTy» :=
  _root_.GebMirror.Metalogic.«Theory.coprod»
    _root_.GebMirror.Metalogic.«Theory.one»
    _root_.GebMirror.Metalogic.«Translation.bitTy»

def «Translation.trTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x2;
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» _root_.GebMirror.Metalogic.«Translation.treeTy»
          else
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.some» _root_.GebMirror.Metalogic.«Theory.one»
            else
              _root_.GebMirror.Metalogic.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x3
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Base.mapO»
                _root_.GebMirror.Metalogic.«Theory.list»
                (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
            else
              _root_.GebMirror.Metalogic.«Prelude.none»
          else
            if (_root_.Geb.Kernel.Const.eq
              x3
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
              if (_root_.Geb.Kernel.Const.eq
                x1
                (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
                  (fun (x4 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Base.mapO»
                      (_root_.GebMirror.Metalogic.«Theory.prod» x4)
                      (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x1
                  (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Base.bindO»
                    (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
                    (fun (x4 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.mapO»
                        (_root_.GebMirror.Metalogic.«Theory.exp» x4)
                        (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)))
                else
                  _root_.GebMirror.Metalogic.«Prelude.none»
            else
              _root_.GebMirror.Metalogic.«Prelude.none»)
      x0;
    x1

def «$284665772e6c32204c616e67756167652e5072696d697469766529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$284665772e6c33204c616e67756167652e5072696d697469766529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c32204c616e67756167652e5072696d697469766529»
        x1
        x2));
    x3

def «$284665772e6c34204c616e67756167652e5072696d697469766529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c33204c616e67756167652e5072696d697469766529»
        x1
        x2
        x3));
    x4

def «$284665772e6c35204c616e67756167652e5072696d697469766529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c34204c616e67756167652e5072696d697469766529»
        x1
        x2
        x3
        x4));
    x5

def «$284665772e6c36204c616e67756167652e5072696d697469766529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c35204c616e67756167652e5072696d697469766529»
        x1
        x2
        x3
        x4
        x5));
    x6

def «Translation.trPrims» :=
  _root_.GebMirror.Metalogic.«$284665772e6c36204c616e67756167652e5072696d697469766529»
    _root_.GebMirror.Metalogic.«Derivation.nilPrim»
    _root_.GebMirror.Metalogic.«Derivation.consPrim»
    _root_.GebMirror.Metalogic.«Derivation.lnodePrim»
    _root_.GebMirror.Metalogic.«Derivation.inlPrim»
    _root_.GebMirror.Metalogic.«Derivation.inrPrim»
    _root_.GebMirror.Metalogic.«Derivation.casePrim»

def «Translation.nilT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      _root_.GebMirror.Metalogic.«Language.mStar»;
    x1

def «Translation.consT» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      (_root_.GebMirror.Metalogic.«Language.mPair» x1 x2);
    x3

def «Translation.nodeT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
      (_root_.Geb.Kernel.leaf 2)
      (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      x0;
    x1

def «Translation.bit0T» :=
  _root_.GebMirror.Metalogic.«Language.mArr»
    (_root_.Geb.Kernel.leaf 3)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Theory.one»)
    _root_.GebMirror.Metalogic.«Language.mStar»

def «Translation.bit1T» :=
  _root_.GebMirror.Metalogic.«Language.mArr»
    (_root_.Geb.Kernel.leaf 4)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Theory.one»)
    _root_.GebMirror.Metalogic.«Language.mStar»

def «Translation.ifBit» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mArr»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.GebMirror.Metalogic.«Theory.l3»
          _root_.GebMirror.Metalogic.«Theory.one»
          _root_.GebMirror.Metalogic.«Theory.one»
          x0)
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Theory.one»
            (_root_.GebMirror.Metalogic.«Derivation.weaken1» x2))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Theory.one»
            (_root_.GebMirror.Metalogic.«Derivation.weaken1» x3))))
      x1;
    x4

def «Translation.ltO» :=
  _root_.GebMirror.Metalogic.«Language.mArr»
    (_root_.Geb.Kernel.leaf 3)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Translation.bitTy»)
    _root_.GebMirror.Metalogic.«Language.mStar»

def «Translation.eqO» :=
  _root_.GebMirror.Metalogic.«Language.mArr»
    (_root_.Geb.Kernel.leaf 4)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Translation.bitTy»)
    _root_.GebMirror.Metalogic.«Translation.bit0T»

def «Translation.gtO» :=
  _root_.GebMirror.Metalogic.«Language.mArr»
    (_root_.Geb.Kernel.leaf 4)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Translation.bitTy»)
    _root_.GebMirror.Metalogic.«Translation.bit1T»

def «Translation.ifOrd» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mArr»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.GebMirror.Metalogic.«Theory.l3»
          _root_.GebMirror.Metalogic.«Theory.one»
          _root_.GebMirror.Metalogic.«Translation.bitTy»
          x0)
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Theory.one»
            (_root_.GebMirror.Metalogic.«Derivation.weaken1» x2))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            (_root_.GebMirror.Metalogic.«Translation.ifBit»
              x0
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
              (_root_.GebMirror.Metalogic.«Derivation.weaken1» x3)
              (_root_.GebMirror.Metalogic.«Derivation.weaken1» x4)))))
      x1;
    x5

def «Translation.leafT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.nodeT»
      (_root_.GebMirror.Metalogic.«Language.mPair»
        x0
        (_root_.GebMirror.Metalogic.«Translation.nilT»
          _root_.GebMirror.Metalogic.«Translation.treeTy»));
    x1

def «Translation.call» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mDefn»
      x0
      x1
      (_root_.GebMirror.Metalogic.«Prelude.reverse» x2);
    x3

def «Translation.mkDefn» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.ldefn»
      x0
      (_root_.GebMirror.Metalogic.«Language.objs» (_root_.GebMirror.Metalogic.«Prelude.reverse» x1))
      x2
      x3;
    x4

def «Translation.bnilT» :=
  _root_.GebMirror.Metalogic.«Translation.call»
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Translation.b0T» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 1)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Translation.b1T» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Translation.trueT» :=
  _root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Translation.bnilT»

def «Translation.trNumeral» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                                          x0
                                          (_root_.Geb.Kernel.leaf 1);
                                        _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          (fun (x2 : _root_.Geb.Kernel.Tree)
                                             (x3 : _root_.Geb.Kernel.Tree) =>
                                            if (x2).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Translation.b1T» x3
                                            else
                                              _root_.GebMirror.Metalogic.«Translation.b0T» x3)
                                          _root_.GebMirror.Metalogic.«Translation.bnilT»
                                          (_root_.GebMirror.Metalogic.«Prelude.digitsLsb»
                                            (_root_.Geb.Kernel.leaf 2)
                                            x1
                                            (_root_.Geb.Kernel.Const.log2 x1)));
    x1

def «Translation.quoteT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Translation.nodeT»
          (_root_.GebMirror.Metalogic.«Language.mPair»
            (_root_.GebMirror.Metalogic.«Translation.trNumeral» x1)
            (_root_.Geb.Kernel.Const.foldr
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Translation.consT»
                _root_.GebMirror.Metalogic.«Translation.treeTy»)
              (_root_.GebMirror.Metalogic.«Translation.nilT»
                _root_.GebMirror.Metalogic.«Translation.treeTy»)
              x2)))
      x0;
    x1

def «Translation.condT» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 6)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      (_root_.GebMirror.Metalogic.«Theory.l3» x1 x2 x3);
    x4

def «Translation.lcaseB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 9)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1)
      (_root_.GebMirror.Metalogic.«Theory.l3»
        x2
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Theory.one»
          (_root_.GebMirror.Metalogic.«Derivation.weaken1» x3))
        x4);
    x5

def «Translation.cmpT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 16)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1);
    x2

def «Translation.digitT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.ifBit»
      _root_.GebMirror.Metalogic.«Translation.bitTy»
      x0
      (_root_.GebMirror.Metalogic.«Translation.ifBit»
        _root_.GebMirror.Metalogic.«Translation.bitTy»
        x1
        _root_.GebMirror.Metalogic.«Translation.bit1T»
        _root_.GebMirror.Metalogic.«Translation.bit0T»)
      (_root_.GebMirror.Metalogic.«Translation.ifBit»
        _root_.GebMirror.Metalogic.«Translation.bitTy»
        x1
        _root_.GebMirror.Metalogic.«Translation.bit0T»
        _root_.GebMirror.Metalogic.«Translation.bit1T»);
    x2

def «Translation.bitOrdT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.ifBit»
      _root_.GebMirror.Metalogic.«Translation.ordTy»
      x0
      (_root_.GebMirror.Metalogic.«Translation.ifBit»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        x1
        _root_.GebMirror.Metalogic.«Translation.eqO»
        _root_.GebMirror.Metalogic.«Translation.ltO»)
      (_root_.GebMirror.Metalogic.«Translation.ifBit»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        x1
        _root_.GebMirror.Metalogic.«Translation.gtO»
        _root_.GebMirror.Metalogic.«Translation.eqO»);
    x2

def «Translation.X0» :=
  _root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0)

def «Translation.X1» :=
  _root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)

def «Translation.lbBnil» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.nilT» _root_.GebMirror.Metalogic.«Translation.bitTy»)

def «Translation.lbB0» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.consT»
      _root_.GebMirror.Metalogic.«Translation.bitTy»
      _root_.GebMirror.Metalogic.«Translation.bit0T»
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbB1» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.consT»
      _root_.GebMirror.Metalogic.«Translation.bitTy»
      _root_.GebMirror.Metalogic.«Translation.bit1T»
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbLab» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mRoseRec»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      (_root_.GebMirror.Metalogic.«Language.mFst»
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbUnnode» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
    (_root_.GebMirror.Metalogic.«Theory.prod»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»))
    (_root_.GebMirror.Metalogic.«Language.mRoseRec»
      (_root_.GebMirror.Metalogic.«Theory.prod»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»
        (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»))
      (_root_.GebMirror.Metalogic.«Language.mPair»
        (_root_.GebMirror.Metalogic.«Language.mFst»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Translation.nilT»
            _root_.GebMirror.Metalogic.«Translation.treeTy»)
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.treeTy»
            (_root_.GebMirror.Metalogic.«Translation.nodeT»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Language.mSnd»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbChildren» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Translation.call»
        (_root_.Geb.Kernel.leaf 4)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))

def «Translation.lbCond» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Theory.l3»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.X0»
      _root_.GebMirror.Metalogic.«Translation.X0»)
    _root_.GebMirror.Metalogic.«Translation.X0»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.app»
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.X0»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.X0»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.X0»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.X0»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbTail» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Prelude.single»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»))
    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»)
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.nilT» _root_.GebMirror.Metalogic.«Translation.X0»)
          (_root_.GebMirror.Metalogic.«Translation.nilT» _root_.GebMirror.Metalogic.«Translation.X0»))
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.X0»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.mFst»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Language.mFst»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))

def «Translation.lbHeadD» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.X0»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»))
    _root_.GebMirror.Metalogic.«Translation.X0»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.X0»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.X0»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbLcase» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.exp»
    _root_.GebMirror.Metalogic.«Translation.X0»
    (_root_.GebMirror.Metalogic.«Theory.exp»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»)
      _root_.GebMirror.Metalogic.«Translation.X1»);
  let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
    (_root_.GebMirror.Metalogic.«Theory.exp»
      _root_.GebMirror.Metalogic.«Theory.one»
      _root_.GebMirror.Metalogic.«Translation.X1»)
    x0;
  let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mFst»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)));
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 2)
    (_root_.GebMirror.Metalogic.«Theory.l3»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»)
      (_root_.GebMirror.Metalogic.«Theory.exp»
        _root_.GebMirror.Metalogic.«Theory.one»
        _root_.GebMirror.Metalogic.«Translation.X1»)
      x0)
    _root_.GebMirror.Metalogic.«Translation.X1»
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Language.app»
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            x1
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.nilT» _root_.GebMirror.Metalogic.«Translation.X0»)
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Language.mFst»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                _root_.GebMirror.Metalogic.«Language.mStar»)))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            x1
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.consT»
                _root_.GebMirror.Metalogic.«Translation.X0»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                x2)
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.mSnd»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
                x2)))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))

def «Translation.lbIsNil» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Prelude.single»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»))
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mListRec»
      _root_.GebMirror.Metalogic.«Translation.trueT»
      _root_.GebMirror.Metalogic.«Translation.bnilT»
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbSucc» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.trueT»)
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.mFst»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Translation.ifBit»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Translation.b1T»
              (_root_.GebMirror.Metalogic.«Language.mFst»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
            (_root_.GebMirror.Metalogic.«Translation.b0T»
              (_root_.GebMirror.Metalogic.«Language.mSnd»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))

def «Translation.lbLength» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Prelude.single»
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X0»))
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mListRec»
      _root_.GebMirror.Metalogic.«Translation.bnilT»
      (_root_.GebMirror.Metalogic.«Translation.call»
        (_root_.Geb.Kernel.leaf 11)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbPred» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.mFst»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Translation.ifBit»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Translation.condT»
              _root_.GebMirror.Metalogic.«Translation.bitsTy»
              (_root_.GebMirror.Metalogic.«Language.mFst»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
              (_root_.GebMirror.Metalogic.«Translation.b1T»
                (_root_.GebMirror.Metalogic.«Language.mSnd»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
              _root_.GebMirror.Metalogic.«Translation.bnilT»)
            (_root_.GebMirror.Metalogic.«Translation.b0T»
              (_root_.GebMirror.Metalogic.«Language.mFst»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))

def «Translation.lbDbl» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.mSnd»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        (_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.mFst»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Translation.ifBit»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Translation.b1T»
              (_root_.GebMirror.Metalogic.«Language.mSnd»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
            (_root_.GebMirror.Metalogic.«Translation.b1T»
              (_root_.GebMirror.Metalogic.«Translation.b0T»
                (_root_.GebMirror.Metalogic.«Language.mFst»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))

def «Translation.lbAdd» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mSnd»
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Language.mPair»
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.bitsTy»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Language.mPair»
            (_root_.GebMirror.Metalogic.«Translation.consT»
              _root_.GebMirror.Metalogic.«Translation.bitTy»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
              (_root_.GebMirror.Metalogic.«Language.mFst»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.bitsTy»
              (_root_.GebMirror.Metalogic.«Translation.lcaseB»
                _root_.GebMirror.Metalogic.«Translation.bitTy»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                (_root_.GebMirror.Metalogic.«Translation.consT»
                  _root_.GebMirror.Metalogic.«Translation.bitTy»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                  (_root_.GebMirror.Metalogic.«Language.mFst»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
                (_root_.GebMirror.Metalogic.«Language.mLam»
                  _root_.GebMirror.Metalogic.«Translation.bitTy»
                  (_root_.GebMirror.Metalogic.«Language.mLam»
                    _root_.GebMirror.Metalogic.«Translation.bitsTy»
                    (_root_.GebMirror.Metalogic.«Translation.consT»
                      _root_.GebMirror.Metalogic.«Translation.bitTy»
                      (_root_.GebMirror.Metalogic.«Translation.digitT»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4)))
                      (_root_.GebMirror.Metalogic.«Language.app»
                        (_root_.GebMirror.Metalogic.«Language.mLam»
                          _root_.GebMirror.Metalogic.«Translation.bitsTy»
                          (_root_.GebMirror.Metalogic.«Translation.ifBit»
                            _root_.GebMirror.Metalogic.«Translation.bitsTy»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                            (_root_.GebMirror.Metalogic.«Translation.ifBit»
                              _root_.GebMirror.Metalogic.«Translation.bitsTy»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 5))
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                              (_root_.GebMirror.Metalogic.«Translation.call»
                                (_root_.Geb.Kernel.leaf 11)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
                            (_root_.GebMirror.Metalogic.«Translation.call»
                              (_root_.Geb.Kernel.leaf 11)
                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
                        (_root_.GebMirror.Metalogic.«Language.app»
                          (_root_.GebMirror.Metalogic.«Language.mSnd»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3)))
                          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))))))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbCmp» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.ordTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.condT»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Translation.gtO»
            _root_.GebMirror.Metalogic.«Translation.eqO»))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.lcaseB»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Translation.ltO»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.bitTy»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Translation.ifOrd»
                  _root_.GebMirror.Metalogic.«Translation.ordTy»
                  (_root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                  _root_.GebMirror.Metalogic.«Translation.ltO»
                  (_root_.GebMirror.Metalogic.«Translation.bitOrdT»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4)))
                  _root_.GebMirror.Metalogic.«Translation.gtO»)))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbLtB» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.ifOrd»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      (_root_.GebMirror.Metalogic.«Translation.cmpT»
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      _root_.GebMirror.Metalogic.«Translation.trueT»
      _root_.GebMirror.Metalogic.«Translation.bnilT»
      _root_.GebMirror.Metalogic.«Translation.bnilT»)

def «Translation.lbEqB» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 10)
            (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitTy»)
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.lcaseB»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.bitTy»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Translation.ifBit»
                  _root_.GebMirror.Metalogic.«Translation.bitsTy»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Translation.ifBit»
                    _root_.GebMirror.Metalogic.«Translation.bitsTy»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4))
                    (_root_.GebMirror.Metalogic.«Language.app»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                    _root_.GebMirror.Metalogic.«Translation.bnilT»)
                  (_root_.GebMirror.Metalogic.«Translation.ifBit»
                    _root_.GebMirror.Metalogic.«Translation.bitsTy»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4))
                    _root_.GebMirror.Metalogic.«Translation.bnilT»
                    (_root_.GebMirror.Metalogic.«Language.app»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbSubE» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.lcaseB»
            _root_.GebMirror.Metalogic.«Translation.bitTy»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.bitTy»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.mLam»
                    _root_.GebMirror.Metalogic.«Translation.bitsTy»
                    (_root_.GebMirror.Metalogic.«Translation.ifBit»
                      _root_.GebMirror.Metalogic.«Translation.bitsTy»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                      (_root_.GebMirror.Metalogic.«Translation.ifBit»
                        _root_.GebMirror.Metalogic.«Translation.bitsTy»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 5))
                        (_root_.GebMirror.Metalogic.«Translation.call»
                          (_root_.Geb.Kernel.leaf 14)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
                        (_root_.GebMirror.Metalogic.«Translation.b0T»
                          (_root_.GebMirror.Metalogic.«Translation.call»
                            (_root_.Geb.Kernel.leaf 13)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Prelude.single»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
                      (_root_.GebMirror.Metalogic.«Translation.ifBit»
                        _root_.GebMirror.Metalogic.«Translation.bitsTy»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 5))
                        (_root_.GebMirror.Metalogic.«Translation.b0T»
                          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                        (_root_.GebMirror.Metalogic.«Translation.call»
                          (_root_.Geb.Kernel.leaf 14)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))
                  (_root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbSub» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.condT»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      (_root_.GebMirror.Metalogic.«Translation.call»
        (_root_.Geb.Kernel.leaf 17)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Theory.l2»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
      _root_.GebMirror.Metalogic.«Translation.bnilT»
      (_root_.GebMirror.Metalogic.«Translation.call»
        (_root_.Geb.Kernel.leaf 19)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Theory.l2»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))

def «Translation.lbMul» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 15)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2»
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 14)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
              (_root_.GebMirror.Metalogic.«Translation.ifBit»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                (_root_.GebMirror.Metalogic.«Translation.call»
                  (_root_.Geb.Kernel.leaf 14)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))

def «Translation.lbDivMod» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»;
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    x0
    (_root_.GebMirror.Metalogic.«Translation.condT»
      x0
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
      (_root_.GebMirror.Metalogic.«Language.app»
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.mPair»
              _root_.GebMirror.Metalogic.«Translation.bnilT»
              _root_.GebMirror.Metalogic.«Translation.bnilT»))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Language.app»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                x0
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.mLam»
                    _root_.GebMirror.Metalogic.«Translation.bitsTy»
                    (_root_.GebMirror.Metalogic.«Translation.ifOrd»
                      x0
                      (_root_.GebMirror.Metalogic.«Translation.cmpT»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
                      (_root_.GebMirror.Metalogic.«Language.mPair»
                        (_root_.GebMirror.Metalogic.«Translation.call»
                          (_root_.Geb.Kernel.leaf 14)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.mFst»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))))
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                      (_root_.GebMirror.Metalogic.«Language.mPair»
                        (_root_.GebMirror.Metalogic.«Translation.b0T»
                          (_root_.GebMirror.Metalogic.«Language.mFst»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
                        _root_.GebMirror.Metalogic.«Translation.bnilT»)
                      (_root_.GebMirror.Metalogic.«Translation.ifOrd»
                        x0
                        (_root_.GebMirror.Metalogic.«Translation.cmpT»
                          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                          (_root_.GebMirror.Metalogic.«Translation.call»
                            (_root_.Geb.Kernel.leaf 14)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Prelude.single»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))))
                        (_root_.GebMirror.Metalogic.«Language.mPair»
                          (_root_.GebMirror.Metalogic.«Translation.b0T»
                            (_root_.GebMirror.Metalogic.«Language.mFst»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
                          (_root_.GebMirror.Metalogic.«Translation.call»
                            (_root_.Geb.Kernel.leaf 19)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))))
                        (_root_.GebMirror.Metalogic.«Language.mPair»
                          (_root_.GebMirror.Metalogic.«Translation.b1T»
                            (_root_.GebMirror.Metalogic.«Language.mFst»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
                          _root_.GebMirror.Metalogic.«Translation.bnilT»)
                        (_root_.GebMirror.Metalogic.«Language.mPair»
                          (_root_.GebMirror.Metalogic.«Translation.b1T»
                            (_root_.GebMirror.Metalogic.«Language.mFst»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))
                          _root_.GebMirror.Metalogic.«Translation.bnilT»))))
                  (_root_.GebMirror.Metalogic.«Translation.consT»
                    _root_.GebMirror.Metalogic.«Translation.bitTy»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
                    (_root_.GebMirror.Metalogic.«Language.mSnd»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Language.mPair»
        _root_.GebMirror.Metalogic.«Translation.bnilT»
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))

def «Translation.lbLog2» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»;
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mLam»
        x0
        (_root_.GebMirror.Metalogic.«Translation.condT»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»
          (_root_.GebMirror.Metalogic.«Language.mSnd»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Language.mFst»
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 13)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Language.mFst»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        (_root_.GebMirror.Metalogic.«Language.app»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            x0
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 11)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Language.mFst»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
              (_root_.GebMirror.Metalogic.«Translation.ifBit»
                _root_.GebMirror.Metalogic.«Translation.bitsTy»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                (_root_.GebMirror.Metalogic.«Language.mSnd»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                _root_.GebMirror.Metalogic.«Translation.trueT»)))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))

def «Translation.lbIter» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.exp»
    _root_.GebMirror.Metalogic.«Translation.X0»
    _root_.GebMirror.Metalogic.«Translation.X0»;
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Theory.l3»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      x0
      _root_.GebMirror.Metalogic.«Translation.X0»)
    _root_.GebMirror.Metalogic.«Translation.X0»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.app»
        (_root_.GebMirror.Metalogic.«Language.mListRec»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            x0
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.X0»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
          (_root_.GebMirror.Metalogic.«Language.mLam»
            x0
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.X0»
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Language.mLam»
                  _root_.GebMirror.Metalogic.«Translation.X0»
                  (_root_.GebMirror.Metalogic.«Translation.ifBit»
                    _root_.GebMirror.Metalogic.«Translation.X0»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4))
                    (_root_.GebMirror.Metalogic.«Language.app»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                    (_root_.GebMirror.Metalogic.«Language.app»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                      (_root_.GebMirror.Metalogic.«Language.app»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                  (_root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.app»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbMapApp» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 2)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      (_root_.GebMirror.Metalogic.«Theory.list»
        (_root_.GebMirror.Metalogic.«Theory.exp»
          _root_.GebMirror.Metalogic.«Translation.X0»
          _root_.GebMirror.Metalogic.«Translation.X1»))
      _root_.GebMirror.Metalogic.«Translation.X0»)
    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.X1»)
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.X0»
          (_root_.GebMirror.Metalogic.«Translation.nilT» _root_.GebMirror.Metalogic.«Translation.X1»))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.X0»
          (_root_.GebMirror.Metalogic.«Translation.consT»
            _root_.GebMirror.Metalogic.«Translation.X1»
            (_root_.GebMirror.Metalogic.«Language.app»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
            (_root_.GebMirror.Metalogic.«Language.app»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbAnd» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Translation.condT»
      _root_.GebMirror.Metalogic.«Translation.bitsTy»
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))
      _root_.GebMirror.Metalogic.«Translation.bnilT»)

def «Translation.lbAllZip» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      (_root_.GebMirror.Metalogic.«Theory.list»
        (_root_.GebMirror.Metalogic.«Theory.exp»
          _root_.GebMirror.Metalogic.«Translation.treeTy»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»))
      (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»))
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mListRec»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 10)
            (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
        (_root_.GebMirror.Metalogic.«Language.mLam»
          (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
          (_root_.GebMirror.Metalogic.«Translation.condT»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Translation.call»
              (_root_.Geb.Kernel.leaf 10)
              (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
              (_root_.GebMirror.Metalogic.«Prelude.single»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Translation.call»
              (_root_.Geb.Kernel.leaf 26)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 8)
                    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                    (_root_.GebMirror.Metalogic.«Theory.l2»
                      (_root_.GebMirror.Metalogic.«Translation.leafT»
                        _root_.GebMirror.Metalogic.«Translation.bnilT»)
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
                (_root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 7)
                    (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lbEqual» :=
  _root_.GebMirror.Metalogic.«Translation.mkDefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      _root_.GebMirror.Metalogic.«Translation.treeTy»
      _root_.GebMirror.Metalogic.«Translation.treeTy»)
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Language.app»
      (_root_.GebMirror.Metalogic.«Language.mRoseRec»
        (_root_.GebMirror.Metalogic.«Theory.exp»
          _root_.GebMirror.Metalogic.«Translation.treeTy»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.treeTy»
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 26)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2»
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 18)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Theory.l2»
                  (_root_.GebMirror.Metalogic.«Language.mFst»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 3)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 27)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Theory.l2»
                  (_root_.GebMirror.Metalogic.«Language.mSnd»
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 5)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))

def «Translation.lib» :=
  (_root_.GebMirror.Metalogic.«Translation.lbBnil» ::
    (_root_.GebMirror.Metalogic.«Translation.lbB0» ::
      (_root_.GebMirror.Metalogic.«Translation.lbB1» ::
        (_root_.GebMirror.Metalogic.«Translation.lbLab» ::
          (_root_.GebMirror.Metalogic.«Translation.lbUnnode» ::
            (_root_.GebMirror.Metalogic.«Translation.lbChildren» ::
              (_root_.GebMirror.Metalogic.«Translation.lbCond» ::
                (_root_.GebMirror.Metalogic.«Translation.lbTail» ::
                  (_root_.GebMirror.Metalogic.«Translation.lbHeadD» ::
                    (_root_.GebMirror.Metalogic.«Translation.lbLcase» ::
                      (_root_.GebMirror.Metalogic.«Translation.lbIsNil» ::
                        (_root_.GebMirror.Metalogic.«Translation.lbSucc» ::
                          (_root_.GebMirror.Metalogic.«Translation.lbLength» ::
                            (_root_.GebMirror.Metalogic.«Translation.lbPred» ::
                              (_root_.GebMirror.Metalogic.«Translation.lbDbl» ::
                                (_root_.GebMirror.Metalogic.«Translation.lbAdd» ::
                                  (_root_.GebMirror.Metalogic.«Translation.lbCmp» ::
                                    (_root_.GebMirror.Metalogic.«Translation.lbLtB» ::
                                      (_root_.GebMirror.Metalogic.«Translation.lbEqB» ::
                                        (_root_.GebMirror.Metalogic.«Translation.lbSubE» ::
                                          (_root_.GebMirror.Metalogic.«Translation.lbSub» ::
                                            (_root_.GebMirror.Metalogic.«Translation.lbMul» ::
                                              (_root_.GebMirror.Metalogic.«Translation.lbDivMod» ::
                                                (_root_.GebMirror.Metalogic.«Translation.lbLog2» ::
                                                  (_root_.GebMirror.Metalogic.«Translation.lbIter» ::
                                                    (_root_.GebMirror.Metalogic.«Translation.lbMapApp» ::
                                                      (_root_.GebMirror.Metalogic.«Translation.lbAnd» ::
                                                        (_root_.GebMirror.Metalogic.«Translation.lbAllZip» ::
                                                          (_root_.GebMirror.Metalogic.«Translation.lbEqual» ::
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree))))))))))))))))))))))))))))))

def «Translation.foldT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.exp»
                                          _root_.GebMirror.Metalogic.«Translation.treeTy»
                                          (_root_.GebMirror.Metalogic.«Theory.exp»
                                            (_root_.GebMirror.Metalogic.«Theory.list» x0)
                                            x0);
                                        _root_.GebMirror.Metalogic.«Language.mLam»
                                          x1
                                          (_root_.GebMirror.Metalogic.«Language.mLam»
                                            _root_.GebMirror.Metalogic.«Translation.treeTy»
                                            (_root_.GebMirror.Metalogic.«Language.app»
                                              (_root_.GebMirror.Metalogic.«Language.mRoseRec»
                                                (_root_.GebMirror.Metalogic.«Theory.exp» x1 x0)
                                                (_root_.GebMirror.Metalogic.«Language.mLam»
                                                  x1
                                                  (_root_.GebMirror.Metalogic.«Language.app»
                                                    (_root_.GebMirror.Metalogic.«Language.app»
                                                      (_root_.GebMirror.Metalogic.«Language.var»
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      (_root_.GebMirror.Metalogic.«Translation.leafT»
                                                        (_root_.GebMirror.Metalogic.«Language.mFst»
                                                          (_root_.GebMirror.Metalogic.«Language.var»
                                                            (_root_.Geb.Kernel.leaf 1)))))
                                                    (_root_.GebMirror.Metalogic.«Translation.call»
                                                      (_root_.Geb.Kernel.leaf 25)
                                                      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x0)
                                                      (_root_.GebMirror.Metalogic.«Theory.l2»
                                                        (_root_.GebMirror.Metalogic.«Language.mSnd»
                                                          (_root_.GebMirror.Metalogic.«Language.var»
                                                            (_root_.Geb.Kernel.leaf 1)))
                                                        (_root_.GebMirror.Metalogic.«Language.var»
                                                          (_root_.Geb.Kernel.leaf 0))))))
                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                  (_root_.Geb.Kernel.leaf 0)))
                                              (_root_.GebMirror.Metalogic.«Language.var»
                                                (_root_.Geb.Kernel.leaf 1)))));
    x1

def «Translation.fstsT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mListRec»
      (_root_.GebMirror.Metalogic.«Translation.nilT»
        _root_.GebMirror.Metalogic.«Translation.treeTy»)
      (_root_.GebMirror.Metalogic.«Translation.consT»
        _root_.GebMirror.Metalogic.«Translation.treeTy»
        (_root_.GebMirror.Metalogic.«Language.mFst»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      x0;
    x1

def «Translation.sndsT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mListRec»
      (_root_.GebMirror.Metalogic.«Translation.nilT» x0)
      (_root_.GebMirror.Metalogic.«Translation.consT»
        x0
        (_root_.GebMirror.Metalogic.«Language.mSnd»
          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
      x1;
    x2

def «Translation.paraT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.exp»
                                          _root_.GebMirror.Metalogic.«Translation.treeTy»
                                          (_root_.GebMirror.Metalogic.«Theory.exp»
                                            (_root_.GebMirror.Metalogic.«Theory.list» x0)
                                            x0);
                                        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
                                          _root_.GebMirror.Metalogic.«Translation.treeTy»
                                          x0;
                                        _root_.GebMirror.Metalogic.«Language.mLam»
                                          x1
                                          (_root_.GebMirror.Metalogic.«Language.mLam»
                                            _root_.GebMirror.Metalogic.«Translation.treeTy»
                                            (_root_.GebMirror.Metalogic.«Language.mSnd»
                                              (_root_.GebMirror.Metalogic.«Language.app»
                                                (_root_.GebMirror.Metalogic.«Language.mRoseRec»
                                                  (_root_.GebMirror.Metalogic.«Theory.exp» x1 x2)
                                                  (_root_.GebMirror.Metalogic.«Language.mLam»
                                                    x1
                                                    (_root_.GebMirror.Metalogic.«Language.app»
                                                      (_root_.GebMirror.Metalogic.«Language.mLam»
                                                        (_root_.GebMirror.Metalogic.«Theory.list» x2)
                                                        (_root_.GebMirror.Metalogic.«Language.app»
                                                          (_root_.GebMirror.Metalogic.«Language.mLam»
                                                            _root_.GebMirror.Metalogic.«Translation.treeTy»
                                                            (_root_.GebMirror.Metalogic.«Language.mPair»
                                                              (_root_.GebMirror.Metalogic.«Language.var»
                                                                (_root_.Geb.Kernel.leaf 0))
                                                              (_root_.GebMirror.Metalogic.«Language.app»
                                                                (_root_.GebMirror.Metalogic.«Language.app»
                                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                                    (_root_.Geb.Kernel.leaf 2))
                                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                                    (_root_.Geb.Kernel.leaf 0)))
                                                                (_root_.GebMirror.Metalogic.«Translation.sndsT»
                                                                  x0
                                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                                    (_root_.Geb.Kernel.leaf 1))))))
                                                          (_root_.GebMirror.Metalogic.«Translation.nodeT»
                                                            (_root_.GebMirror.Metalogic.«Language.mPair»
                                                              (_root_.GebMirror.Metalogic.«Language.mFst»
                                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                                  (_root_.Geb.Kernel.leaf 2)))
                                                              (_root_.GebMirror.Metalogic.«Translation.fstsT»
                                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                                  (_root_.Geb.Kernel.leaf 0)))))))
                                                      (_root_.GebMirror.Metalogic.«Translation.call»
                                                        (_root_.Geb.Kernel.leaf 25)
                                                        (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
                                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                                          (_root_.GebMirror.Metalogic.«Language.mSnd»
                                                            (_root_.GebMirror.Metalogic.«Language.var»
                                                              (_root_.Geb.Kernel.leaf 1)))
                                                          (_root_.GebMirror.Metalogic.«Language.var»
                                                            (_root_.Geb.Kernel.leaf 0))))))
                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                    (_root_.Geb.Kernel.leaf 0)))
                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                  (_root_.Geb.Kernel.leaf 1))))));
    x1

def «Translation.iterT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
      (_root_.GebMirror.Metalogic.«Theory.exp» x0 x0)
      (_root_.GebMirror.Metalogic.«Language.mLam»
        x0
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.treeTy»
          (_root_.GebMirror.Metalogic.«Translation.call»
            (_root_.Geb.Kernel.leaf 24)
            (_root_.GebMirror.Metalogic.«Prelude.single» x0)
            (_root_.GebMirror.Metalogic.«Theory.l3»
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 3)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))));
    x1

def «Translation.foldrT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
                                          (_root_.GebMirror.Metalogic.«Theory.exp»
                                            x0
                                            (_root_.GebMirror.Metalogic.«Theory.exp» x1 x1))
                                          x1;
                                        _root_.GebMirror.Metalogic.«Language.mLam»
                                          (_root_.GebMirror.Metalogic.«Theory.exp»
                                            x0
                                            (_root_.GebMirror.Metalogic.«Theory.exp» x1 x1))
                                          (_root_.GebMirror.Metalogic.«Language.mLam»
                                            x1
                                            (_root_.GebMirror.Metalogic.«Language.mLam»
                                              (_root_.GebMirror.Metalogic.«Theory.list» x0)
                                              (_root_.GebMirror.Metalogic.«Language.app»
                                                (_root_.GebMirror.Metalogic.«Language.mListRec»
                                                  (_root_.GebMirror.Metalogic.«Language.mLam»
                                                    x2
                                                    (_root_.GebMirror.Metalogic.«Language.mSnd»
                                                      (_root_.GebMirror.Metalogic.«Language.var»
                                                        (_root_.Geb.Kernel.leaf 0))))
                                                  (_root_.GebMirror.Metalogic.«Language.mLam»
                                                    x2
                                                    (_root_.GebMirror.Metalogic.«Language.app»
                                                      (_root_.GebMirror.Metalogic.«Language.app»
                                                        (_root_.GebMirror.Metalogic.«Language.mFst»
                                                          (_root_.GebMirror.Metalogic.«Language.var»
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                        (_root_.GebMirror.Metalogic.«Language.var»
                                                          (_root_.Geb.Kernel.leaf 2)))
                                                      (_root_.GebMirror.Metalogic.«Language.app»
                                                        (_root_.GebMirror.Metalogic.«Language.var»
                                                          (_root_.Geb.Kernel.leaf 1))
                                                        (_root_.GebMirror.Metalogic.«Language.var»
                                                          (_root_.Geb.Kernel.leaf 0)))))
                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                    (_root_.Geb.Kernel.leaf 0)))
                                                (_root_.GebMirror.Metalogic.«Language.mPair»
                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                    (_root_.Geb.Kernel.leaf 2))
                                                  (_root_.GebMirror.Metalogic.«Language.var»
                                                    (_root_.Geb.Kernel.leaf 1)))))));
    x2

def «Translation.lcaseT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
      (_root_.GebMirror.Metalogic.«Theory.list» x0)
      (_root_.GebMirror.Metalogic.«Language.mLam»
        x1
        (_root_.GebMirror.Metalogic.«Language.mLam»
          (_root_.GebMirror.Metalogic.«Theory.exp»
            x0
            (_root_.GebMirror.Metalogic.«Theory.exp» (_root_.GebMirror.Metalogic.«Theory.list» x0) x1))
          (_root_.GebMirror.Metalogic.«Translation.lcaseB»
            x0
            x1
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2))
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))));
    x2

def «Translation.labT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 3)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Translation.binT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
      _root_.GebMirror.Metalogic.«Translation.treeTy»
      (_root_.GebMirror.Metalogic.«Language.mLam»
        _root_.GebMirror.Metalogic.«Translation.treeTy»
        (_root_.GebMirror.Metalogic.«Translation.leafT»
          (x0
            (_root_.GebMirror.Metalogic.«Translation.labT»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
            (_root_.GebMirror.Metalogic.«Translation.labT»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))));
    x1

def «Translation.primT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Translation.treeTy»
          (_root_.GebMirror.Metalogic.«Translation.leafT»
            (_root_.GebMirror.Metalogic.«Translation.labT»
              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Language.mLam»
            _root_.GebMirror.Metalogic.«Translation.treeTy»
            (_root_.GebMirror.Metalogic.«Translation.leafT»
              (_root_.GebMirror.Metalogic.«Translation.call»
                (_root_.Geb.Kernel.leaf 12)
                (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 5)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))))
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.GebMirror.Metalogic.«Language.mLam»
              _root_.GebMirror.Metalogic.«Translation.treeTy»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                _root_.GebMirror.Metalogic.«Translation.treeTy»
                (_root_.GebMirror.Metalogic.«Translation.call»
                  (_root_.Geb.Kernel.leaf 8)
                  (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.GebMirror.Metalogic.«Translation.leafT»
                      _root_.GebMirror.Metalogic.«Translation.bnilT»)
                    (_root_.GebMirror.Metalogic.«Translation.call»
                      (_root_.Geb.Kernel.leaf 24)
                      (_root_.GebMirror.Metalogic.«Prelude.single»
                        (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»))
                      (_root_.GebMirror.Metalogic.«Theory.l3»
                        (_root_.GebMirror.Metalogic.«Translation.labT»
                          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
                        (_root_.GebMirror.Metalogic.«Language.mLam»
                          (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                          (_root_.GebMirror.Metalogic.«Translation.call»
                            (_root_.Geb.Kernel.leaf 7)
                            (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                            (_root_.GebMirror.Metalogic.«Prelude.single»
                              (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
                        (_root_.GebMirror.Metalogic.«Translation.call»
                          (_root_.Geb.Kernel.leaf 5)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))))))))))
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some»
              (_root_.GebMirror.Metalogic.«Language.mLam»
                _root_.GebMirror.Metalogic.«Translation.treeTy»
                (_root_.GebMirror.Metalogic.«Language.mLam»
                  (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                  (_root_.GebMirror.Metalogic.«Translation.nodeT»
                    (_root_.GebMirror.Metalogic.«Language.mPair»
                      (_root_.GebMirror.Metalogic.«Translation.labT»
                        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))))
          else
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.some»
                (_root_.GebMirror.Metalogic.«Language.mLam»
                  _root_.GebMirror.Metalogic.«Translation.treeTy»
                  (_root_.GebMirror.Metalogic.«Translation.call»
                    (_root_.Geb.Kernel.leaf 5)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Prelude.some»
                  (_root_.GebMirror.Metalogic.«Translation.binT»
                    (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Translation.call»
                        (_root_.Geb.Kernel.leaf 15)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Prelude.some»
                    (_root_.GebMirror.Metalogic.«Translation.binT»
                      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Translation.call»
                          (_root_.Geb.Kernel.leaf 20)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)))
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«Prelude.some»
                      (_root_.GebMirror.Metalogic.«Translation.binT»
                        (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Translation.call»
                            (_root_.Geb.Kernel.leaf 21)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)))
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«Prelude.some»
                        (_root_.GebMirror.Metalogic.«Translation.binT»
                          (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                            _root_.GebMirror.Metalogic.«Language.mFst»
                              (_root_.GebMirror.Metalogic.«Translation.call»
                                (_root_.Geb.Kernel.leaf 22)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2))))
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                        _root_.GebMirror.Metalogic.«Prelude.some»
                          (_root_.GebMirror.Metalogic.«Translation.binT»
                            (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«Language.mSnd»
                                (_root_.GebMirror.Metalogic.«Translation.call»
                                  (_root_.Geb.Kernel.leaf 22)
                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                  (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2))))
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«Prelude.some»
                            (_root_.GebMirror.Metalogic.«Translation.binT»
                              (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                                _root_.GebMirror.Metalogic.«Translation.call»
                                  (_root_.Geb.Kernel.leaf 18)
                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                  (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)))
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                            _root_.GebMirror.Metalogic.«Prelude.some»
                              (_root_.GebMirror.Metalogic.«Translation.binT»
                                (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«Translation.call»
                                    (_root_.Geb.Kernel.leaf 17)
                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                    (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)))
                          else
                            if (_root_.Geb.Kernel.Const.eq
                              x0
                              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«Prelude.some»
                                (_root_.GebMirror.Metalogic.«Language.mLam»
                                  _root_.GebMirror.Metalogic.«Translation.treeTy»
                                  (_root_.GebMirror.Metalogic.«Language.mLam»
                                    _root_.GebMirror.Metalogic.«Translation.treeTy»
                                    (_root_.GebMirror.Metalogic.«Translation.leafT»
                                      (_root_.GebMirror.Metalogic.«Translation.call»
                                        (_root_.Geb.Kernel.leaf 28)
                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                                          (_root_.GebMirror.Metalogic.«Language.var»
                                            (_root_.Geb.Kernel.leaf 0)))))))
                            else
                              if (_root_.Geb.Kernel.Const.eq
                                x0
                                (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                _root_.GebMirror.Metalogic.«Prelude.some»
                                  (_root_.GebMirror.Metalogic.«Language.mLam»
                                    _root_.GebMirror.Metalogic.«Translation.treeTy»
                                    (_root_.GebMirror.Metalogic.«Translation.leafT»
                                      (_root_.GebMirror.Metalogic.«Translation.call»
                                        (_root_.Geb.Kernel.leaf 23)
                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                        (_root_.GebMirror.Metalogic.«Prelude.single»
                                          (_root_.GebMirror.Metalogic.«Translation.labT»
                                            (_root_.GebMirror.Metalogic.«Language.var»
                                              (_root_.Geb.Kernel.leaf 0)))))))
                              else
                                _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Translation.kArrowParts» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 3))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
        (_root_.GebMirror.Metalogic.«Language.pr»
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1)))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x1

def «Translation.kProdParts» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
        (_root_.GebMirror.Metalogic.«Language.pr»
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1)))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x1

def «Translation.kListPart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 4))
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x0)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Translation.trKids» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree)
        (fun (x4 : _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x5 : _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree)
           (x6 : _root_.Geb.Kernel.Tree)
           (x7 : _root_.List _root_.Geb.Kernel.Tree)
           (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
          ((if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              x4 x7 (x1 :: x8)
            else
              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
          else
            if (_root_.GebMirror.Metalogic.«Prelude.or»
              (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 10))
              (_root_.GebMirror.Metalogic.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 12))
                (_root_.GebMirror.Metalogic.«Prelude.or»
                  (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 13))
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 14))
                    (_root_.GebMirror.Metalogic.«Prelude.or»
                      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 16))
                      (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 20))))))).label ≠ 0 then
              x4 x7 x8
            else
              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229») ::
            (x5
              (_root_.Geb.Kernel.Const.add x6 (_root_.Geb.Kernel.leaf 1))
              x7
              x8)))
        (fun (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          ([] : _root_.List _root_.Geb.Kernel.Tree))
        x2
        x3);
    x3

def «$284c697374732e7461696c2032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2)

def «Translation.trAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«$284c697374732e7461696c2032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
        x0
        x1)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x2

def «Translation.bindP» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x2

def «Translation.bindTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.Metalogic.«Prelude.get» x0)
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x2

def «Translation.mapTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
        (x0 (_root_.GebMirror.Metalogic.«Prelude.get» x1))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x2

def «$285365712e6c656e677468204c616e67756167652e4c4465666e29» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «Translation.termStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x2 : _root_.List _root_.Geb.Kernel.Tree →
                                     _root_.List _root_.Geb.Kernel.Tree →
                                       _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.trKids»
                                     (_root_.Geb.Kernel.Const.label x0)
                                     (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))
                                     x1
                                     (_root_.Geb.Kernel.leaf 0);
                                   fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                     (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                       x0;
                                     let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.arity
                                       x0;
                                     let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                       x0
                                       (_root_.Geb.Kernel.leaf 0);
                                     let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                       x0
                                       (_root_.Geb.Kernel.leaf 1);
                                     let x9 : _root_.List _root_.Geb.Kernel.Tree := x2 x3 x4;
                                     if (_root_.Geb.Kernel.Const.eq
                                       x5
                                       (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                       if (_root_.Geb.Kernel.Const.eq
                                         x6
                                         (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                         _root_.GebMirror.Metalogic.«Translation.bindTy»
                                           (_root_.GebMirror.Metalogic.«Prelude.nth»
                                             x4
                                             (_root_.Geb.Kernel.Const.label x7))
                                           (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                               (_root_.GebMirror.Metalogic.«Language.pr»
                                                 x10
                                                 (_root_.GebMirror.Metalogic.«Language.var»
                                                   (_root_.Geb.Kernel.Const.label x7))))
                                       else
                                         _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                     else
                                       if (_root_.Geb.Kernel.Const.eq
                                         x5
                                         (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                         if (_root_.Geb.Kernel.Const.eq
                                           x6
                                           (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                           if (_root_.GebMirror.Metalogic.«Check.isTy» x7).label ≠ 0 then
                                             _root_.GebMirror.Metalogic.«Translation.bindP»
                                               (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                 x9
                                                 (_root_.Geb.Kernel.leaf 1))
                                               (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                   (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«Language.pr»
                                                       (_root_.GebMirror.Metalogic.«Check.tyArrow»
                                                         x7
                                                         (_root_.GebMirror.Metalogic.«Language.p1» x10))
                                                       (_root_.GebMirror.Metalogic.«Language.mLam»
                                                         x11
                                                         (_root_.GebMirror.Metalogic.«Language.p2» x10)))
                                                   (_root_.GebMirror.Metalogic.«Translation.trTy» x7))
                                           else
                                             _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                         else
                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                       else
                                         if (_root_.Geb.Kernel.Const.eq
                                           x5
                                           (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                           if (_root_.Geb.Kernel.Const.eq
                                             x6
                                             (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                             _root_.GebMirror.Metalogic.«Translation.bindP»
                                               (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                 x9
                                                 (_root_.Geb.Kernel.leaf 0))
                                               (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«Translation.bindP»
                                                   (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                     x9
                                                     (_root_.Geb.Kernel.leaf 1))
                                                   (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«Translation.bindP»
                                                       (_root_.GebMirror.Metalogic.«Translation.kArrowParts»
                                                         (_root_.GebMirror.Metalogic.«Language.p1» x10))
                                                       (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                         if (_root_.Geb.Kernel.Const.equal
                                                           (_root_.GebMirror.Metalogic.«Language.p1» x11)
                                                           (_root_.GebMirror.Metalogic.«Language.p1»
                                                             x12)).label ≠ 0 then
                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                             (_root_.GebMirror.Metalogic.«Language.pr»
                                                               (_root_.GebMirror.Metalogic.«Language.p2» x12)
                                                               (_root_.GebMirror.Metalogic.«Language.app»
                                                                 (_root_.GebMirror.Metalogic.«Language.p2» x10)
                                                                 (_root_.GebMirror.Metalogic.«Language.p2»
                                                                   x11)))
                                                         else
                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»)))
                                           else
                                             _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                         else
                                           if (_root_.Geb.Kernel.Const.eq
                                             x5
                                             (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                             if (_root_.Geb.Kernel.Const.eq
                                               x6
                                               (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                               _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                 (_root_.GebMirror.Metalogic.«Language.pr»
                                                   (_root_.Geb.Kernel.leaf 1)
                                                   _root_.GebMirror.Metalogic.«Language.mStar»)
                                             else
                                               _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                           else
                                             if (_root_.Geb.Kernel.Const.eq
                                               x5
                                               (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                               if (_root_.Geb.Kernel.Const.eq
                                                 x6
                                                 (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                 _root_.GebMirror.Metalogic.«Translation.bindP»
                                                   (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                     x9
                                                     (_root_.Geb.Kernel.leaf 0))
                                                   (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«Translation.bindP»
                                                       (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                         x9
                                                         (_root_.Geb.Kernel.leaf 1))
                                                       (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                         _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                           (_root_.GebMirror.Metalogic.«Language.pr»
                                                             (_root_.GebMirror.Metalogic.«Reader.node2»
                                                               (_root_.Geb.Kernel.leaf 2)
                                                               (_root_.GebMirror.Metalogic.«Language.p1» x10)
                                                               (_root_.GebMirror.Metalogic.«Language.p1» x11))
                                                             (_root_.GebMirror.Metalogic.«Language.mPair»
                                                               (_root_.GebMirror.Metalogic.«Language.p2» x10)
                                                               (_root_.GebMirror.Metalogic.«Language.p2»
                                                                 x11)))))
                                               else
                                                 _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                             else
                                               if (_root_.Geb.Kernel.Const.eq
                                                 x5
                                                 (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                                 if (_root_.Geb.Kernel.Const.eq
                                                   x6
                                                   (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                   _root_.GebMirror.Metalogic.«Translation.bindP»
                                                     (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                       x9
                                                       (_root_.Geb.Kernel.leaf 0))
                                                     (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«Translation.bindP»
                                                         (_root_.GebMirror.Metalogic.«Translation.kProdParts»
                                                           (_root_.GebMirror.Metalogic.«Language.p1» x10))
                                                         (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                             (_root_.GebMirror.Metalogic.«Language.pr»
                                                               (_root_.GebMirror.Metalogic.«Language.p1» x11)
                                                               (_root_.GebMirror.Metalogic.«Language.mFst»
                                                                 (_root_.GebMirror.Metalogic.«Language.p2»
                                                                   x10)))))
                                                 else
                                                   _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                               else
                                                 if (_root_.Geb.Kernel.Const.eq
                                                   x5
                                                   (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                                                   if (_root_.Geb.Kernel.Const.eq
                                                     x6
                                                     (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                     _root_.GebMirror.Metalogic.«Translation.bindP»
                                                       (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                         x9
                                                         (_root_.Geb.Kernel.leaf 0))
                                                       (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                         _root_.GebMirror.Metalogic.«Translation.bindP»
                                                           (_root_.GebMirror.Metalogic.«Translation.kProdParts»
                                                             (_root_.GebMirror.Metalogic.«Language.p1» x10))
                                                           (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                             _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                               (_root_.GebMirror.Metalogic.«Language.pr»
                                                                 (_root_.GebMirror.Metalogic.«Language.p2» x11)
                                                                 (_root_.GebMirror.Metalogic.«Language.mSnd»
                                                                   (_root_.GebMirror.Metalogic.«Language.p2»
                                                                     x10)))))
                                                   else
                                                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                 else
                                                   if (_root_.Geb.Kernel.Const.eq
                                                     x5
                                                     (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                                                     if (_root_.Geb.Kernel.Const.eq
                                                       x6
                                                       (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                       _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                         (_root_.GebMirror.Metalogic.«Language.pr»
                                                           (_root_.Geb.Kernel.leaf 0)
                                                           (_root_.GebMirror.Metalogic.«Translation.quoteT» x7))
                                                     else
                                                       _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                   else
                                                     if (_root_.Geb.Kernel.Const.eq
                                                       x5
                                                       (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                                                       if (_root_.Geb.Kernel.Const.eq
                                                         x6
                                                         (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                         _root_.GebMirror.Metalogic.«Translation.bindP»
                                                           (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                             x9
                                                             (_root_.Geb.Kernel.leaf 0))
                                                           (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                             _root_.GebMirror.Metalogic.«Translation.bindP»
                                                               (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                                 x9
                                                                 (_root_.Geb.Kernel.leaf 1))
                                                               (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                 _root_.GebMirror.Metalogic.«Translation.bindP»
                                                                   (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                                     x9
                                                                     (_root_.Geb.Kernel.leaf 2))
                                                                   (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                                     if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                                       (_root_.Geb.Kernel.Const.equal
                                                                         (_root_.GebMirror.Metalogic.«Language.p1»
                                                                           x10)
                                                                         (_root_.Geb.Kernel.leaf 0))
                                                                       (_root_.Geb.Kernel.Const.equal
                                                                         (_root_.GebMirror.Metalogic.«Language.p1»
                                                                           x12)
                                                                         (_root_.GebMirror.Metalogic.«Language.p1»
                                                                           x11))).label ≠ 0 then
                                                                       _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                         (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                                           _root_.GebMirror.Metalogic.«Language.pr»
                                                                             (_root_.GebMirror.Metalogic.«Language.p1»
                                                                               x11)
                                                                             (_root_.GebMirror.Metalogic.«Translation.condT»
                                                                               x13
                                                                               (_root_.GebMirror.Metalogic.«Translation.labT»
                                                                                 (_root_.GebMirror.Metalogic.«Language.p2»
                                                                                   x10))
                                                                               (_root_.GebMirror.Metalogic.«Language.p2»
                                                                                 x11)
                                                                               (_root_.GebMirror.Metalogic.«Language.p2»
                                                                                 x12)))
                                                                         (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                           (_root_.GebMirror.Metalogic.«Language.p1»
                                                                             x11))
                                                                     else
                                                                       _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»)))
                                                       else
                                                         _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                     else
                                                       if (_root_.Geb.Kernel.Const.eq
                                                         x5
                                                         (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                                                         if (_root_.Geb.Kernel.Const.eq
                                                           x6
                                                           (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                           _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                             (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                               _root_.GebMirror.Metalogic.«Language.pr»
                                                                 (_root_.GebMirror.Metalogic.«Check.foldTy» x7)
                                                                 (_root_.GebMirror.Metalogic.«Translation.foldT»
                                                                   x10))
                                                             (_root_.GebMirror.Metalogic.«Translation.trTy» x7)
                                                         else
                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                       else
                                                         if (_root_.Geb.Kernel.Const.eq
                                                           x5
                                                           (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                                                           if (_root_.Geb.Kernel.Const.eq
                                                             x6
                                                             (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                             _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                               (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                 _root_.GebMirror.Metalogic.«Language.pr»
                                                                   (_root_.GebMirror.Metalogic.«Check.iterTy»
                                                                     x7)
                                                                   (_root_.GebMirror.Metalogic.«Translation.iterT»
                                                                     x10))
                                                               (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                 x7)
                                                           else
                                                             _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                         else
                                                           if (_root_.Geb.Kernel.Const.eq
                                                             x5
                                                             (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                                                             if (_root_.Geb.Kernel.Const.eq
                                                               x6
                                                               (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                               _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                 (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                   _root_.GebMirror.Metalogic.«Language.pr»
                                                                     (_root_.GebMirror.Metalogic.«Check.tyList»
                                                                       x7)
                                                                     (_root_.GebMirror.Metalogic.«Translation.nilT»
                                                                       x10))
                                                                 (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                   x7)
                                                             else
                                                               _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                           else
                                                             if (_root_.Geb.Kernel.Const.eq
                                                               x5
                                                               (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                                                               if (_root_.Geb.Kernel.Const.eq
                                                                 x6
                                                                 (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                                 _root_.GebMirror.Metalogic.«Translation.bindP»
                                                                   (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                                     x9
                                                                     (_root_.Geb.Kernel.leaf 0))
                                                                   (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                     _root_.GebMirror.Metalogic.«Translation.bindP»
                                                                       (_root_.GebMirror.Metalogic.«Translation.trAt»
                                                                         x9
                                                                         (_root_.Geb.Kernel.leaf 1))
                                                                       (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                         _root_.GebMirror.Metalogic.«Translation.bindTy»
                                                                           (_root_.GebMirror.Metalogic.«Translation.kListPart»
                                                                             (_root_.GebMirror.Metalogic.«Language.p1»
                                                                               x11))
                                                                           (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                                             if (_root_.Geb.Kernel.Const.equal
                                                                               (_root_.GebMirror.Metalogic.«Language.p1»
                                                                                 x10)
                                                                               x12).label ≠ 0 then
                                                                               _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                                 (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                                                   _root_.GebMirror.Metalogic.«Language.pr»
                                                                                     (_root_.GebMirror.Metalogic.«Language.p1»
                                                                                       x11)
                                                                                     (_root_.GebMirror.Metalogic.«Translation.consT»
                                                                                       x13
                                                                                       (_root_.GebMirror.Metalogic.«Language.p2»
                                                                                         x10)
                                                                                       (_root_.GebMirror.Metalogic.«Language.p2»
                                                                                         x11)))
                                                                                 (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                                   x12)
                                                                             else
                                                                               _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»)))
                                                               else
                                                                 _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                             else
                                                               if (_root_.Geb.Kernel.Const.eq
                                                                 x5
                                                                 (_root_.Geb.Kernel.leaf 21)).label ≠ 0 then
                                                                 if (_root_.Geb.Kernel.Const.eq
                                                                   x6
                                                                   (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                                   _root_.GebMirror.Metalogic.«Translation.bindTy»
                                                                     (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                       x7)
                                                                     (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                       _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                         (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                           _root_.GebMirror.Metalogic.«Language.pr»
                                                                             (_root_.GebMirror.Metalogic.«Check.foldrTy»
                                                                               x7
                                                                               x8)
                                                                             (_root_.GebMirror.Metalogic.«Translation.foldrT»
                                                                               x10
                                                                               x11))
                                                                         (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                           x8))
                                                                 else
                                                                   _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                               else
                                                                 if (_root_.Geb.Kernel.Const.eq
                                                                   x5
                                                                   (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                                                   if (_root_.Geb.Kernel.Const.eq
                                                                     x6
                                                                     (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                     _root_.GebMirror.Metalogic.«Translation.bindTy»
                                                                       (_root_.GebMirror.Metalogic.«Prelude.nth»
                                                                         _root_.GebMirror.Metalogic.«Check.primTypes»
                                                                         (_root_.Geb.Kernel.Const.label
                                                                           x7))
                                                                       (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                         _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                           (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                             _root_.GebMirror.Metalogic.«Language.pr»
                                                                               x10
                                                                               x11)
                                                                           (_root_.GebMirror.Metalogic.«Translation.primT»
                                                                             (_root_.Geb.Kernel.Const.label
                                                                               x7)))
                                                                   else
                                                                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                                 else
                                                                   if (_root_.Geb.Kernel.Const.eq
                                                                     x5
                                                                     (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
                                                                     if (_root_.Geb.Kernel.Const.eq
                                                                       x6
                                                                       (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                       _root_.GebMirror.Metalogic.«Translation.bindTy»
                                                                         (_root_.GebMirror.Metalogic.«Prelude.nth»
                                                                           x3
                                                                           (_root_.Geb.Kernel.Const.label
                                                                             x7))
                                                                         (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                                                             (_root_.GebMirror.Metalogic.«Language.pr»
                                                                               x10
                                                                               (_root_.GebMirror.Metalogic.«Translation.call»
                                                                                 (_root_.Geb.Kernel.Const.add
                                                                                   (_root_.GebMirror.Metalogic.«$285365712e6c656e677468204c616e67756167652e4c4465666e29»
                                                                                     _root_.GebMirror.Metalogic.«Translation.lib»)
                                                                                   (_root_.Geb.Kernel.Const.label
                                                                                     x7))
                                                                                 ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                                 ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                                                     else
                                                                       _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                                   else
                                                                     if (_root_.Geb.Kernel.Const.eq
                                                                       x5
                                                                       (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                                                                       if (_root_.Geb.Kernel.Const.eq
                                                                         x6
                                                                         (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                                         _root_.GebMirror.Metalogic.«Translation.bindTy»
                                                                           (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                             x7)
                                                                           (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                             _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                               (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                                                 _root_.GebMirror.Metalogic.«Language.pr»
                                                                                   (_root_.GebMirror.Metalogic.«Check.lcaseTy»
                                                                                     x7
                                                                                     x8)
                                                                                   (_root_.GebMirror.Metalogic.«Translation.lcaseT»
                                                                                     x10
                                                                                     x11))
                                                                               (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                                 x8))
                                                                       else
                                                                         _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                                     else
                                                                       if (_root_.Geb.Kernel.Const.eq
                                                                         x5
                                                                         (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                                                                         if (_root_.Geb.Kernel.Const.eq
                                                                           x6
                                                                           (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                           _root_.GebMirror.Metalogic.«Translation.mapTy»
                                                                             (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                               _root_.GebMirror.Metalogic.«Language.pr»
                                                                                 (_root_.GebMirror.Metalogic.«Check.foldTy»
                                                                                   x7)
                                                                                 (_root_.GebMirror.Metalogic.«Translation.paraT»
                                                                                   x10))
                                                                             (_root_.GebMirror.Metalogic.«Translation.trTy»
                                                                               x7)
                                                                         else
                                                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                                                                       else
                                                                         _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x2

def «Translation.term» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Translation.termStep»
      x2
      x0
      x1;
    x3

def «Translation.ktys» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Translation.ldefns» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Translation.trState» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Translation.stTypes» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
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
                                 let x7 : _root_.Geb.Kernel.Tree := x3;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «Translation.stDefns» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
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
                                 let x7 : _root_.Geb.Kernel.Tree := x5;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «$284f7074696f6e2e6e6f7468696e67205472616e736c6174696f6e2e5472537461746529» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a757374205472616e736c6174696f6e2e5472537461746529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Translation.bindSS» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67205472616e736c6174696f6e2e5472537461746529»);
    x2

def «Translation.bindPS» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67205472616e736c6174696f6e2e5472537461746529»);
    x2

def «Translation.mapTS» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374205472616e736c6174696f6e2e5472537461746529»
        (x0 (_root_.GebMirror.Metalogic.«Prelude.get» x1))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67205472616e736c6174696f6e2e5472537461746529»);
    x2

def «$285365712e617070656e64205429» :=
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

def «$285365712e73696e676c65205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$285365712e617070656e64204c616e67756167652e4c4465666e29» :=
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

def «$285365712e73696e676c65204c616e67756167652e4c4465666e29» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Translation.program» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Translation.bindSS»
          x2
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.stTypes» x3;
            let x5 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.stDefns» x3;
            _root_.GebMirror.Metalogic.«Translation.bindPS»
              (_root_.GebMirror.Metalogic.«Translation.term»
                x4
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                x1)
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Translation.mapTS»
                  (fun (x7 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Translation.trState»
                      (_root_.GebMirror.Metalogic.«Translation.ktys»
                        (_root_.GebMirror.Metalogic.«$285365712e617070656e64205429»
                          x4
                          (_root_.GebMirror.Metalogic.«$285365712e73696e676c65205429»
                            (_root_.GebMirror.Metalogic.«Language.p1» x6))))
                      (_root_.GebMirror.Metalogic.«Translation.ldefns»
                        (_root_.GebMirror.Metalogic.«$285365712e617070656e64204c616e67756167652e4c4465666e29»
                          x5
                          (_root_.GebMirror.Metalogic.«$285365712e73696e676c65204c616e67756167652e4c4465666e29»
                            (_root_.GebMirror.Metalogic.«Translation.mkDefn»
                              (_root_.Geb.Kernel.leaf 0)
                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                              x7
                              (_root_.GebMirror.Metalogic.«Language.p2» x6))))))
                  (_root_.GebMirror.Metalogic.«Translation.trTy»
                    (_root_.GebMirror.Metalogic.«Language.p1» x6)))))
      (_root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374205472616e736c6174696f6e2e5472537461746529»
        (_root_.GebMirror.Metalogic.«Translation.trState»
          (_root_.GebMirror.Metalogic.«Translation.ktys»
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          (_root_.GebMirror.Metalogic.«Translation.ldefns»
            ([] : _root_.List _root_.Geb.Kernel.Tree))))
      (_root_.GebMirror.Metalogic.«Prelude.reverse» x0);
    x1

def «$284d61702e6d6170204c616e67756167652e4c4465666e204c616e67756167652e446566696e6974696f6e29» :=
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

def «Translation.trGlobals» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.globals»
      (_root_.GebMirror.Metalogic.«Language.prims» _root_.GebMirror.Metalogic.«Translation.trPrims»)
      (_root_.GebMirror.Metalogic.«Language.defs»
        (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e4c4465666e204c616e67756167652e446566696e6974696f6e29»
          _root_.GebMirror.Metalogic.«Language.defLang»
          (_root_.GebMirror.Metalogic.«$285365712e617070656e64204c616e67756167652e4c4465666e29»
            _root_.GebMirror.Metalogic.«Translation.lib»
            x0)))
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e4f7053696729»
        _root_.GebMirror.Metalogic.«Theory.sig»);
    x1

def «Translation.geqn» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «Translation.gthm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Translation.gthmCtx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
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
                                 let x7 : _root_.Geb.Kernel.Tree := x3;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «Translation.gthmEqn» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                        x5);
    x1

def «Translation.geqnLhs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x5);
    x1

def «Translation.geqnRhs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x7);
    x1

def «$284f7074696f6e2e6e6f7468696e67204c616e67756167652e4f626a7329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a757374204c616e67756167652e4f626a7329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Translation.allSomeObjs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Base.allT»
      _root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e4f626a7329»
        (_root_.GebMirror.Metalogic.«Language.objs»
          (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Prelude.get» x0))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e4f626a7329»);
    x1

def «Translation.bindOH» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e672044657269766174696f6e2e54686d29»);
    x2

def «Translation.bindPH» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e672044657269766174696f6e2e54686d29»);
    x2

def «Translation.mapPH» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a7573742044657269766174696f6e2e54686d29»
                                            (x0 x4)
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e672044657269766174696f6e2e54686d29»);
    x2

def «Translation.thm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.gthmCtx»
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.gthmEqn»
                                          x1;
                                        _root_.GebMirror.Metalogic.«Translation.bindOH»
                                          (_root_.GebMirror.Metalogic.«Translation.allSomeObjs»
                                            (_root_.GebMirror.Metalogic.«Base.mapT»
                                              _root_.GebMirror.Metalogic.«Translation.trTy»
                                              x2))
                                          (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Translation.bindPH»
                                              (_root_.GebMirror.Metalogic.«Translation.term»
                                                x0
                                                x2
                                                (_root_.GebMirror.Metalogic.«Translation.geqnLhs» x3))
                                              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.Metalogic.«Translation.mapPH»
                                                  (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«Derivation.mkThm»
                                                      (_root_.Geb.Kernel.leaf 0)
                                                      x4
                                                      (_root_.GebMirror.Metalogic.«Derivation.terms»
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                      (_root_.GebMirror.Metalogic.«Language.mEq»
                                                        (_root_.GebMirror.Metalogic.«Language.p2» x5)
                                                        (_root_.GebMirror.Metalogic.«Language.p2» x6)))
                                                  (_root_.GebMirror.Metalogic.«Translation.term»
                                                    x0
                                                    x2
                                                    (_root_.GebMirror.Metalogic.«Translation.geqnRhs» x3)))));
    x2

end GebMirror.Metalogic

end
