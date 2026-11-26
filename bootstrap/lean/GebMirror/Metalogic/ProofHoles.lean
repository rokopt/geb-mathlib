module

public import GebMirror.Metalogic.Affine

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «ProofHoles.holeTag» := _root_.Geb.Kernel.leaf 42

def «ProofHoles.mkHole» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      _root_.GebMirror.Metalogic.«ProofHoles.holeTag»
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «ProofHoles.wellFormed» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thArity»
                                          x1;
                                        let x3 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thCtx»
                                          x1;
                                        _root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.GebMirror.Metalogic.«Base.allT»
                                            (_root_.GebMirror.Metalogic.«Language.isTy» x0 x2)
                                            x3)
                                          (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.GebMirror.Metalogic.«Base.allT»
                                              (_root_.GebMirror.Metalogic.«Derivation.isFormula» x0 x2 x3)
                                              (_root_.GebMirror.Metalogic.«Derivation.thHyps» x1))
                                            (_root_.GebMirror.Metalogic.«Derivation.isFormula»
                                              x0
                                              x2
                                              x3
                                              (_root_.GebMirror.Metalogic.«Derivation.thConcl» x1))));
    x2

def «$285365712e7461696c20284c69737420542929» :=
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

def «$2850726f6f66486f6c65732e666f6c64536b6574636820284c69737420542929» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
        _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          x0 (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
        else
          x1 x3 (_root_.GebMirror.Metalogic.«$285365712e7461696c20284c69737420542929» x4))
      x2;
    x3

def «ProofHoles.holes» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$2850726f6f66486f6c65732e666f6c64536b6574636820284c69737420542929»
      _root_.GebMirror.Metalogic.«Prelude.single»
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        _root_.Geb.Kernel.Const.foldr
          (α := _root_.List _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Prelude.append»
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x2)
      x0;
    x1

def «ProofHoles.shaped» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x1)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          _root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.arity x1)
            (_root_.Geb.Kernel.leaf 1)
        else
          _root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.lt
              (_root_.Geb.Kernel.Const.label x1)
              _root_.GebMirror.Metalogic.«ProofHoles.holeTag»)
            (_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.Geb.Kernel.Const.lt
                (_root_.Geb.Kernel.leaf 0)
                (_root_.Geb.Kernel.Const.arity x1))
              (_root_.GebMirror.Metalogic.«Base.allT»
                (fun (x3 : _root_.Geb.Kernel.Tree) => x3)
                (_root_.GebMirror.Metalogic.«Prelude.tail» x2))))
      x0;
    x1

def «ProofHoles.rootRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
      _root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 18)
        (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.Geb.Kernel.leaf 0))
    else
      _root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0))));
    x1

def «ProofHoles.holeChecks» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x3 : _root_.Geb.Kernel.Tree)
                                           (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                           (_ : _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x7 : _root_.Geb.Kernel.Tree) =>
      if (x3).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«ProofHoles.wellFormed» x0 x2)
          (_root_.Geb.Kernel.Const.equal
            x2
            (_root_.GebMirror.Metalogic.«Derivation.mkThm»
              x1
              (_root_.GebMirror.Metalogic.«Language.objs» x4)
              (_root_.GebMirror.Metalogic.«Derivation.terms» x6)
              x7))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x3

def «$285365712e7461696c20284172726f77205420284172726f7720284c69737420542920284172726f77205420284172726f7720284c69737420542920284172726f7720542054292929292929» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$2850726f6f66486f6c65732e666f6c64536b6574636820284172726f77205420284172726f7720284c69737420542920284172726f77205420284172726f7720284c69737420542920284172726f7720542054292929292929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          x0 (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
        else
          x1
            x3
            (_root_.GebMirror.Metalogic.«$285365712e7461696c20284172726f77205420284172726f7720284c69737420542920284172726f77205420284172726f7720284c69737420542920284172726f7720542054292929292929»
              x4))
      x2;
    x3

def «ProofHoles.run» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$2850726f6f66486f6c65732e666f6c64536b6574636820284172726f77205420284172726f7720284c69737420542920284172726f77205420284172726f7720284c69737420542920284172726f7720542054292929292929»
      (fun (x6 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«ProofHoles.holeChecks» x0 x3 (x4 x6))
      (fun (x6 : _root_.Geb.Kernel.Tree)
         (x7 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        _root_.GebMirror.Metalogic.«Conversion.convStep»
          x0
          x1
          x2
          x3
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.Const.label x6)
            ((_root_.Geb.Kernel.Const.child x6 (_root_.Geb.Kernel.leaf 0)) ::
              (_root_.GebMirror.Metalogic.«Base.mapT»
                _root_.GebMirror.Metalogic.«ProofHoles.rootRule»
                (_root_.GebMirror.Metalogic.«Prelude.tail»
                  (_root_.Geb.Kernel.Const.children x6)))))
          ((fun (_ : _root_.Geb.Kernel.Tree)
              (_ : _root_.List _root_.Geb.Kernel.Tree)
              (_ : _root_.Geb.Kernel.Tree)
              (_ : _root_.List _root_.Geb.Kernel.Tree)
              (_ : _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.leaf 0) ::
            x7))
      x5;
    x6

def «ProofHoles.checks» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«ProofHoles.shaped» x5)
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«ProofHoles.wellFormed» x0 x4)
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Base.allT»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«ProofHoles.wellFormed» x0 (x3 x6))
            (_root_.GebMirror.Metalogic.«ProofHoles.holes» x5))
          (_root_.GebMirror.Metalogic.«ProofHoles.run»
            x0
            x1
            x2
            (_root_.GebMirror.Metalogic.«Derivation.thArity» x4)
            x3
            x5
            (_root_.Geb.Kernel.leaf 1)
            (_root_.GebMirror.Metalogic.«Derivation.thCtx» x4)
            (_root_.Geb.Kernel.leaf 0)
            (_root_.GebMirror.Metalogic.«Derivation.thHyps» x4)
            (_root_.GebMirror.Metalogic.«Derivation.thConcl» x4))));
    x6

def «ProofHoles.checkSketch» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«ProofHoles.checks»
      x0
      x1
      x2
      x3
      x4
      x5).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Metalogic.«Base.mapT»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              _root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (x6 :: (_root_.GebMirror.Metalogic.«Prelude.single» (x3 x6))))
            (_root_.GebMirror.Metalogic.«ProofHoles.holes» x5)))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x6

def «$285365712e7461696c205429» :=
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

def «$2850726f6f66486f6c65732e666f6c64536b65746368205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          x0 (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
        else
          x1 x3 (_root_.GebMirror.Metalogic.«$285365712e7461696c205429» x4))
      x2;
    x3

def «ProofHoles.graft» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$2850726f6f66486f6c65732e666f6c64536b65746368205429»
      x0
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.Const.label x2)
          ((_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0)) :: x3))
      x1;
    x2

def «ProofHoles.fill» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«ProofHoles.checks» x0 x1 x2 x3 x4 x5)
      (_root_.GebMirror.Metalogic.«Base.allT»
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«ProofHoles.checks» x0 x1 x2 x6 (x3 x8) (x7 x8))
        (_root_.GebMirror.Metalogic.«ProofHoles.holes» x5))).label ≠ 0 then
      let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«ProofHoles.graft»
        x7
        x5;
      if (_root_.GebMirror.Metalogic.«ProofHoles.checks»
        x0
        x1
        x2
        x6
        x4
        x8).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some» x8
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x8

def «ProofHoles.finish» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Base.isEmpty» (_root_.GebMirror.Metalogic.«ProofHoles.holes» x5))
      (_root_.GebMirror.Metalogic.«ProofHoles.checks» x0 x1 x2 x3 x4 x5)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some» x5
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x6

def «HoleConditions.theoremAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.mkThm»
      x0
      (_root_.GebMirror.Metalogic.«Language.objs» x1)
      (_root_.GebMirror.Metalogic.«Derivation.terms» x2)
      x3;
    x4

def «HoleConditions.hypAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 21)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «HoleConditions.applyAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 27)
      (_root_.GebMirror.Metalogic.«Theory.l3»
        x0
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x1)
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x2))
      x3;
    x4

def «HoleConditions.condition» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Language.mDefn»
          (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 3))
          (_root_.GebMirror.Metalogic.«Prelude.single» x2)
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Language.mLam» x2 x3)))
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Tactics.impL» x0)
        (_root_.GebMirror.Metalogic.«Derivation.thConcl» x1)
        (_root_.GebMirror.Metalogic.«Derivation.thHyps» x1))
      (_root_.GebMirror.Metalogic.«Prelude.reverse»
        (_root_.GebMirror.Metalogic.«Derivation.thCtx» x1));
    x2

def «HoleConditions.hypothesis» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapO»
      _root_.GebMirror.Metalogic.«HoleConditions.hypAt»
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal x1 x2).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
          else
            _root_.GebMirror.Metalogic.«Base.mapO»
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 1))
              x3)
        _root_.GebMirror.Metalogic.«Prelude.none»
        x0);
    x2

def «HoleConditions.proved» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1);
    x2

def «HoleConditions.specializeAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                          x3
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                          x4
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                            x4
                                            (_root_.Geb.Kernel.leaf 1))
                                          (_root_.Geb.Kernel.leaf 0);
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.GebMirror.Metalogic.«Language.mIs»
                                            (_root_.Geb.Kernel.leaf 11)
                                            (_root_.Geb.Kernel.leaf 1)
                                            x4)
                                          (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x4
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.Geb.Kernel.Const.add
                                                x0
                                                (_root_.Geb.Kernel.leaf 3)))
                                            (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.arity
                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 1)))
                                                (_root_.Geb.Kernel.leaf 1))
                                              (_root_.GebMirror.Metalogic.«Language.mIs»
                                                (_root_.Geb.Kernel.leaf 5)
                                                (_root_.Geb.Kernel.leaf 1)
                                                x5)))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prelude.some»
                                            (_root_.GebMirror.Metalogic.«HoleConditions.proved»
                                              (_root_.GebMirror.Metalogic.«Language.subst»
                                                (_root_.GebMirror.Metalogic.«Language.mArg»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Derivation.instVar» x2))
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 24)
                                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                                  (_root_.GebMirror.Metalogic.«Language.app» x5 x2))
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 3)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                  (_root_.GebMirror.Metalogic.«HoleConditions.applyAt»
                                                    (_root_.Geb.Kernel.Const.add
                                                      x1
                                                      (_root_.Geb.Kernel.leaf 5))
                                                    (_root_.GebMirror.Metalogic.«Prelude.single» x6)
                                                    (_root_.GebMirror.Metalogic.«Theory.l2» x2 x5)
                                                    (_root_.GebMirror.Metalogic.«Prelude.single»
                                                      (_root_.Geb.Kernel.Const.child
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 1)))))))
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

def «HoleConditions.specialize» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.condition»
                                          x0
                                          x3;
                                        _root_.GebMirror.Metalogic.«Base.bindO»
                                          (_root_.GebMirror.Metalogic.«HoleConditions.hypothesis» x2 x5)
                                          (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Base.mapO»
                                              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                                _root_.Geb.Kernel.Const.child
                                                  x7
                                                  (_root_.Geb.Kernel.leaf 1))
                                              (_root_.GebMirror.Metalogic.«HoleConditions.specializeAt»
                                                x0
                                                x1
                                                x4
                                                (_root_.GebMirror.Metalogic.«HoleConditions.proved» x5 x6))));
    x5

def «HoleConditions.applyCondition» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                          x4
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                          x5
                                          (_root_.Geb.Kernel.leaf 0);
                                        if (_root_.Geb.Kernel.Const.equal
                                          x5
                                          (_root_.GebMirror.Metalogic.«Tactics.impL» x0 x3 x6)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Base.mapO»
                                            (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«HoleConditions.proved»
                                                x6
                                                (_root_.GebMirror.Metalogic.«HoleConditions.applyAt»
                                                  (_root_.Geb.Kernel.Const.add
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 4))
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (_root_.GebMirror.Metalogic.«Theory.l2» x6 x3)
                                                  (_root_.GebMirror.Metalogic.«Theory.l2»
                                                    (_root_.Geb.Kernel.Const.child
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    x7)))
                                            (_root_.GebMirror.Metalogic.«HoleConditions.hypothesis» x2 x3)
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x5

def «HoleConditions.discharge» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
                                          x2
                                          (_root_.GebMirror.Metalogic.«Derivation.thHyps» x3);
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.condition»
                                          x0
                                          x3;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapO»
                                          (_root_.GebMirror.Metalogic.«HoleConditions.proved» x5)
                                          (_root_.GebMirror.Metalogic.«HoleConditions.hypothesis» x4 x5);
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Base.bindO»
                                              x8
                                              (_root_.GebMirror.Metalogic.«HoleConditions.specializeAt»
                                                x0
                                                x1
                                                (_root_.GebMirror.Metalogic.«Language.var» x7)))
                                          x6
                                          (_root_.GebMirror.Metalogic.«Base.range»
                                            (_root_.GebMirror.Metalogic.«Prelude.length»
                                              (_root_.GebMirror.Metalogic.«Derivation.thCtx» x3)));
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          (fun (x8 : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Base.bindO»
                                              x9
                                              (_root_.GebMirror.Metalogic.«HoleConditions.applyCondition»
                                                x0
                                                x1
                                                x4
                                                x8))
                                          x7
                                          (_root_.GebMirror.Metalogic.«Prelude.reverse»
                                            (_root_.GebMirror.Metalogic.«Derivation.thHyps» x3));
                                        _root_.GebMirror.Metalogic.«Base.bindO»
                                          x8
                                          (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                            if (_root_.Geb.Kernel.Const.equal
                                              (_root_.Geb.Kernel.Const.child
                                                x9
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.GebMirror.Metalogic.«Derivation.thConcl»
                                                x3)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prelude.some»
                                                (_root_.Geb.Kernel.Const.child
                                                  x9
                                                  (_root_.Geb.Kernel.leaf 1))
                                            else
                                              _root_.GebMirror.Metalogic.«Prelude.none»));
    x4

def «HoleConditions.baseData» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 17))
      (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 21))).label ≠ 0 then
      ((_root_.Geb.Kernel.Const.add
        x0
        (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))) ::
        (_root_.GebMirror.Metalogic.«Prelude.tail» x2))
    else
      x2);
    x3

def «HoleConditions.shiftNorm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x2
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 0)
                                                (_root_.GebMirror.Metalogic.«HoleConditions.baseData»
                                                  x0
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 0))
                                                  (_root_.Geb.Kernel.Const.children
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 1))))))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                            _root_.Geb.Kernel.Const.node
                                              (_root_.Geb.Kernel.leaf 6)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.Geb.Kernel.Const.add
                                                  x0
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 0))))
                                          else
                                            x1);
    x2

def «HoleConditions.shifted» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x1;
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          (_root_.Geb.Kernel.Const.child
                                            x1
                                            (_root_.Geb.Kernel.leaf 0));
                                        let x5 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree := (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                          _root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Base.mapT»
                                              (_root_.GebMirror.Metalogic.«HoleConditions.shiftNorm» x0)
                                              (_root_.Geb.Kernel.Const.children x5)));
                                        _root_.GebMirror.Metalogic.«Prover.dNode»
                                          x3
                                          (if (_root_.GebMirror.Metalogic.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 37))
                                            (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 38))).label ≠ 0 then
                                            ((x5
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x4
                                                (_root_.Geb.Kernel.leaf 0))) ::
                                              (_root_.GebMirror.Metalogic.«Prelude.tail» x4))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 41)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prelude.append»
                                                (_root_.GebMirror.Metalogic.«Base.take»
                                                  (_root_.Geb.Kernel.leaf 5)
                                                  x4)
                                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                                  (x5
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 5))))
                                            else
                                              _root_.GebMirror.Metalogic.«HoleConditions.baseData» x0 x3 x4)
                                          x2);
    x3

def «HoleConditions.shiftTree» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«HoleConditions.shifted»
          x0
          x2
          (_root_.GebMirror.Metalogic.«Prelude.tail» x3))
      x1;
    x2

def «HoleConditions.implyFrom» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (x6 : _root_.Geb.Kernel.Tree) (x7 : _root_.Geb.Kernel.Tree) =>
          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at» x3 x6;
          _root_.GebMirror.Metalogic.«HoleConditions.proved»
            (_root_.GebMirror.Metalogic.«Tactics.impL»
              x0
              x8
              (_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 0)))
            (_root_.GebMirror.Metalogic.«Tactics.impI»
              x1
              (_root_.Geb.Kernel.Const.add x2 x6)
              x8
              (_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 0))
              (_root_.Geb.Kernel.Const.child x7 (_root_.Geb.Kernel.leaf 1))))
        (_root_.GebMirror.Metalogic.«HoleConditions.proved» x4 x5)
        (_root_.GebMirror.Metalogic.«Base.range» (_root_.GebMirror.Metalogic.«Prelude.length» x3)))
      (_root_.Geb.Kernel.leaf 1);
    x6

def «HoleConditions.allIntro» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                          (_root_.Geb.Kernel.leaf 3)
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          ([] : _root_.List _root_.Geb.Kernel.Tree);
                                        _root_.GebMirror.Metalogic.«Prover.dNode»
                                          (_root_.Geb.Kernel.leaf 23)
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (_root_.GebMirror.Metalogic.«Theory.l2»
                                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                                              (_root_.Geb.Kernel.leaf 8)
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              ([] : _root_.List _root_.Geb.Kernel.Tree))
                                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                                              (_root_.Geb.Kernel.leaf 26)
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                  (_root_.Geb.Kernel.leaf 23)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (_root_.GebMirror.Metalogic.«Theory.l2»
                                                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                      (_root_.Geb.Kernel.leaf 2)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x1))
                                                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                      (_root_.Geb.Kernel.leaf 25)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (_root_.GebMirror.Metalogic.«Theory.l2»
                                                        _root_.GebMirror.Metalogic.«Tactics.trueI»
                                                        x0))))))));
    x1

def «HoleConditions.close» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«HoleConditions.allIntro»
      (_root_.GebMirror.Metalogic.«HoleConditions.implyFrom»
        x0
        x1
        (_root_.Geb.Kernel.Const.add
          (_root_.GebMirror.Metalogic.«Prelude.length» x2)
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.GebMirror.Metalogic.«Derivation.thCtx» x3)))
        (_root_.GebMirror.Metalogic.«Derivation.thHyps» x3)
        (_root_.GebMirror.Metalogic.«Derivation.thConcl» x3)
        x4)
      (_root_.GebMirror.Metalogic.«Prelude.length»
        (_root_.GebMirror.Metalogic.«Derivation.thCtx» x3));
    x5

def «HoleConditions.bodyAssumptions» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
      x1
      (_root_.GebMirror.Metalogic.«Prelude.replicate»
        (_root_.GebMirror.Metalogic.«Prelude.length»
          (_root_.GebMirror.Metalogic.«Derivation.thCtx» x2))
        (_root_.GebMirror.Metalogic.«Tactics.ttL» x0));
    x3

def «HoleConditions.conditional» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
      (_root_.GebMirror.Metalogic.«Derivation.thArity» x2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Tactics.impL» x0)
        (_root_.GebMirror.Metalogic.«HoleConditions.condition» x0 x2)
        (_root_.GebMirror.Metalogic.«Base.mapT»
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«HoleConditions.condition» x0 (x1 x4))
          (_root_.GebMirror.Metalogic.«ProofHoles.holes» x3)));
    x4

def «$285365712e7461696c20284172726f7720284c69737420542920542929» :=
  fun (x0 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$2850726f6f66486f6c65732e666f6c64536b6574636820284172726f7720284c69737420542920542929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List
        (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          x0 (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
        else
          x1
            x3
            (_root_.GebMirror.Metalogic.«$285365712e7461696c20284172726f7720284c69737420542920542929»
              x4))
      x2;
    x3

def «$284d61702e6d617020284172726f7720284c697374205429205429205429» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree) →
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «HoleConditions.direct» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$2850726f6f66486f6c65732e666f6c64536b6574636820284172726f7720284c69737420542920542929»
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«HoleConditions.discharge» x0 x1 x5 (x2 x4))
      (fun (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List
           (_root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x4;
        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length» x6;
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 36) x7)
          (_root_.GebMirror.Metalogic.«Base.not»
            (_root_.Geb.Kernel.Const.eq
              x7
              (_root_.Geb.Kernel.leaf 39)))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.GebMirror.Metalogic.«HoleConditions.shifted»
              x8
              x4
              ([] : _root_.List _root_.Geb.Kernel.Tree))
        else
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x9 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«HoleConditions.shifted»
                x8
                x4
                (_root_.Geb.Kernel.Const.children x9))
            (_root_.GebMirror.Metalogic.«Base.allSomeT»
              (_root_.GebMirror.Metalogic.«$284d61702e6d617020284172726f7720284c697374205429205429205429»
                (fun (x9 : _root_.List _root_.Geb.Kernel.Tree →
                     _root_.Geb.Kernel.Tree) =>
                  x9
                    (if (_root_.Geb.Kernel.Const.eq
                      x7
                      (_root_.Geb.Kernel.leaf 32)).label ≠ 0 then
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                    else
                      x6))
                x5)))
      x3;
    x4

def «HoleConditions.directCertify» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«ProofHoles.checks»
      x0
      x1
      x2
      x5
      x6
      x7).label ≠ 0 then
      let x8 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«HoleConditions.condition» x3 (x5 x8))
        (_root_.GebMirror.Metalogic.«ProofHoles.holes» x7);
      let x9 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
        x8
        (_root_.GebMirror.Metalogic.«Derivation.thHyps» x6);
      let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thConcl»
        x6;
      let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
        (_root_.GebMirror.Metalogic.«Derivation.thArity» x6)
        (_root_.GebMirror.Metalogic.«Derivation.thCtx» x6)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«Tactics.impL» x3)
          x10
          x9);
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«HoleConditions.direct» x3 x4 x5 x7 x8)
        (fun (x12 : _root_.Geb.Kernel.Tree) =>
          let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.implyFrom»
            x3
            x4
            (_root_.Geb.Kernel.leaf 0)
            x9
            x10
            x12;
          if (_root_.GebMirror.Metalogic.«Conversion.thmConvChecks»
            x0
            x1
            x2
            x11
            x13).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» x13
          else
            _root_.GebMirror.Metalogic.«Prelude.none»)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x8

def «HolePlan.rewriting» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HolePlan.proving» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HolePlan.premises» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «HolePlan.proofNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «HolePlan.nodes» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e4e6f64657329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420486f6c65506c616e2e4e6f64657329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HolePlan.proveAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HolePlan.proving»
      (_root_.GebMirror.Metalogic.«HoleConditions.theoremAt» x0 x1 x2 x3);
    x4

def «$284665772e6c3220486f6c65506c616e2e5072656d69736529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$285365712e73696e676c6520486f6c65506c616e2e5072656d69736529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$284d61702e6d6170205420486f6c65506c616e2e5072656d69736529» :=
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

def «$284665772e6c3320486f6c65506c616e2e5072656d69736529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
        x1
        x2));
    x3

def «HolePlan.proofPremises» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x4;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thArity»
                                          x3;
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thCtx»
                                          x3;
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.tail»
                                          x7;
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thHyps»
                                          x3;
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thConcl»
                                          x3;
                                        let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                          x10
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                          x10
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x4
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x4
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                          x7
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x16 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x4;
                                        let x17 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x14;
                                        let x18 : _root_.List
                                          _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
                                          x5
                                          (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.Metalogic.«Prelude.get»
                                              (_root_.GebMirror.Metalogic.«Conversion.applyInst»
                                                x1
                                                x13
                                                x17
                                                x10))
                                        else
                                          _root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                              x4
                                              (_root_.Geb.Kernel.leaf 2)));
                                        let x19 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
                                          x5
                                          (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«HoleConditions.applyAt»
                                            x13
                                            x17
                                            x18
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                        else
                                          x4);
                                        let x20 : _root_.List _root_.Geb.Kernel.Tree →
                                          _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree →
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HolePlan.proveAt»
                                          x6;
                                        _root_.GebMirror.Metalogic.«HolePlan.proofNode»
                                          x3
                                          x19
                                          (_root_.GebMirror.Metalogic.«HolePlan.premises»
                                            (if (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                (x20 x7 x9 x13)
                                                (x20
                                                  x7
                                                  (_root_.GebMirror.Metalogic.«Prelude.append»
                                                    x9
                                                    (_root_.GebMirror.Metalogic.«Prelude.single» x13))
                                                  x10)
                                            else
                                              if (_root_.GebMirror.Metalogic.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 23))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 24))).label ≠ 0 then
                                                let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                                  x16
                                                  (_root_.Geb.Kernel.leaf 0);
                                                _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                  (_root_.GebMirror.Metalogic.«HolePlan.rewriting» x21)
                                                  (x20
                                                    x7
                                                    x9
                                                    (if (_root_.Geb.Kernel.Const.eq
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Prelude.get»
                                                        (_root_.GebMirror.Metalogic.«Conversion.convCheck»
                                                          x0
                                                          x1
                                                          x2
                                                          x6
                                                          x21
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          x7
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          x9
                                                          x10)
                                                    else
                                                      x13))
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 25)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                    (x20
                                                      x7
                                                      (_root_.GebMirror.Metalogic.«Prelude.append»
                                                        x9
                                                        (_root_.GebMirror.Metalogic.«Prelude.single» x11))
                                                      x12)
                                                    (x20
                                                      x7
                                                      (_root_.GebMirror.Metalogic.«Prelude.append»
                                                        x9
                                                        (_root_.GebMirror.Metalogic.«Prelude.single» x12))
                                                      x11)
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 26)).label ≠ 0 then
                                                    let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.expParts»
                                                      (_root_.GebMirror.Metalogic.«Prelude.get»
                                                        (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                                          x0
                                                          x6
                                                          x7
                                                          x11));
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      (_root_.Geb.Kernel.Const.label x21)
                                                      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                      let x22 : _root_.List
                                                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                        x21;
                                                      let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                        (α := _root_.Geb.Kernel.Tree)
                                                        (β := _root_.Geb.Kernel.Tree)
                                                        x22
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        (fun (x23 : _root_.Geb.Kernel.Tree)
                                                           (_ : _root_.List
                                                             _root_.Geb.Kernel.Tree) =>
                                                          x23);
                                                      let _ : _root_.List
                                                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                        (α := _root_.Geb.Kernel.Tree)
                                                        (β := _root_.List _root_.Geb.Kernel.Tree)
                                                        x22
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        (fun (_ : _root_.Geb.Kernel.Tree)
                                                           (x25 : _root_.List
                                                             _root_.Geb.Kernel.Tree) =>
                                                          x25);
                                                      _root_.GebMirror.Metalogic.«$285365712e73696e676c6520486f6c65506c616e2e5072656d69736529»
                                                        (x20
                                                          ((_root_.GebMirror.Metalogic.«Language.p1» x23) :: x7)
                                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                                            _root_.GebMirror.Metalogic.«Derivation.weaken1»
                                                            x9)
                                                          (_root_.GebMirror.Metalogic.«Language.mEq»
                                                            (_root_.GebMirror.Metalogic.«Language.app»
                                                              (_root_.GebMirror.Metalogic.«Derivation.weaken1»
                                                                x11)
                                                              (_root_.GebMirror.Metalogic.«Language.var»
                                                                (_root_.Geb.Kernel.leaf 0)))
                                                            (_root_.GebMirror.Metalogic.«Language.app»
                                                              (_root_.GebMirror.Metalogic.«Derivation.weaken1»
                                                                x12)
                                                              (_root_.GebMirror.Metalogic.«Language.var»
                                                                (_root_.Geb.Kernel.leaf 0)))))
                                                    else
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  else
                                                    if (_root_.GebMirror.Metalogic.«Prelude.or»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x5
                                                        (_root_.Geb.Kernel.leaf 27))
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x5
                                                        (_root_.Geb.Kernel.leaf 39))).label ≠ 0 then
                                                      let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thmAt»
                                                        x1
                                                        x13;
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        (_root_.Geb.Kernel.Const.label x21)
                                                        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                        let x22 : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                          x21;
                                                        let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.Geb.Kernel.Tree)
                                                          x22
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          (fun (x23 : _root_.Geb.Kernel.Tree)
                                                             (_ : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x23);
                                                        let _ : _root_.List
                                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                          (α := _root_.Geb.Kernel.Tree)
                                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                                          x22
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                                             (x25 : _root_.List
                                                               _root_.Geb.Kernel.Tree) =>
                                                            x25);
                                                        _root_.GebMirror.Metalogic.«$284d61702e6d6170205420486f6c65506c616e2e5072656d69736529»
                                                          (fun (x25 : _root_.Geb.Kernel.Tree) =>
                                                            x20
                                                              x7
                                                              x9
                                                              (_root_.GebMirror.Metalogic.«Derivation.instTerm»
                                                                x17
                                                                x18
                                                                x25))
                                                          (_root_.GebMirror.Metalogic.«Derivation.thHyps» x23)
                                                      else
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    else
                                                      if (_root_.GebMirror.Metalogic.«Prelude.or»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 19))
                                                        (_root_.Geb.Kernel.Const.eq
                                                          x5
                                                          (_root_.Geb.Kernel.leaf 28))).label ≠ 0 then
                                                        let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.lowerHyps»
                                                          x0
                                                          x6
                                                          x8
                                                          x9;
                                                        if (_root_.Geb.Kernel.Const.eq
                                                          (_root_.Geb.Kernel.Const.label x21)
                                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                          let x22 : _root_.List
                                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                            x21;
                                                          let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                            (α := _root_.Geb.Kernel.Tree)
                                                            (β := _root_.Geb.Kernel.Tree)
                                                            x22
                                                            (_root_.Geb.Kernel.leaf 0)
                                                            (fun (x23 : _root_.Geb.Kernel.Tree)
                                                               (_ : _root_.List
                                                                 _root_.Geb.Kernel.Tree) =>
                                                              x23);
                                                          let _ : _root_.List
                                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                            (α := _root_.Geb.Kernel.Tree)
                                                            (β := _root_.List
                                                              _root_.Geb.Kernel.Tree)
                                                            x22
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                                               (x25 : _root_.List
                                                                 _root_.Geb.Kernel.Tree) =>
                                                              x25);
                                                          let x25 : _root_.Geb.Kernel.Tree →
                                                            _root_.Geb.Kernel.Tree := (fun (x25 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.Metalogic.«Language.subst»
                                                              x25
                                                              (_root_.GebMirror.Metalogic.«Derivation.instVar»
                                                                (_root_.GebMirror.Metalogic.«Language.mArr»
                                                                  x13
                                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                  _root_.GebMirror.Metalogic.«Language.mStar»)));
                                                          let x26 : _root_.Geb.Kernel.Tree →
                                                            _root_.Geb.Kernel.Tree := (fun (x26 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.Metalogic.«Language.mEq»
                                                              (_root_.GebMirror.Metalogic.«Derivation.natSuccAt»
                                                                x14
                                                                x26)
                                                              (_root_.GebMirror.Metalogic.«Language.subst»
                                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                                  x4
                                                                  (_root_.Geb.Kernel.leaf 2))
                                                                (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                                                  x26)));
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
                                                            _root_.GebMirror.Metalogic.«$284665772e6c3320486f6c65506c616e2e5072656d69736529»
                                                              (x20
                                                                x8
                                                                (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                                  x23)
                                                                (_root_.GebMirror.Metalogic.«Language.mEq»
                                                                  (x25 x11)
                                                                  (x25 x12)))
                                                              (x20 x7 x9 (x26 x11))
                                                              (x20 x7 x9 (x26 x12))
                                                          else
                                                            _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                              (x20
                                                                x8
                                                                (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                                  x23)
                                                                (x25 x10))
                                                              (x20
                                                                x7
                                                                (_root_.GebMirror.Metalogic.«Prelude.append»
                                                                  x9
                                                                  (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                    x10))
                                                                (_root_.GebMirror.Metalogic.«Derivation.natSuccAt»
                                                                  x14
                                                                  x10))
                                                        else
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      else
                                                        if (_root_.GebMirror.Metalogic.«Prelude.or»
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 20))
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 29))).label ≠ 0 then
                                                          let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.lowerHyps»
                                                            x0
                                                            x6
                                                            x8
                                                            x9;
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            (_root_.Geb.Kernel.Const.label x21)
                                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                            let x22 : _root_.List
                                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                              x21;
                                                            let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                              (α := _root_.Geb.Kernel.Tree)
                                                              (β := _root_.Geb.Kernel.Tree)
                                                              x22
                                                              (_root_.Geb.Kernel.leaf 0)
                                                              (fun (x23 : _root_.Geb.Kernel.Tree)
                                                                 (_ : _root_.List
                                                                   _root_.Geb.Kernel.Tree) =>
                                                                x23);
                                                            let _ : _root_.List
                                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                              (α := _root_.Geb.Kernel.Tree)
                                                              (β := _root_.List
                                                                _root_.Geb.Kernel.Tree)
                                                              x22
                                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                                 (x25 : _root_.List
                                                                   _root_.Geb.Kernel.Tree) =>
                                                                x25);
                                                            let x25 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get»
                                                              (_root_.GebMirror.Metalogic.«Language.listPart»
                                                                x15);
                                                            let x26 : _root_.List
                                                              _root_.Geb.Kernel.Tree := (x15 ::
                                                              (x25 :: x8));
                                                            let x27 : _root_.List
                                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
                                                              _root_.GebMirror.Metalogic.«Derivation.weaken2»
                                                              (_root_.GebMirror.Metalogic.«Prover.termsOf» x23);
                                                            let x28 : _root_.Geb.Kernel.Tree →
                                                              _root_.Geb.Kernel.Tree := (fun (x28 : _root_.Geb.Kernel.Tree) =>
                                                              _root_.GebMirror.Metalogic.«Language.subst»
                                                                x28
                                                                (_root_.GebMirror.Metalogic.«Derivation.instVar»
                                                                  (_root_.GebMirror.Metalogic.«Language.mArr»
                                                                    x13
                                                                    (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                      x25)
                                                                    _root_.GebMirror.Metalogic.«Language.mStar»)));
                                                            let x29 : _root_.Geb.Kernel.Tree →
                                                              _root_.Geb.Kernel.Tree := (fun (x29 : _root_.Geb.Kernel.Tree) =>
                                                              _root_.GebMirror.Metalogic.«Language.mEq»
                                                                (_root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                                                  x14
                                                                  x25
                                                                  x29)
                                                                (_root_.GebMirror.Metalogic.«Language.subst»
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x4
                                                                    (_root_.Geb.Kernel.leaf 2))
                                                                  (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                                                    (_root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                                                      x29))));
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                                                              _root_.GebMirror.Metalogic.«$284665772e6c3320486f6c65506c616e2e5072656d69736529»
                                                                (x20
                                                                  x8
                                                                  (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                                    x23)
                                                                  (_root_.GebMirror.Metalogic.«Language.mEq»
                                                                    (x28 x11)
                                                                    (x28 x12)))
                                                                (x20 x26 x27 (x29 x11))
                                                                (x20 x26 x27 (x29 x12))
                                                            else
                                                              _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                                (x20
                                                                  x8
                                                                  (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                                    x23)
                                                                  (x28 x10))
                                                                (x20
                                                                  x26
                                                                  (_root_.GebMirror.Metalogic.«Prelude.append»
                                                                    x27
                                                                    (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                      (_root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                                                        x10)))
                                                                  (_root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                                                    x14
                                                                    x25
                                                                    x10))
                                                          else
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        else
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 34)).label ≠ 0 then
                                                            let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.coprodParts»
                                                              x15;
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              (_root_.Geb.Kernel.Const.label x21)
                                                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                              let x22 : _root_.List
                                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                x21;
                                                              let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                (α := _root_.Geb.Kernel.Tree)
                                                                (β := _root_.Geb.Kernel.Tree)
                                                                x22
                                                                (_root_.Geb.Kernel.leaf 0)
                                                                (fun (x23 : _root_.Geb.Kernel.Tree)
                                                                   (_ : _root_.List
                                                                     _root_.Geb.Kernel.Tree) =>
                                                                  x23);
                                                              let _ : _root_.List
                                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                (α := _root_.Geb.Kernel.Tree)
                                                                (β := _root_.List
                                                                  _root_.Geb.Kernel.Tree)
                                                                x22
                                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                (fun (_ : _root_.Geb.Kernel.Tree)
                                                                   (x25 : _root_.List
                                                                     _root_.Geb.Kernel.Tree) =>
                                                                  x25);
                                                              let x25 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1»
                                                                x23;
                                                              let x26 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p2»
                                                                x23;
                                                              let x27 : _root_.Geb.Kernel.Tree →
                                                                _root_.Geb.Kernel.Tree := (fun (x27 : _root_.Geb.Kernel.Tree) =>
                                                                _root_.GebMirror.Metalogic.«Language.subst»
                                                                  x10
                                                                  (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                                                    (_root_.GebMirror.Metalogic.«Language.mArr»
                                                                      x27
                                                                      (_root_.GebMirror.Metalogic.«Theory.l2»
                                                                        x25
                                                                        x26)
                                                                      (_root_.GebMirror.Metalogic.«Language.var»
                                                                        (_root_.Geb.Kernel.leaf 0)))));
                                                              _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                                (x20 (x25 :: x8) x9 (x27 x13))
                                                                (x20 (x26 :: x8) x9 (x27 x14))
                                                            else
                                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          else
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 36)).label ≠ 0 then
                                                              let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66204c616e67756167652e5072696d697469766529»
                                                                (_root_.GebMirror.Metalogic.«Language.gPrims»
                                                                  x0)
                                                                x13;
                                                              if (_root_.Geb.Kernel.Const.eq
                                                                (_root_.Geb.Kernel.Const.label x21)
                                                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                let x22 : _root_.List
                                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                  x21;
                                                                let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                  (α := _root_.Geb.Kernel.Tree)
                                                                  (β := _root_.Geb.Kernel.Tree)
                                                                  x22
                                                                  (_root_.Geb.Kernel.leaf 0)
                                                                  (fun (x23 : _root_.Geb.Kernel.Tree)
                                                                     (_ : _root_.List
                                                                       _root_.Geb.Kernel.Tree) =>
                                                                    x23);
                                                                let _ : _root_.List
                                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                  (α := _root_.Geb.Kernel.Tree)
                                                                  (β := _root_.List
                                                                    _root_.Geb.Kernel.Tree)
                                                                  x22
                                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                                     (x25 : _root_.List
                                                                       _root_.Geb.Kernel.Tree) =>
                                                                    x25);
                                                                _root_.GebMirror.Metalogic.«$285365712e73696e676c6520486f6c65506c616e2e5072656d69736529»
                                                                  (x20
                                                                    ((_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
                                                                      x17
                                                                      (_root_.GebMirror.Metalogic.«Language.prDom»
                                                                        x23)) ::
                                                                      x8)
                                                                    x9
                                                                    (_root_.GebMirror.Metalogic.«Language.subst»
                                                                      x10
                                                                      (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                                                        (_root_.GebMirror.Metalogic.«Language.mArr»
                                                                          x13
                                                                          x17
                                                                          (_root_.GebMirror.Metalogic.«Language.var»
                                                                            (_root_.Geb.Kernel.leaf 0))))))
                                                              else
                                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                            else
                                                              if (_root_.Geb.Kernel.Const.eq
                                                                x5
                                                                (_root_.Geb.Kernel.leaf 32)).label ≠ 0 then
                                                                let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get»
                                                                  (_root_.GebMirror.Metalogic.«Language.roseLabel»
                                                                    x15);
                                                                let x22 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get»
                                                                  (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                                                    x0
                                                                    x6
                                                                    x7
                                                                    x11);
                                                                let x23 : _root_.Geb.Kernel.Tree →
                                                                  _root_.Geb.Kernel.Tree := (fun (x23 : _root_.Geb.Kernel.Tree) =>
                                                                  x20
                                                                    (_root_.GebMirror.Metalogic.«Theory.l2»
                                                                      (_root_.GebMirror.Metalogic.«Theory.list»
                                                                        x15)
                                                                      x21)
                                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                    (_root_.GebMirror.Metalogic.«Language.mEq»
                                                                      (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt»
                                                                        x13
                                                                        x15
                                                                        x21
                                                                        x23)
                                                                      (_root_.GebMirror.Metalogic.«Language.subst»
                                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                                          x4
                                                                          (_root_.Geb.Kernel.leaf 3))
                                                                        (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                                                          (_root_.GebMirror.Metalogic.«Derivation.roseMapAt»
                                                                            x14
                                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                                              x4
                                                                              (_root_.Geb.Kernel.leaf 2))
                                                                            x22
                                                                            x23)))));
                                                                _root_.GebMirror.Metalogic.«$284665772e6c3220486f6c65506c616e2e5072656d69736529»
                                                                  (x23 x11)
                                                                  (x23 x12)
                                                              else
                                                                if (_root_.Geb.Kernel.Const.eq
                                                                  x5
                                                                  (_root_.Geb.Kernel.leaf 33)).label ≠ 0 then
                                                                  let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.lowerHyps»
                                                                    x0
                                                                    x6
                                                                    x8
                                                                    x9;
                                                                  if (_root_.Geb.Kernel.Const.eq
                                                                    (_root_.Geb.Kernel.Const.label
                                                                      x21)
                                                                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                                    let x22 : _root_.List
                                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                      x21;
                                                                    let x23 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                      (α := _root_.Geb.Kernel.Tree)
                                                                      (β := _root_.Geb.Kernel.Tree)
                                                                      x22
                                                                      (_root_.Geb.Kernel.leaf 0)
                                                                      (fun (x23 : _root_.Geb.Kernel.Tree)
                                                                         (_ : _root_.List
                                                                           _root_.Geb.Kernel.Tree) =>
                                                                        x23);
                                                                    let _ : _root_.List
                                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                                      (α := _root_.Geb.Kernel.Tree)
                                                                      (β := _root_.List
                                                                        _root_.Geb.Kernel.Tree)
                                                                      x22
                                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                      (fun (_ : _root_.Geb.Kernel.Tree)
                                                                         (x25 : _root_.List
                                                                           _root_.Geb.Kernel.Tree) =>
                                                                        x25);
                                                                    let x25 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get»
                                                                      (_root_.GebMirror.Metalogic.«Language.roseLabel»
                                                                        x15);
                                                                    _root_.GebMirror.Metalogic.«$285365712e73696e676c6520486f6c65506c616e2e5072656d69736529»
                                                                      (x20
                                                                        ((_root_.GebMirror.Metalogic.«Theory.list»
                                                                          x15) ::
                                                                          (x25 :: x8))
                                                                        (_root_.GebMirror.Metalogic.«Prelude.append»
                                                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                                                            _root_.GebMirror.Metalogic.«Derivation.weaken2»
                                                                            (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                                              x23))
                                                                          (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                            (_root_.GebMirror.Metalogic.«Derivation.roseHyp»
                                                                              x14
                                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                                x4
                                                                                (_root_.Geb.Kernel.leaf 2))
                                                                              x10)))
                                                                        (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt»
                                                                          x13
                                                                          x15
                                                                          x25
                                                                          x10))
                                                                  else
                                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                else
                                                                  _root_.GebMirror.Metalogic.«$284d61702e6d6170205420486f6c65506c616e2e5072656d69736529»
                                                                    _root_.GebMirror.Metalogic.«HolePlan.rewriting»
                                                                    x16)));
    x5

def «$285365712e617070656e6420486f6c65506c616e2e50726f6f664e6f646529» :=
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

def «HolePlan.appendNodes» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
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
                                          let x6 : _root_.Geb.Kernel.Tree := x4;
                                          let x7 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
                                          let x8 : _root_.List _root_.Geb.Kernel.Tree := x7;
                                          let x9 : _root_.Geb.Kernel.Tree := x1;
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x9)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x10 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x9;
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
                                            let x13 : _root_.Geb.Kernel.Tree := x11;
                                            let x14 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x13;
                                            let x15 : _root_.List _root_.Geb.Kernel.Tree := x14;
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c65506c616e2e4e6f64657329»
                                              (_root_.GebMirror.Metalogic.«HolePlan.nodes»
                                                (_root_.GebMirror.Metalogic.«$285365712e617070656e6420486f6c65506c616e2e50726f6f664e6f646529»
                                                  x8
                                                  x15))
                                          else
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e4e6f64657329»
                                        else
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e4e6f64657329»);
    x2

def «$28456163682e6973456d70747920486f6c65506c616e2e5072656d69736529» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
        (_root_.Geb.Kernel.leaf 0)
        x0)
      (_root_.Geb.Kernel.leaf 0);
    x1

def «$285365712e73696e676c6520486f6c65506c616e2e50726f6f664e6f646529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «HolePlan.collect» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x4 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x5
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e4e6f64657329»
          (fun (x6 : _root_.Geb.Kernel.Tree)
             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
            let x8 : _root_.Geb.Kernel.Tree := x6;
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x8)
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
              x4 x7
            else
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
              _root_.GebMirror.Metalogic.«HolePlan.appendNodes» ((x3).2 x10) (x4 x7)))
      (fun (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«$28456163682e6973456d70747920486f6c65506c616e2e5072656d69736529»
          x3).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c65506c616e2e4e6f64657329»
            (_root_.GebMirror.Metalogic.«HolePlan.nodes»
              (_root_.GebMirror.Metalogic.«$285365712e73696e676c6520486f6c65506c616e2e50726f6f664e6f646529»
                x2))
        else
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e4e6f64657329»)
      x0
      x1;
    x3

def «$285365712e7461696c202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f64657329292929» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        x2);
    x1

def «$2850726f6f66486f6c65732e666f6c64536b65746368202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f64657329292929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
        _root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          _root_.GebMirror.Metalogic.«ProofHoles.holeTag»).label ≠ 0 then
          x0 (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
        else
          x1
            x3
            (_root_.GebMirror.Metalogic.«$285365712e7461696c202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f64657329292929»
              x4))
      x2;
    x3

def «$284d61702e6d6170202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f646573292929205429» :=
  fun (x0 : (_root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) →
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «HolePlan.plan» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (_root_.GebMirror.Metalogic.«$2850726f6f66486f6c65732e666f6c64536b65746368202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f64657329292929»
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        (_root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 18)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          ([] : _root_.List _root_.Geb.Kernel.Tree),
          fun (_ : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c65506c616e2e4e6f64657329»
              (_root_.GebMirror.Metalogic.«HolePlan.nodes»
                ([] : _root_.List _root_.Geb.Kernel.Tree))))
      (fun (x5 : _root_.Geb.Kernel.Tree)
         (x6 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))) =>
        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.Const.label x5)
          ((_root_.Geb.Kernel.Const.child x5 (_root_.Geb.Kernel.leaf 0)) ::
            (_root_.GebMirror.Metalogic.«$284d61702e6d6170202850726f64205420284172726f772044657269766174696f6e2e54686d2032393a284f7074696f6e2e4d6179626520486f6c65506c616e2e4e6f646573292929205429»
              (fun (x7 : _root_.Geb.Kernel.Tree ×
                   (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
                (x7).1)
              x6));
        (x7,
          fun (x8 : _root_.Geb.Kernel.Tree) =>
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HolePlan.proofPremises»
              x0
              x1
              x2
              x8
              x7;
            let x10 : _root_.Geb.Kernel.Tree := x9;
            let x11 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x10;
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
            let x18 : _root_.Geb.Kernel.Tree := x16;
            let x19 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x18;
            let x20 : _root_.List _root_.Geb.Kernel.Tree := x19;
            _root_.GebMirror.Metalogic.«HolePlan.collect» x6 x20 x9))
      x3).2
      x4;
    x5

def «HoleSequent.equalizerAxiom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
      _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
      (_root_.Geb.Kernel.Const.add
        (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
          _root_.GebMirror.Metalogic.«Theory.productAxioms»)
        x0);
    x1

def «HoleSequent.classifierAxiom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
      _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
      (_root_.Geb.Kernel.Const.add
        (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
          _root_.GebMirror.Metalogic.«Theory.exponentialAxioms»)
        x0);
    x1

def «HoleSequent.diagonalDfd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                     (_root_.Geb.Kernel.Const.child
                                       (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
                                       (_root_.Geb.Kernel.leaf 0))
                                     (_root_.Geb.Kernel.leaf 0);
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                     (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                       (_root_.Geb.Kernel.Const.equal
                                         (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
                                         (_root_.GebMirror.Metalogic.«Theory.diag» x1)))
                                     (fun (_ : _root_.Geb.Kernel.Tree) =>
                                       let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.dom»
                                         (_root_.GebMirror.Metalogic.«Combinator.tyT» x0);
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
                                         (_root_.GebMirror.Metalogic.«Combinator.pInst»
                                           (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                               (_root_.Geb.Kernel.leaf 7)))
                                           (_root_.GebMirror.Metalogic.«Theory.l2»
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
                                               (_root_.GebMirror.Metalogic.«Theory.cFst» x3 x3))
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
                                               (_root_.GebMirror.Metalogic.«Theory.cSnd» x3 x3))))
                                         (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                           let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ecEqn»
                                             x4;
                                           let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.cFst»
                                             x1
                                             x1;
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                             (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x6)
                                             (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                                 (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
                                                   (_root_.GebMirror.Metalogic.«Theory.comp»
                                                     x6
                                                     (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x5)))
                                                 (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                   let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.cCong»
                                                     (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x8)
                                                     (_root_.GebMirror.Metalogic.«Theory.l2»
                                                       (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x7)
                                                       (_root_.GebMirror.Metalogic.«Combinator.ecCert» x4));
                                                   let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.monoCond»
                                                     (_root_.GebMirror.Metalogic.«Combinator.tyT» x0);
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                     (_root_.GebMirror.Metalogic.«Combinator.pByNorm»
                                                       _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                         (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x10)
                                                         (_root_.GebMirror.Metalogic.«Theory.comp»
                                                           x6
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                                                             x5))))
                                                     (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                         (_root_.GebMirror.Metalogic.«Combinator.pByNorm»
                                                           _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                                               x6
                                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                                                                 x5))
                                                             (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                                                               x10)))
                                                         (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                                             (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                               (_root_.GebMirror.Metalogic.«HoleSequent.classifierAxiom»
                                                                 (_root_.Geb.Kernel.leaf 4))
                                                               (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.tyT»
                                                                   x0))
                                                               (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                                                   x0))
                                                               (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                   x11
                                                                   (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                     x9
                                                                     x12)))))))))));
    x1

def «HoleSequent.sequentOp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 27))
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e50547929»
          x2)
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e61744f7220436f6d62696e61746f722e50547929»
        _root_.GebMirror.Metalogic.«Combinator.pty0»
        x2
        (_root_.Geb.Kernel.leaf 0);
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
        (_root_.GebMirror.Metalogic.«HoleSequent.diagonalDfd» x3)
        (fun (x4 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e50547929»
            (_root_.GebMirror.Metalogic.«Combinator.typeOpTy»
              x0
              x1
              (_root_.Geb.Kernel.leaf 1)
              (_root_.GebMirror.Metalogic.«Theory.chi» (_root_.GebMirror.Metalogic.«Combinator.tyT» x3))
              x4
              x2)
            _root_.GebMirror.Metalogic.«Combinator.memoRet»)
    else
      _root_.GebMirror.Metalogic.«Combinator.typeOp» x0 x1 x2);
    x3

def «HoleSequent.sequentStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x3)
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.arity x3)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        x1
          (_root_.Geb.Kernel.Const.label
            (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0)))
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»
    else
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792920436f6d62696e61746f722e50547929»
        (_root_.GebMirror.Metalogic.«Combinator.lookup» (x2 x3))
        (fun (x5 : _root_.Geb.Kernel.Tree) =>
          let x6 : _root_.Geb.Kernel.Tree := x5;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x6)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x7 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x6;
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
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
              x8
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x6;
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e50547929»
              (_root_.GebMirror.Metalogic.«Combinator.seqY» x4)
              (fun (x8 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«HoleSequent.sequentOp»
                  x0
                  (_root_.Geb.Kernel.Const.sub
                    (_root_.Geb.Kernel.Const.label x3)
                    (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x8))));
    x5

def «HoleSequent.sequentTypers» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree) := (fun (x1 : _root_.List _root_.Geb.Kernel.Tree)
                                          (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.para
        (α := _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«HoleSequent.sequentStep»
          (x0).1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e50547929»
              x1
              x3;
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
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                x6
            else
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»)
          (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
            (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
              _root_.GebMirror.Metalogic.«Combinator.tyT»
              x1)))
        x2,
      fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.para
          (α := _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«HoleSequent.sequentStep»
            (x0).1
            (_root_.GebMirror.Metalogic.«Combinator.typeVar» (x0).2)
            (fun (x2 : _root_.Geb.Kernel.Tree) => x2))
          x1);
    x1

def «HoleSequent.typedTerm» :=
  (_root_.Geb.Kernel.Const.iter
    (α := (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    _root_.GebMirror.Metalogic.«HoleSequent.sequentTypers»
    (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
       (_ : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»,
      fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»)
    (_root_.Geb.Kernel.leaf 8)).2

def «HoleSequent.atomicSide» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x0)
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
          (if (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Combinator.tySort» x1)
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Language.pr»
              (_root_.GebMirror.Metalogic.«Combinator.tyLo» x1)
              (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x1)
          else
            _root_.GebMirror.Metalogic.«Language.pr»
              x0
              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x1)));
    x1

def «HoleSequent.rewriteComposite» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x1)
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d61796265204c616e67756167652e545061697229204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f72456c73652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
            (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e54506169722032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
              (_root_.GebMirror.Metalogic.«Combinator.rewriteRoot»
                _root_.GebMirror.Metalogic.«Combinator.baseRules»
                x1)
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e707572652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
                  (_root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                    x4)))
            (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e707572652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»))
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            let x5 : _root_.Geb.Kernel.Tree := x4;
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x5)
              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
              let x6 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972204c616e67756167652e545061697229»
                (x0 (_root_.GebMirror.Metalogic.«Language.p1» x7))
                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                    (_root_.GebMirror.Metalogic.«Language.pr»
                      (_root_.GebMirror.Metalogic.«Language.p1» x9)
                      (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                        x2
                        (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                          (_root_.GebMirror.Metalogic.«Language.p2» x7)
                          (_root_.GebMirror.Metalogic.«Language.p2» x9)))))
            else
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                (_root_.GebMirror.Metalogic.«Language.pr» x1 x2)));
    x3

def «$284d61702e6d6170205420284172726f7720436f6d62696e61746f722e506853636f706520284172726f7720436f6d62696e61746f722e5053742033363a28436f6d62696e61746f722e436f6d702e4f7574204c616e67756167652e545061697229292929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        ((x0 x2) :: x3))
      ([] : _root_.List (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x1;
    x2

def «HoleSequent.compositionStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x1)
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Combinator.tySort» x3)
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Language.pr»
              (_root_.GebMirror.Metalogic.«Combinator.tyLo» x3)
              (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x3))
        else
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
              (_root_.GebMirror.Metalogic.«Language.pr»
                x1
                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3))
          else
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5061697273204c616e67756167652e545061697229»
              (_root_.GebMirror.Metalogic.«Combinator.seqP»
                (if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                  x2
                else
                  _root_.GebMirror.Metalogic.«$284d61702e6d6170205420284172726f7720436f6d62696e61746f722e506853636f706520284172726f7720436f6d62696e61746f722e5053742033363a28436f6d62696e61746f722e436f6d702e4f7574204c616e67756167652e545061697229292929»
                    _root_.GebMirror.Metalogic.«HoleSequent.atomicSide»
                    (_root_.Geb.Kernel.Const.children x1)))
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                let x5 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.pairsOf» x4;
                let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e5450616972205429»
                    _root_.GebMirror.Metalogic.«Language.p1»
                    x5);
                let x7 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.equal
                  x1
                  x6).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Combinator.tyDfd» x3
                else
                  _root_.GebMirror.Metalogic.«Combinator.cCong»
                    (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3)
                    (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e5450616972205429»
                      _root_.GebMirror.Metalogic.«Language.p2»
                      x5));
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«HoleSequent.rewriteComposite» x0 x6 x7
                else
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                    (_root_.GebMirror.Metalogic.«Language.pr» x6 x7)));
    x3

def «HoleSequent.normal» :=
  _root_.Geb.Kernel.Const.iter
    (α := _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (fun (x0 : _root_.Geb.Kernel.Tree →
         _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
       (x1 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.para
        (α := _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«HoleSequent.compositionStep» x0)
        x1)
    (fun (_ : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»)
    (_root_.Geb.Kernel.leaf 64)

def «HoleSequent.normalizeEq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.normal»
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0))
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
          (_root_.GebMirror.Metalogic.«HoleSequent.normal»
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x0))
          (fun (x2 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
              (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Language.p1» x1)
                  (_root_.GebMirror.Metalogic.«Language.p1» x2)))
              (fun (_ : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                    (_root_.GebMirror.Metalogic.«Language.p2» x1)
                    (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                      (_root_.GebMirror.Metalogic.«Language.p2» x2))))));
    x1

def «HoleSequent.transportEq» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.normalizeEq»
        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2)
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0)))
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
          (_root_.GebMirror.Metalogic.«HoleSequent.normalizeEq»
            (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
              (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x0)
              (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2)))
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
              (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                x3
                (_root_.GebMirror.Metalogic.«Combinator.cTrans» x1 x4))));
    x3

def «HoleSequent.compCong» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm»
        (_root_.GebMirror.Metalogic.«Theory.comp»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0)
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x1)))
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
          (_root_.GebMirror.Metalogic.«Combinator.cCong»
            (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x4)
            (_root_.GebMirror.Metalogic.«Theory.l2» x2 x3)));
    x4

def «HoleSequent.postcompose» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x0)
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«HoleSequent.compCong»
          (_root_.GebMirror.Metalogic.«Theory.dfd» x0)
          x1
          (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3)
          x2);
    x3

def «HoleSequent.precompose» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x2)
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«HoleSequent.compCong»
          x0
          (_root_.GebMirror.Metalogic.«Theory.dfd» x2)
          x1
          (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3));
    x3

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e45716e4365727429»);
    x4

def «HoleSequent.truthEquation» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                     _root_.GebMirror.Metalogic.«Theory.tru»
                                     (_root_.GebMirror.Metalogic.«Theory.bang»
                                       (_root_.GebMirror.Metalogic.«Theory.dom» x0));
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e45716e4365727429»
                                     (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm»
                                       (_root_.GebMirror.Metalogic.«Theory.eqz» x0 x1))
                                     (fun (_ : _root_.Geb.Kernel.Tree) =>
                                       _root_.GebMirror.Metalogic.«Combinator.pInst»
                                         (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                                           (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                             (_root_.Geb.Kernel.leaf 7)))
                                         (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1)));
    x1

def «HoleSequent.truthFactor» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                     _root_.GebMirror.Metalogic.«Theory.tru»
                                     (_root_.GebMirror.Metalogic.«Theory.bang»
                                       (_root_.GebMirror.Metalogic.«Theory.dom» x0));
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                                     (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x0)
                                     (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x3)
                                         (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm» x1)
                                             (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                                                 (_root_.GebMirror.Metalogic.«HoleSequent.typedTerm»
                                                   (_root_.GebMirror.Metalogic.«Theory.eqz» x0 x3))
                                                 (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                                   let x8 : _root_.List
                                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l3»
                                                     x0
                                                     x3
                                                     x1;
                                                   let x9 : _root_.List
                                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l3»
                                                     (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x4)
                                                     (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                                                     (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x6);
                                                   let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.truthLift»
                                                     x0
                                                     x1;
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                                     (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                                       (_root_.GebMirror.Metalogic.«Theory.dfd» x10)
                                                       (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                                           (_root_.Geb.Kernel.leaf 10))
                                                         x8
                                                         x9
                                                         (_root_.GebMirror.Metalogic.«Theory.l2»
                                                           (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x7)
                                                           x2)))
                                                     (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                                         (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                             (_root_.GebMirror.Metalogic.«Theory.dom» x10)
                                                             (_root_.GebMirror.Metalogic.«Combinator.tyLo» x6))
                                                           (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                             (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                               (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                                                 (_root_.Geb.Kernel.leaf 11))
                                                               x8
                                                               x9
                                                               (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                 x11))
                                                             (_root_.GebMirror.Metalogic.«Combinator.tyLoC»
                                                               x6)))
                                                         (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                                             (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                                 (_root_.GebMirror.Metalogic.«Theory.cod» x10)
                                                                 (_root_.GebMirror.Metalogic.«Combinator.tyLo»
                                                                   x7))
                                                               (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                                   (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                                                     (_root_.Geb.Kernel.leaf 12))
                                                                   x8
                                                                   x9
                                                                   (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                     x11))
                                                                 (_root_.GebMirror.Metalogic.«Combinator.tyLoC»
                                                                   x7)))
                                                             (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.memoRet»
                                                                   (_root_.GebMirror.Metalogic.«Combinator.pty»
                                                                     x10
                                                                     (_root_.Geb.Kernel.leaf 1)
                                                                     x11
                                                                     (_root_.GebMirror.Metalogic.«Combinator.tyLo»
                                                                       x6)
                                                                     x12
                                                                     (_root_.GebMirror.Metalogic.«Combinator.tyLo»
                                                                       x7)
                                                                     x13))
                                                                 (fun (_ : _root_.Geb.Kernel.Tree) =>
                                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                                                     (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                                         (_root_.GebMirror.Metalogic.«Theory.comp»
                                                                           (_root_.GebMirror.Metalogic.«Theory.truthIncl»
                                                                             x0)
                                                                           x10)
                                                                         x1)
                                                                       (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                                         (_root_.GebMirror.Metalogic.«HoleSequent.equalizerAxiom»
                                                                           (_root_.Geb.Kernel.leaf 13))
                                                                         x8
                                                                         x9
                                                                         (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                           x11)))
                                                                     (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                                                                         (_root_.GebMirror.Metalogic.«Language.pr»
                                                                           x10
                                                                           x15)))))))))));
    x3

def «HoleSequent.subobject» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «$28436f6d62696e61746f722e436f6d702e72657320486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e5375626f626a65637429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HoleSequent.subDom» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x3);
    x1

def «HoleSequent.inclusion» :=
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

def «HoleSequent.facts» :=
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
                                 _root_.GebMirror.Metalogic.«Combinator.pairsOf» x7);
    x1

def «HoleSequent.restrictFact» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1»
                                     x4;
                                   let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                     (_root_.GebMirror.Metalogic.«Theory.comp»
                                       x5
                                       (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0))
                                     (_root_.GebMirror.Metalogic.«Theory.comp»
                                       _root_.GebMirror.Metalogic.«Theory.tru»
                                       (_root_.GebMirror.Metalogic.«Theory.bang»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.subDom» x0)));
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                     (_root_.GebMirror.Metalogic.«HoleSequent.precompose»
                                       x6
                                       (_root_.GebMirror.Metalogic.«Language.p2» x4)
                                       x1)
                                     (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                       let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                         (_root_.GebMirror.Metalogic.«Theory.comp» x5 x3)
                                         (_root_.GebMirror.Metalogic.«Theory.comp»
                                           _root_.GebMirror.Metalogic.«Theory.tru»
                                           (_root_.GebMirror.Metalogic.«Theory.bang» x2));
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.transportEq»
                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x6)
                                               x1)
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x6)
                                               x1))
                                           x7
                                           x8)
                                         (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                                             (_root_.GebMirror.Metalogic.«Combinator.addLemma» x8 x9)
                                             (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                                                 (_root_.GebMirror.Metalogic.«Language.pr» x5 x10)))));
    x5

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e506169727320486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e5375626f626a65637429»);
    x4

def «$284d61702e6d6170204c616e67756167652e545061697220284172726f7720436f6d62696e61746f722e506853636f706520284172726f7720436f6d62696e61746f722e5053742033363a28436f6d62696e61746f722e436f6d702e4f7574204c616e67756167652e545061697229292929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        ((x0 x2) :: x3))
      ([] : _root_.List (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x1;
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e4365727420486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e5375626f626a65637429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e5375626f626a65637429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20486f6c6553657175656e742e5375626f626a65637429»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320486f6c6553657175656e742e5375626f626a65637429»
        x0
        x2);
    x3

def «$285365712e617070656e64204c616e67756167652e545061697229» :=
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

def «HoleSequent.intersect» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                     x1
                                     (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0);
                                   let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.truthIncl»
                                     x2;
                                   let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.truthEq»
                                     x2;
                                   let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                     (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0)
                                     x3;
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e506169727320486f6c6553657175656e742e5375626f626a65637429»
                                     (_root_.GebMirror.Metalogic.«Combinator.seqP»
                                       (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e545061697220284172726f7720436f6d62696e61746f722e506853636f706520284172726f7720436f6d62696e61746f722e5053742033363a28436f6d62696e61746f722e436f6d702e4f7574204c616e67756167652e545061697229292929»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.restrictFact» x0 x3 x4 x5)
                                         (_root_.GebMirror.Metalogic.«HoleSequent.facts» x0)))
                                     (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e4365727420486f6c6553657175656e742e5375626f626a65637429»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.truthEquation» x2)
                                         (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                           let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                             (_root_.GebMirror.Metalogic.«Theory.comp» x1 x5)
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               _root_.GebMirror.Metalogic.«Theory.tru»
                                               (_root_.GebMirror.Metalogic.«Theory.bang» x4));
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e5375626f626a65637429»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.transportEq»
                                               (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x7)
                                               (_root_.GebMirror.Metalogic.«Combinator.ecCert» x7)
                                               x8)
                                             (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e5375626f626a65637429»
                                                 (_root_.GebMirror.Metalogic.«Combinator.addLemma» x8 x9)
                                                 (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e5375626f626a65637429»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.subobject»
                                                       x4
                                                       x5
                                                       (_root_.GebMirror.Metalogic.«Combinator.pairs»
                                                         (_root_.GebMirror.Metalogic.«$285365712e617070656e64204c616e67756167652e545061697229»
                                                           (_root_.GebMirror.Metalogic.«Combinator.pairsOf» x6)
                                                           (_root_.GebMirror.Metalogic.«$285365712e73696e676c65204c616e67756167652e545061697229»
                                                             (_root_.GebMirror.Metalogic.«Language.pr»
                                                               x1
                                                               x10))))))))));
    x2

def «HoleSequent.factor» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «$28436f6d62696e61746f722e436f6d702e72657320486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e466163746f7229» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HoleSequent.through» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x3);
    x1

def «HoleSequent.liftOf» :=
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

def «HoleSequent.equation» :=
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

def «HoleSequent.factOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal
          x1
          (_root_.GebMirror.Metalogic.«Language.p1» x2)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some» (_root_.GebMirror.Metalogic.«Language.p2» x2)
        else
          x3)
      _root_.GebMirror.Metalogic.«Prelude.none»
      (_root_.GebMirror.Metalogic.«HoleSequent.facts» x0);
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e466163746f7229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e466163746f7229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20486f6c6553657175656e742e466163746f7229»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320486f6c6553657175656e742e466163746f7229»
        x0
        x2);
    x3

def «HoleSequent.factorStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleSequent.factOf»
                                     x0
                                     x2;
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                     (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                       (_root_.GebMirror.Metalogic.«Prelude.isSome» x3))
                                     (fun (_ : _root_.Geb.Kernel.Tree) =>
                                       let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                         x2
                                         (_root_.GebMirror.Metalogic.«HoleSequent.through» x1);
                                       let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                         _root_.GebMirror.Metalogic.«Theory.tru»
                                         (_root_.GebMirror.Metalogic.«Theory.bang»
                                           (_root_.GebMirror.Metalogic.«Theory.dom» x5));
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                         (_root_.GebMirror.Metalogic.«HoleSequent.postcompose»
                                           x2
                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                               (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
                                               (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))
                                             (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0))
                                           (_root_.GebMirror.Metalogic.«HoleSequent.equation» x1))
                                         (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.transportEq»
                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                 (_root_.GebMirror.Metalogic.«Theory.comp»
                                                   x2
                                                   (_root_.GebMirror.Metalogic.«Theory.comp»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1)))
                                                 (_root_.GebMirror.Metalogic.«Theory.comp»
                                                   _root_.GebMirror.Metalogic.«Theory.tru»
                                                   (_root_.GebMirror.Metalogic.«Theory.bang»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.subDom» x0))))
                                               (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                 x7
                                                 (_root_.GebMirror.Metalogic.«Prelude.get» x3))
                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                 (_root_.GebMirror.Metalogic.«Theory.comp»
                                                   x5
                                                   (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))
                                                 (_root_.GebMirror.Metalogic.«Theory.comp»
                                                   x6
                                                   (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))))
                                             (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220486f6c6553657175656e742e466163746f7229»
                                                 (_root_.GebMirror.Metalogic.«HoleSequent.truthFactor»
                                                   x5
                                                   (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1)
                                                   x8)
                                                 (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.postcompose»
                                                       (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                         (_root_.GebMirror.Metalogic.«Theory.comp»
                                                           (_root_.GebMirror.Metalogic.«Theory.truthIncl» x5)
                                                           (_root_.GebMirror.Metalogic.«Language.p1» x9))
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))
                                                       (_root_.GebMirror.Metalogic.«Language.p2» x9))
                                                     (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                       let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
                                                         (_root_.GebMirror.Metalogic.«Theory.truthIncl» x5);
                                                       let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                         (_root_.GebMirror.Metalogic.«Theory.comp»
                                                           x11
                                                           (_root_.GebMirror.Metalogic.«Language.p1» x9))
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.inclusion»
                                                           x0);
                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.transportEq»
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                             (_root_.GebMirror.Metalogic.«Theory.comp»
                                                               (_root_.GebMirror.Metalogic.«HoleSequent.through»
                                                                 x1)
                                                               (_root_.GebMirror.Metalogic.«Theory.comp»
                                                                 (_root_.GebMirror.Metalogic.«Theory.truthIncl»
                                                                   x5)
                                                                 (_root_.GebMirror.Metalogic.«Language.p1» x9)))
                                                             (_root_.GebMirror.Metalogic.«HoleSequent.inclusion»
                                                               x0))
                                                           (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                             x10
                                                             (_root_.GebMirror.Metalogic.«HoleSequent.equation»
                                                               x1))
                                                           x12)
                                                         (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420486f6c6553657175656e742e466163746f7229»
                                                             (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                                               x12
                                                               x13)
                                                             (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e466163746f7229»
                                                                 (_root_.GebMirror.Metalogic.«HoleSequent.factor»
                                                                   x11
                                                                   (_root_.GebMirror.Metalogic.«Language.p1» x9)
                                                                   x14)))))))));
    x3

def «HoleSequent.sideEquation» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
      (_root_.GebMirror.Metalogic.«HoleSequent.postcompose»
        x2
        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
          (_root_.GebMirror.Metalogic.«Theory.comp»
            (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
            (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))
          (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0))
        (_root_.GebMirror.Metalogic.«HoleSequent.equation» x1))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«HoleSequent.transportEq»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
            (_root_.GebMirror.Metalogic.«Theory.comp»
              x2
              (_root_.GebMirror.Metalogic.«Theory.comp»
                (_root_.GebMirror.Metalogic.«HoleSequent.through» x1)
                (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1)))
            (_root_.GebMirror.Metalogic.«Theory.comp»
              x2
              (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x0)))
          x5
          (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
            (_root_.GebMirror.Metalogic.«Theory.comp»
              x3
              (_root_.GebMirror.Metalogic.«HoleSequent.liftOf» x1))
            x4));
    x5

def «$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e5375626f626a656374205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e5375626f626a65637420486f6c6553657175656e742e5375626f626a65637429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e5375626f626a65637429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e466163746f72205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e466163746f7220486f6c6553657175656e742e466163746f7229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
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
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420486f6c6553657175656e742e466163746f7229»);
    x4

def «HoleSequent.weakenProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thArity»
                                     x1;
                                   let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.ctxObj»
                                     (_root_.GebMirror.Metalogic.«Derivation.thCtx» x1);
                                   let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.seqConcl»
                                     (_root_.GebMirror.Metalogic.«Derivation.thmSeq» x0 x1);
                                   let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
                                     x4
                                     (_root_.GebMirror.Metalogic.«Derivation.thCtx» x1)
                                     x2
                                     (_root_.GebMirror.Metalogic.«Derivation.thConcl» x1);
                                   let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.seqConcl»
                                     (_root_.GebMirror.Metalogic.«Derivation.thmSeq» x0 x7);
                                   let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.seqConcl»
                                     (_root_.GebMirror.Metalogic.«Derivation.thmSeq»
                                       x0
                                       (_root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
                                         x4
                                         (_root_.GebMirror.Metalogic.«Derivation.thCtx» x1)
                                         ([] : _root_.List _root_.Geb.Kernel.Tree)
                                         (_root_.GebMirror.Metalogic.«Derivation.thConcl» x1)));
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                     (_root_.GebMirror.Metalogic.«Combinator.addLemma» x6 x3)
                                     (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e5375626f626a656374205429»
                                         (_root_.Geb.Kernel.Const.foldr
                                           (α := _root_.Geb.Kernel.Tree)
                                           (β := _root_.Geb.Kernel.Tree →
                                             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                           (fun (x11 : _root_.Geb.Kernel.Tree)
                                              (x12 : _root_.Geb.Kernel.Tree →
                                                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e5375626f626a65637420486f6c6553657175656e742e5375626f626a65637429»
                                               x12
                                               (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«HoleSequent.intersect»
                                                   x13
                                                   (_root_.GebMirror.Metalogic.«Derivation.thmArrow»
                                                     x0
                                                     x1
                                                     x11)))
                                           (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e5375626f626a65637429»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.subobject»
                                               x5
                                               (_root_.GebMirror.Metalogic.«Theory.idt» x5)
                                               (_root_.GebMirror.Metalogic.«Combinator.pairs»
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                           (_root_.GebMirror.Metalogic.«Prelude.reverse» x2))
                                         (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                             (_root_.GebMirror.Metalogic.«HoleSequent.normalizeEq»
                                               (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                 (_root_.GebMirror.Metalogic.«Theory.comp»
                                                   (_root_.GebMirror.Metalogic.«Theory.idt» x5)
                                                   (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x11))
                                                 (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x11)))
                                             (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e466163746f72205429»
                                                 (_root_.Geb.Kernel.Const.foldr
                                                   (α := _root_.Geb.Kernel.Tree)
                                                   (β := _root_.Geb.Kernel.Tree →
                                                     _root_.Geb.Kernel.Tree →
                                                       _root_.Geb.Kernel.Tree)
                                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                                      (x14 : _root_.Geb.Kernel.Tree →
                                                        _root_.Geb.Kernel.Tree →
                                                          _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420486f6c6553657175656e742e466163746f7220486f6c6553657175656e742e466163746f7229»
                                                       x14
                                                       (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                                         _root_.GebMirror.Metalogic.«HoleSequent.factorStep»
                                                           x11
                                                           x15
                                                           (_root_.GebMirror.Metalogic.«Derivation.thmArrow»
                                                             x0
                                                             x1
                                                             x13)))
                                                   (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520486f6c6553657175656e742e466163746f7229»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.factor»
                                                       (_root_.GebMirror.Metalogic.«Theory.idt» x5)
                                                       (_root_.GebMirror.Metalogic.«HoleSequent.inclusion» x11)
                                                       x12))
                                                   (_root_.GebMirror.Metalogic.«Prelude.reverse»
                                                     (_root_.GebMirror.Metalogic.«Derivation.thHyps» x1)))
                                                 (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                     (_root_.GebMirror.Metalogic.«HoleSequent.sideEquation»
                                                       x11
                                                       x13
                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x9)
                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x6)
                                                       (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x8))
                                                     (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                         (_root_.GebMirror.Metalogic.«HoleSequent.sideEquation»
                                                           x11
                                                           x13
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x9)
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x6)
                                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x8))
                                                         (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                             (_root_.GebMirror.Metalogic.«HoleSequent.precompose»
                                                               x6
                                                               x10
                                                               (_root_.GebMirror.Metalogic.«HoleSequent.liftOf»
                                                                 x13))
                                                             (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                   (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                                                     x14)
                                                                   (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                     x16
                                                                     x15))))))))));
    x4

def «$285365712e7461696c20284172726f77205420542929» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2);
    x1

def «$285365712e64726f7020284172726f77205420542929» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree) := _root_.Geb.Kernel.Const.iter
      (α := _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      _root_.GebMirror.Metalogic.«$285365712e7461696c20284172726f77205420542929»
      x1
      x0;
    x2

def «$285365712e61744f7220284172726f77205420542929» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$285365712e64726f7020284172726f77205420542929» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (_ : _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x3);
    x3

def «$284d61702e6d617020284172726f772054205429205429» :=
  fun (x0 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
      _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «HoleSequent.lower» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
         (x5 : _root_.Geb.Kernel.Tree) =>
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x3;
        let x7 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
          x3
          (_root_.Geb.Kernel.leaf 0);
        let x9 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
          _root_.Geb.Kernel.Tree := (fun (x9 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
          x9 x5);
        if (_root_.Geb.Kernel.Const.eq
          x6
          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Combinator.cHyp»
            (_root_.Geb.Kernel.Const.add
              x5
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.sub x1 (_root_.Geb.Kernel.leaf 1))
                x8))
        else
          if (_root_.GebMirror.Metalogic.«Prelude.or»
            (_root_.Geb.Kernel.Const.eq x6 (_root_.Geb.Kernel.leaf 1))
            (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
            x3
          else
            if (_root_.Geb.Kernel.Const.eq
              x6
              (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Combinator.cStrict»
                x8
                (_root_.GebMirror.Metalogic.«$285365712e61744f7220284172726f77205420542929»
                  (fun (_ : _root_.Geb.Kernel.Tree) => _root_.Geb.Kernel.leaf 0)
                  x4
                  (_root_.Geb.Kernel.leaf 1)
                  x5)
            else
              if (_root_.Geb.Kernel.Const.eq
                x6
                (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                _root_.Geb.Kernel.Const.node
                  x6
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.GebMirror.Metalogic.«$285365712e61744f7220284172726f77205420542929»
                      (fun (_ : _root_.Geb.Kernel.Tree) => _root_.Geb.Kernel.leaf 0)
                      x4
                      (_root_.Geb.Kernel.leaf 0)
                      x5)
                    (_root_.GebMirror.Metalogic.«$285365712e61744f7220284172726f77205420542929»
                      (fun (_ : _root_.Geb.Kernel.Tree) => _root_.Geb.Kernel.leaf 0)
                      x4
                      (_root_.Geb.Kernel.leaf 1)
                      (_root_.Geb.Kernel.Const.add x5 (_root_.Geb.Kernel.leaf 1))))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x6
                  (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                  let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                    (_root_.Geb.Kernel.leaf 1)
                    (_root_.GebMirror.Metalogic.«Prelude.length»
                      (_root_.GebMirror.Metalogic.«PartialHorn.seqCtx»
                        (_root_.GebMirror.Metalogic.«$285365712e61744f72205061727469616c486f726e2e53657175656e7429»
                          (_root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                              (_root_.Geb.Kernel.leaf 0)
                              (_root_.Geb.Kernel.leaf 0)))
                          x0
                          x8)));
                  _root_.Geb.Kernel.Const.node
                    x6
                    (_root_.GebMirror.Metalogic.«Prelude.append»
                      (_root_.GebMirror.Metalogic.«Base.take» x10 x7)
                      (_root_.GebMirror.Metalogic.«$284d61702e6d617020284172726f772054205429205429»
                        x9
                        (_root_.GebMirror.Metalogic.«$285365712e64726f7020284172726f77205420542929»
                          x10
                          x4)))
                else
                  _root_.Geb.Kernel.Const.node
                    x6
                    (_root_.GebMirror.Metalogic.«$284d61702e6d617020284172726f772054205429205429»
                      x9
                      x4))
      x2
      (_root_.Geb.Kernel.leaf 0);
    x3

def «HoleSequent.assemble» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e446576456e74727929»
                                          x1;
                                        _root_.Geb.Kernel.Const.foldr
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          (fun (x4 : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.Geb.Kernel.Tree) =>
                                            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e446576456e74727929»
                                              x1
                                              x4;
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
                                              let x10 : _root_.Geb.Kernel.Tree := x8;
                                              let x11 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x10;
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
                                              _root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 7)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (if (x4).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«HoleSequent.lower» x0 x4 x14
                                                  else
                                                    x14)
                                                  x5)
                                            else
                                              x5)
                                          (_root_.GebMirror.Metalogic.«HoleSequent.lower» x0 x3 x2)
                                          (_root_.GebMirror.Metalogic.«Base.range» x3));
    x3

def «HoleSequent.weakenSequent» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Derivation.certifies»
      x0
      x1
      x4
      (_root_.GebMirror.Metalogic.«Derivation.thmSeq» x0 x2)).label ≠ 0 then
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.compileDefs»
        x0;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
        let x9 : _root_.Geb.Kernel.Tree := x7;
        let x10 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x9;
        let x11 : _root_.List _root_.Geb.Kernel.Tree := x10;
        let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleSequent.weakenProof»
          x0
          x2
          x3
          x4
          (_root_.GebMirror.Metalogic.«Combinator.scope»
            (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
              (_root_.GebMirror.Metalogic.«Prelude.replicate»
                (_root_.GebMirror.Metalogic.«Derivation.thArity» x2)
                (_root_.Geb.Kernel.leaf 0)))
            (_root_.GebMirror.Metalogic.«PartialHorn.eqns»
              ([] : _root_.List _root_.Geb.Kernel.Tree)))
          (_root_.GebMirror.Metalogic.«Combinator.pmStart»
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            x11
            (_root_.Geb.Kernel.leaf 0));
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
          let x16 : _root_.Geb.Kernel.Tree := x14;
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
          let x19 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x17
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
              x20);
          let x20 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x19
            (_root_.Geb.Kernel.leaf 0)
            (fun (x20 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x20);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x19
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x22 : _root_.List _root_.Geb.Kernel.Tree) =>
              x22);
          let x22 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleSequent.assemble»
            (_root_.GebMirror.Metalogic.«PartialHorn.thyAxioms»
              (_root_.GebMirror.Metalogic.«Infer.ext» x11))
            (_root_.GebMirror.Metalogic.«Combinator.stDev» x20)
            x18;
          if (_root_.GebMirror.Metalogic.«Derivation.certifies»
            x0
            x1
            x22
            (_root_.GebMirror.Metalogic.«Derivation.thmSeq»
              x0
              (_root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
                (_root_.GebMirror.Metalogic.«Derivation.thArity» x2)
                (_root_.GebMirror.Metalogic.«Derivation.thCtx» x2)
                x3
                (_root_.GebMirror.Metalogic.«Derivation.thConcl» x2)))).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» x22
          else
            _root_.GebMirror.Metalogic.«Prelude.none»
        else
          _root_.GebMirror.Metalogic.«Prelude.none»
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x5

def «HoleRose.normBy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 37)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0)
        (_root_.Geb.Kernel.leaf 64))
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «HoleRose.joinByRules» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.normBy»
                                          x0;
                                        _root_.GebMirror.Metalogic.«Prover.dNode»
                                          (_root_.Geb.Kernel.leaf 18)
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (_root_.GebMirror.Metalogic.«Theory.l2» x1 x1));
    x1

def «HoleRose.nd0» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «HoleRose.congBy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «HoleRose.transBy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 1)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1);
    x2

def «HoleRose.readHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 17)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 (_root_.Geb.Kernel.leaf 0))
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «HoleRose.normHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.normBy»
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.Geb.Kernel.Const.node
          (_root_.Geb.Kernel.leaf 6)
          (_root_.GebMirror.Metalogic.«Prelude.single» x0)));
    x1

def «HoleRose.cutBy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 22)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2);
    x3

def «HoleRose.impElim» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.applyAt»
      (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 4))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2» x2 x1)
      (_root_.GebMirror.Metalogic.«Theory.l2» x3 x4);
    x5

def «HoleRose.tails» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
                                          x0
                                          (_root_.GebMirror.Metalogic.«Prelude.single»
                                            _root_.GebMirror.Metalogic.«Theory.omega»)
                                          _root_.GebMirror.Metalogic.«Language.mStar»;
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mFst»
                                          (_root_.GebMirror.Metalogic.«Language.var»
                                            (_root_.Geb.Kernel.leaf 0));
                                        _root_.GebMirror.Metalogic.«Language.mListRec»
                                          (_root_.GebMirror.Metalogic.«Language.mPair» x3 x3)
                                          (_root_.GebMirror.Metalogic.«Language.mPair»
                                            (_root_.GebMirror.Metalogic.«Language.mArr»
                                              x1
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                _root_.GebMirror.Metalogic.«Theory.omega»)
                                              (_root_.GebMirror.Metalogic.«Language.mPair»
                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                  (_root_.Geb.Kernel.leaf 1))
                                                x4))
                                            x4)
                                          x2);
    x3

def «HoleRose.rebuildList» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
      x0
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Theory.omega»))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Language.mEq»
        (_root_.GebMirror.Metalogic.«Language.mFst»
          (_root_.GebMirror.Metalogic.«HoleRose.tails»
            x1
            x2
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)));
    x3

def «HoleRose.rebuildProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree →
                                          _root_.List _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                                                         (x3 : _root_.List
                                                                           _root_.Geb.Kernel.Tree) =>
                                          _root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              x2
                                              (_root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 0)
                                                x3)));
                                        let x3 : _root_.Geb.Kernel.Tree := x2
                                          (_root_.Geb.Kernel.leaf 4)
                                          ([] : _root_.List _root_.Geb.Kernel.Tree);
                                        _root_.GebMirror.Metalogic.«Prover.dNode»
                                          (_root_.Geb.Kernel.leaf 20)
                                          (_root_.GebMirror.Metalogic.«Theory.l3»
                                            x0
                                            x1
                                            (_root_.GebMirror.Metalogic.«Language.mArr»
                                              x1
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                _root_.GebMirror.Metalogic.«Theory.omega»)
                                              (_root_.GebMirror.Metalogic.«Language.mPair»
                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (_root_.GebMirror.Metalogic.«Language.var»
                                                  (_root_.Geb.Kernel.leaf 0)))))
                                          (_root_.GebMirror.Metalogic.«Theory.l3»
                                            (_root_.GebMirror.Metalogic.«HoleRose.joinByRules»
                                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                                (x2
                                                  (_root_.Geb.Kernel.leaf 11)
                                                  (_root_.GebMirror.Metalogic.«Prelude.single» x0))
                                                x3))
                                            (_root_.GebMirror.Metalogic.«HoleRose.joinByRules»
                                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                                (x2
                                                  (_root_.Geb.Kernel.leaf 12)
                                                  (_root_.GebMirror.Metalogic.«Prelude.single» x1))
                                                x3))
                                            (_root_.GebMirror.Metalogic.«HoleRose.joinByRules»
                                              ([] : _root_.List _root_.Geb.Kernel.Tree))));
    x2

def «HoleRose.mapEquation» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
      x1
      (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.GebMirror.Metalogic.«Theory.list» x4))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Tactics.impL»
        x0
        (_root_.GebMirror.Metalogic.«Derivation.roseHyp»
          x2
          x3
          (_root_.GebMirror.Metalogic.«Language.mEq» x6 x7))
        (_root_.GebMirror.Metalogic.«Language.mEq»
          (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x2 x3 x5 x6)
          (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x2 x3 x5 x7)));
    x8

def «HoleRose.destructorEq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 18)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.GebMirror.Metalogic.«HoleRose.normHyp» x0)
        (_root_.GebMirror.Metalogic.«HoleRose.nd0» (_root_.Geb.Kernel.leaf 0)));
    x1

def «HoleRose.tailStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.transBy»
      (_root_.GebMirror.Metalogic.«HoleRose.congBy»
        (_root_.GebMirror.Metalogic.«Prelude.single» x0))
      (_root_.GebMirror.Metalogic.«HoleRose.transBy»
        (_root_.GebMirror.Metalogic.«HoleRose.nd0» (_root_.Geb.Kernel.leaf 5))
        (_root_.GebMirror.Metalogic.«HoleRose.readHyp» x1));
    x2

def «HoleRose.fromBy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 24)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2);
    x3

def «HoleRose.mapProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.Geb.Kernel.Tree := (let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.mapEquation»
                                           x0
                                           x2
                                           x3
                                           x4
                                           x5
                                           x6
                                           x7
                                           x8;
                                         let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.roseHyp»
                                           x3
                                           x4
                                           (_root_.GebMirror.Metalogic.«Language.mEq» x7 x8);
                                         let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x3 x4 x6 x7)
                                           (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x3 x4 x6 x8);
                                         let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                           x9;
                                         let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                           x4
                                           x5
                                           x11;
                                         let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                           x4
                                           x5
                                           x12;
                                         let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                           x11;
                                         let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                           x12;
                                         let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.subst»
                                           (_root_.GebMirror.Metalogic.«Language.mEq» x7 x8)
                                           (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                             (_root_.GebMirror.Metalogic.«Language.var»
                                               (_root_.Geb.Kernel.leaf 1)));
                                         let x19 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           _root_.GebMirror.Metalogic.«Language.mStar»
                                           _root_.GebMirror.Metalogic.«Language.mStar»;
                                         let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                           x16
                                           (_root_.Geb.Kernel.leaf 0);
                                         let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                           x16
                                           (_root_.Geb.Kernel.leaf 1);
                                         let x22 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
                                           x4
                                           (_root_.GebMirror.Metalogic.«Prelude.single»
                                             _root_.GebMirror.Metalogic.«Theory.omega»)
                                           (_root_.GebMirror.Metalogic.«Language.mPair» x18 x20);
                                         let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
                                           x4
                                           (_root_.GebMirror.Metalogic.«Prelude.single»
                                             _root_.GebMirror.Metalogic.«Theory.omega»)
                                           (_root_.GebMirror.Metalogic.«Language.mPair» x19 x21);
                                         let x24 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           x22
                                           x23;
                                         let x25 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Language.mListRec»
                                             x19
                                             (_root_.GebMirror.Metalogic.«Language.var»
                                               (_root_.Geb.Kernel.leaf 1))
                                             x22)
                                           (_root_.GebMirror.Metalogic.«Language.mListRec»
                                             x19
                                             (_root_.GebMirror.Metalogic.«Language.var»
                                               (_root_.Geb.Kernel.leaf 1))
                                             x23);
                                         let x26 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Language.mSnd»
                                             (_root_.GebMirror.Metalogic.«HoleRose.tails» x3 x4 x22))
                                           (_root_.GebMirror.Metalogic.«Language.mSnd»
                                             (_root_.GebMirror.Metalogic.«HoleRose.tails» x3 x4 x23));
                                         let x27 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Language.mFst»
                                             (_root_.GebMirror.Metalogic.«HoleRose.tails» x3 x4 x20))
                                           x20;
                                         let x28 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Language.mFst»
                                             (_root_.GebMirror.Metalogic.«HoleRose.tails» x3 x4 x21))
                                           x21;
                                         let x29 : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
                                           x9
                                           (_root_.GebMirror.Metalogic.«Theory.l3»
                                             (_root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                               (_root_.GebMirror.Metalogic.«Derivation.thConcl» x10))
                                             x14
                                             x24);
                                         let x30 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.rebuildList»
                                           x2
                                           x3
                                           x4;
                                         let x31 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 12)
                                           (_root_.GebMirror.Metalogic.«Prelude.single» x4)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree);
                                         let x32 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.congBy»
                                           (_root_.GebMirror.Metalogic.«Theory.l2» x31 x31);
                                         let x33 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.fromBy»
                                           x25
                                           x32
                                           (_root_.GebMirror.Metalogic.«HoleRose.destructorEq»
                                             (_root_.Geb.Kernel.Const.add
                                               x13
                                               (_root_.Geb.Kernel.leaf 2)));
                                         let x34 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.fromBy»
                                           x26
                                           (_root_.GebMirror.Metalogic.«HoleRose.congBy»
                                             (_root_.GebMirror.Metalogic.«Theory.l2»
                                               (_root_.GebMirror.Metalogic.«HoleRose.tailStep»
                                                 x31
                                                 (_root_.Geb.Kernel.Const.add
                                                   x13
                                                   (_root_.Geb.Kernel.leaf 3)))
                                               (_root_.GebMirror.Metalogic.«HoleRose.tailStep»
                                                 x31
                                                 (_root_.Geb.Kernel.Const.add
                                                   x13
                                                   (_root_.Geb.Kernel.leaf 4)))))
                                           (_root_.GebMirror.Metalogic.«HoleRose.destructorEq»
                                             (_root_.Geb.Kernel.Const.add
                                               x13
                                               (_root_.Geb.Kernel.leaf 2)));
                                         let x35 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 23)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (_root_.GebMirror.Metalogic.«Theory.l2»
                                             (_root_.GebMirror.Metalogic.«HoleRose.readHyp»
                                               (_root_.Geb.Kernel.Const.add
                                                 x13
                                                 (_root_.Geb.Kernel.leaf 5)))
                                             (_root_.GebMirror.Metalogic.«HoleRose.joinByRules»
                                               ([] : _root_.List _root_.Geb.Kernel.Tree)));
                                         let x36 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.impElim»
                                           x1
                                           x16
                                           x17
                                           (_root_.GebMirror.Metalogic.«HoleConditions.hypAt» x13)
                                           (_root_.GebMirror.Metalogic.«HoleConditions.hypAt»
                                             (_root_.Geb.Kernel.Const.add
                                               x13
                                               (_root_.Geb.Kernel.leaf 6)));
                                         let x37 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 18)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (_root_.GebMirror.Metalogic.«Theory.l2»
                                             (_root_.GebMirror.Metalogic.«HoleRose.transBy»
                                               x31
                                               (_root_.GebMirror.Metalogic.«HoleRose.congBy»
                                                 (_root_.GebMirror.Metalogic.«Prelude.single»
                                                   (_root_.GebMirror.Metalogic.«HoleRose.congBy»
                                                     (_root_.GebMirror.Metalogic.«Theory.l2»
                                                       (_root_.GebMirror.Metalogic.«HoleRose.readHyp»
                                                         (_root_.Geb.Kernel.Const.add
                                                           x13
                                                           (_root_.Geb.Kernel.leaf 7)))
                                                       (_root_.GebMirror.Metalogic.«HoleRose.readHyp»
                                                         (_root_.Geb.Kernel.Const.add
                                                           x13
                                                           (_root_.Geb.Kernel.leaf 8))))))))
                                             x31);
                                         let x38 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArr»
                                           x3
                                           (_root_.GebMirror.Metalogic.«Prelude.single» x5)
                                           _root_.GebMirror.Metalogic.«Language.mStar»;
                                         let x39 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 11)
                                           (_root_.GebMirror.Metalogic.«Prelude.single» x3)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree);
                                         let x40 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.impI»
                                           x1
                                           x13
                                           (_root_.GebMirror.Metalogic.«Language.subst»
                                             x11
                                             (_root_.GebMirror.Metalogic.«Derivation.instVar» x38))
                                           (_root_.GebMirror.Metalogic.«Language.subst»
                                             x12
                                             (_root_.GebMirror.Metalogic.«Derivation.instVar» x38))
                                           (_root_.GebMirror.Metalogic.«Prover.dNode»
                                             (_root_.Geb.Kernel.leaf 18)
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (_root_.GebMirror.Metalogic.«Theory.l2» x39 x39));
                                         _root_.GebMirror.Metalogic.«Base.bindO»
                                           (_root_.GebMirror.Metalogic.«HoleConditions.specialize»
                                             x0
                                             x1
                                             x29
                                             x30
                                             x20)
                                           (fun (x41 : _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«Base.mapO»
                                               (fun (x42 : _root_.Geb.Kernel.Tree) =>
                                                 let x43 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.impI»
                                                   x1
                                                   (_root_.Geb.Kernel.Const.add
                                                     x13
                                                     (_root_.Geb.Kernel.leaf 1))
                                                   x14
                                                   x15
                                                   (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                     x24
                                                     (_root_.GebMirror.Metalogic.«HoleRose.fromBy»
                                                       x14
                                                       x32
                                                       (_root_.GebMirror.Metalogic.«HoleConditions.hypAt»
                                                         (_root_.Geb.Kernel.Const.add
                                                           x13
                                                           (_root_.Geb.Kernel.leaf 1))))
                                                     (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                       x27
                                                       x41
                                                       (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                         x28
                                                         x42
                                                         (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                           (_root_.GebMirror.Metalogic.«Language.mEq» x18 x19)
                                                           x33
                                                           (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                             x16
                                                             x34
                                                             (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                               x18
                                                               x35
                                                               (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                                 x17
                                                                 x36
                                                                 x37)))))));
                                                 _root_.GebMirror.Metalogic.«Prover.dNode»
                                                   (_root_.Geb.Kernel.leaf 29)
                                                   (_root_.GebMirror.Metalogic.«Theory.l2» x3 x4)
                                                   (_root_.GebMirror.Metalogic.«Theory.l2» x40 x43))
                                               (_root_.GebMirror.Metalogic.«HoleConditions.specialize»
                                                 x0
                                                 x1
                                                 (_root_.GebMirror.Metalogic.«Prelude.append»
                                                   x29
                                                   (_root_.GebMirror.Metalogic.«Prelude.single» x27))
                                                 x30
                                                 x21)));
    x10

def «HoleRose.inductionBody» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := (let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x2
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x2
                                          (_root_.Geb.Kernel.leaf 2);
                                        let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.roseHyp»
                                          x9
                                          x10
                                          (_root_.GebMirror.Metalogic.«Derivation.thConcl» x3);
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                          x7;
                                        let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thConcl»
                                          x4;
                                        let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thConcl»
                                          x5;
                                        let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.transBy»
                                          (_root_.GebMirror.Metalogic.«HoleRose.readHyp»
                                            (_root_.Geb.Kernel.Const.add
                                              x12
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (_root_.GebMirror.Metalogic.«HoleRose.normHyp»
                                            (_root_.Geb.Kernel.Const.add
                                              x12
                                              (_root_.Geb.Kernel.leaf 3)));
                                        let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.transBy»
                                          (_root_.GebMirror.Metalogic.«HoleRose.readHyp»
                                            (_root_.Geb.Kernel.Const.add
                                              x12
                                              (_root_.Geb.Kernel.leaf 2)))
                                          (_root_.GebMirror.Metalogic.«HoleRose.normHyp»
                                            (_root_.Geb.Kernel.Const.add
                                              x12
                                              (_root_.Geb.Kernel.leaf 3)));
                                        _root_.GebMirror.Metalogic.«Base.bindO»
                                          (_root_.GebMirror.Metalogic.«HoleConditions.discharge»
                                            x0
                                            x1
                                            (_root_.GebMirror.Metalogic.«Prelude.append»
                                              x7
                                              (_root_.GebMirror.Metalogic.«Prelude.single» x11))
                                            x4)
                                          (fun (x17 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Base.bindO»
                                              (_root_.GebMirror.Metalogic.«HoleConditions.discharge»
                                                x0
                                                x1
                                                (_root_.GebMirror.Metalogic.«Prelude.append»
                                                  x7
                                                  (_root_.GebMirror.Metalogic.«Theory.l2» x11 x13))
                                                x5)
                                              (fun (x18 : _root_.Geb.Kernel.Tree) =>
                                                _root_.GebMirror.Metalogic.«Base.mapO»
                                                  (fun (x19 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«Prover.dNode»
                                                      (_root_.Geb.Kernel.leaf 33)
                                                      (_root_.GebMirror.Metalogic.«Theory.l3»
                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                          x2
                                                          (_root_.Geb.Kernel.leaf 0))
                                                        x9
                                                        x10)
                                                      (_root_.GebMirror.Metalogic.«Prelude.single»
                                                        (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                          x13
                                                          x17
                                                          (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                            x14
                                                            x18
                                                            (_root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                              x8
                                                              (_root_.GebMirror.Metalogic.«HoleRose.impElim»
                                                                x1
                                                                x11
                                                                x8
                                                                x19
                                                                (_root_.GebMirror.Metalogic.«HoleConditions.hypAt»
                                                                  x12))
                                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                                (_root_.Geb.Kernel.leaf 18)
                                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                                  x15
                                                                  x16)))))))
                                                  (_root_.GebMirror.Metalogic.«HoleConditions.specialize»
                                                    x0
                                                    x1
                                                    (_root_.GebMirror.Metalogic.«Prelude.append»
                                                      x7
                                                      (_root_.GebMirror.Metalogic.«Theory.l3» x11 x13 x14))
                                                    x6
                                                    (_root_.GebMirror.Metalogic.«Language.var»
                                                      (_root_.Geb.Kernel.leaf 0))))));
    x9

def «HoleCertificates.ledger» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «HoleCertificates.claimsOf» :=
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
                                 _root_.GebMirror.Metalogic.«Prover.termsOf» x3);
    x1

def «HoleCertificates.proofsOf» :=
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
                                 _root_.GebMirror.Metalogic.«Prover.termsOf» x5);
    x1

def «HoleCertificates.andThen» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229»);
    x2

def «HoleCertificates.containsClaim» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.anyT»
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.equal x1 x2)
      (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf» x0);
    x2

def «HoleCertificates.recordLemma» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x6).label ≠ 0 then
      let x8 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleCertificates.claimsOf»
        x7;
      let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.condition»
        x3
        x5;
      let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.close»
        x3
        x4
        x8
        x5
        (_root_.GebMirror.Metalogic.«Prelude.get» x6);
      if (_root_.GebMirror.Metalogic.«Conversion.thmConvChecks»
        x0
        x1
        x2
        (_root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
          (_root_.GebMirror.Metalogic.«Derivation.thArity» x5)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x8
          x9)
        x10).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229»
          (_root_.GebMirror.Metalogic.«HoleCertificates.ledger»
            (_root_.GebMirror.Metalogic.«Derivation.terms»
              (_root_.GebMirror.Metalogic.«Prelude.append»
                x8
                (_root_.GebMirror.Metalogic.«Prelude.single» x9)))
            (_root_.GebMirror.Metalogic.«Derivation.terms»
              (_root_.GebMirror.Metalogic.«Prelude.append»
                (_root_.GebMirror.Metalogic.«HoleCertificates.proofsOf» x7)
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    (_root_.GebMirror.Metalogic.«Theory.l2» x9 x10))))))
      else
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229»
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229»);
    x8

def «$284d61702e6d617020486f6c65506c616e2e5072656d697365205429» :=
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

def «HoleCertificates.regular» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x6)
      (_root_.Geb.Kernel.leaf 31)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Base.mapO»
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.dNode»
            (_root_.Geb.Kernel.leaf 31)
            (_root_.GebMirror.Metalogic.«Prelude.single» x8)
            ([] : _root_.List _root_.Geb.Kernel.Tree))
        (_root_.GebMirror.Metalogic.«HoleSequent.weakenSequent»
          x0
          x1
          x5
          (_root_.GebMirror.Metalogic.«Prelude.append»
            x4
            (_root_.GebMirror.Metalogic.«Derivation.thHyps» x5))
          (_root_.GebMirror.Metalogic.«Language.mD» x6 (_root_.Geb.Kernel.leaf 0)))
    else
      _root_.GebMirror.Metalogic.«Base.mapO»
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«HoleConditions.shifted»
            (_root_.GebMirror.Metalogic.«Prelude.length» x4)
            x6
            (_root_.Geb.Kernel.Const.children x8))
        (_root_.GebMirror.Metalogic.«Base.allSomeT»
          (_root_.GebMirror.Metalogic.«$284d61702e6d617020486f6c65506c616e2e5072656d697365205429»
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              let x9 : _root_.Geb.Kernel.Tree := x8;
              if (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.label x9)
                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                _root_.GebMirror.Metalogic.«Prelude.some»
                  (_root_.GebMirror.Metalogic.«HoleConditions.shiftTree»
                    (_root_.GebMirror.Metalogic.«Prelude.length» x4)
                    x11)
              else
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
                _root_.GebMirror.Metalogic.«HoleConditions.discharge» x2 x3 x4 x11)
            x7)));
    x8

def «HoleCertificates.roseLemmas» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.Geb.Kernel.Tree := (let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thArity»
                                           x5;
                                         let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                           (_root_.GebMirror.Metalogic.«Derivation.thCtx» x5)
                                           (_root_.Geb.Kernel.leaf 0);
                                         let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                           x6
                                           (_root_.Geb.Kernel.leaf 1);
                                         let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                           x6
                                           (_root_.Geb.Kernel.leaf 2);
                                         let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                           (_root_.GebMirror.Metalogic.«Derivation.thConcl» x5)
                                           (_root_.Geb.Kernel.leaf 0);
                                         let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                           (_root_.GebMirror.Metalogic.«Derivation.thConcl» x5)
                                           (_root_.Geb.Kernel.leaf 1);
                                         let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get»
                                           (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                             x0
                                             x10
                                             (_root_.GebMirror.Metalogic.«Derivation.thCtx» x5)
                                             x14);
                                         let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.rebuildList»
                                           x10
                                           x12
                                           x13;
                                         let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleRose.mapEquation»
                                           x3
                                           x10
                                           x12
                                           x13
                                           x11
                                           x16
                                           x14
                                           x15;
                                         let x19 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.theoremAt»
                                           x10
                                           (_root_.GebMirror.Metalogic.«Derivation.thCtx» x5)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (_root_.GebMirror.Metalogic.«Derivation.thConcl» x5);
                                         let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x12 x13 x16 x14)
                                           (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x12 x13 x16 x15);
                                         let x21 : _root_.Geb.Kernel.Tree →
                                           _root_.Geb.Kernel.Tree →
                                             _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleCertificates.recordLemma»
                                           x0
                                           x1
                                           x2
                                           x3
                                           x4;
                                         let x22 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«HoleCertificates.containsClaim»
                                           x9
                                           (_root_.GebMirror.Metalogic.«HoleConditions.condition»
                                             x3
                                             x17)).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229»
                                             x9
                                         else
                                           x21
                                             x17
                                             (_root_.GebMirror.Metalogic.«Prelude.some»
                                               (_root_.GebMirror.Metalogic.«HoleRose.rebuildProof» x12 x13))
                                             x9);
                                         _root_.GebMirror.Metalogic.«HoleCertificates.andThen»
                                           x22
                                           (fun (x23 : _root_.Geb.Kernel.Tree) =>
                                             let x24 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«HoleCertificates.containsClaim»
                                               x23
                                               (_root_.GebMirror.Metalogic.«HoleConditions.condition»
                                                 x3
                                                 x18)).label ≠ 0 then
                                               _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229»
                                                 x23
                                             else
                                               x21
                                                 x18
                                                 (_root_.GebMirror.Metalogic.«HoleRose.mapProof»
                                                   x3
                                                   x4
                                                   x10
                                                   x12
                                                   x13
                                                   x11
                                                   x16
                                                   x14
                                                   x15
                                                   (_root_.GebMirror.Metalogic.«HoleConditions.bodyAssumptions»
                                                     x3
                                                     (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf»
                                                       x23)
                                                     x18))
                                                 x23);
                                             _root_.GebMirror.Metalogic.«HoleCertificates.andThen»
                                               x24
                                               (fun (x25 : _root_.Geb.Kernel.Tree) =>
                                                 let x26 : _root_.Geb.Kernel.Tree := x21
                                                   x19
                                                   (_root_.GebMirror.Metalogic.«HoleRose.inductionBody»
                                                     x3
                                                     x4
                                                     x6
                                                     x19
                                                     x7
                                                     x8
                                                     x18
                                                     (_root_.GebMirror.Metalogic.«HoleConditions.bodyAssumptions»
                                                       x3
                                                       (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf»
                                                         x25)
                                                       x19)
                                                     x20)
                                                   x25;
                                                 if (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                                   (_root_.GebMirror.Metalogic.«Derivation.thHyps»
                                                     x5)).label ≠ 0 then
                                                   x26
                                                 else
                                                   _root_.GebMirror.Metalogic.«HoleCertificates.andThen»
                                                     x26
                                                     (fun (x27 : _root_.Geb.Kernel.Tree) =>
                                                       x21
                                                         x5
                                                         (_root_.GebMirror.Metalogic.«HoleConditions.discharge»
                                                           x3
                                                           x4
                                                           (_root_.GebMirror.Metalogic.«Prelude.append»
                                                             (_root_.GebMirror.Metalogic.«HoleConditions.bodyAssumptions»
                                                               x3
                                                               (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf»
                                                                 x27)
                                                               x5)
                                                             (_root_.GebMirror.Metalogic.«Derivation.thHyps»
                                                               x5))
                                                           x19)
                                                         x27))));
    x10

def «$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e5072656d69736529» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420486f6c65506c616e2e5072656d69736529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$284f7074696f6e2e6e74684f6620486f6c65506c616e2e5072656d69736529» :=
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
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c65506c616e2e5072656d69736529»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c65506c616e2e5072656d69736529»
          x2);
    x2

def «HoleCertificates.asGoal» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620486f6c65506c616e2e5072656d69736529»
                                          x0
                                          x1;
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
                                          let x6 : _root_.Geb.Kernel.Tree := x4;
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
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a7573742044657269766174696f6e2e54686d29»
                                              x8
                                          else
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e672044657269766174696f6e2e54686d29»
                                        else
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e672044657269766174696f6e2e54686d29»);
    x2

def «HoleCertificates.synthesize» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := (let x7 : _root_.Geb.Kernel.Tree := x5;
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
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        if (_root_.GebMirror.Metalogic.«HoleCertificates.containsClaim»
                                          x6
                                          (_root_.GebMirror.Metalogic.«HoleConditions.condition»
                                            x3
                                            x9)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229»
                                            x6
                                        else
                                          let x15 : _root_.Geb.Kernel.Tree := x13;
                                          let x16 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x15;
                                          let x17 : _root_.List _root_.Geb.Kernel.Tree := x16;
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x11)
                                            (_root_.Geb.Kernel.leaf 32)).label ≠ 0 then
                                            let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleCertificates.asGoal»
                                              x17
                                              (_root_.Geb.Kernel.leaf 0);
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x18)
                                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                              let x19 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x18;
                                              let x20 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.Geb.Kernel.Tree)
                                                x19
                                                (_root_.Geb.Kernel.leaf 0)
                                                (fun (x20 : _root_.Geb.Kernel.Tree)
                                                   (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                  x20);
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.List _root_.Geb.Kernel.Tree)
                                                x19
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (fun (_ : _root_.Geb.Kernel.Tree)
                                                   (x22 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                  x22);
                                              let x22 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleCertificates.asGoal»
                                                x17
                                                (_root_.Geb.Kernel.leaf 1);
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x22)
                                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                let x23 : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x22;
                                                let x24 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.Geb.Kernel.Tree)
                                                  x23
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (fun (x24 : _root_.Geb.Kernel.Tree)
                                                     (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x24);
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x23
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x26 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x26);
                                                _root_.GebMirror.Metalogic.«HoleCertificates.roseLemmas»
                                                  x0
                                                  x1
                                                  x2
                                                  x3
                                                  x4
                                                  x9
                                                  x11
                                                  x20
                                                  x24
                                                  x6
                                              else
                                                _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229»
                                            else
                                              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720486f6c654365727469666963617465732e4c656467657229»
                                          else
                                            _root_.GebMirror.Metalogic.«HoleCertificates.recordLemma»
                                              x0
                                              x1
                                              x2
                                              x3
                                              x4
                                              x9
                                              (_root_.GebMirror.Metalogic.«HoleCertificates.regular»
                                                x0
                                                x1
                                                x3
                                                x4
                                                (_root_.GebMirror.Metalogic.«HoleConditions.bodyAssumptions»
                                                  x3
                                                  (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf» x6)
                                                  x9)
                                                x9
                                                x11
                                                x17)
                                              x6);
    x7

def «HoleCertificates.assemble» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HoleConditions.condition»
                                          x0
                                          x3;
                                        _root_.GebMirror.Metalogic.«Base.mapO»
                                          (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«HoleConditions.implyFrom»
                                              x0
                                              x1
                                              (_root_.Geb.Kernel.leaf 0)
                                              x2
                                              x5
                                              (_root_.Geb.Kernel.Const.foldr
                                                (α := _root_.Geb.Kernel.Tree)
                                                (β := _root_.Geb.Kernel.Tree)
                                                (fun (x7 : _root_.Geb.Kernel.Tree)
                                                   (x8 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«HoleRose.cutBy»
                                                    (_root_.Geb.Kernel.Const.child
                                                      x7
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    (_root_.Geb.Kernel.Const.child
                                                      x7
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    x8)
                                                x6
                                                (_root_.GebMirror.Metalogic.«HoleCertificates.proofsOf» x4)))
                                          (_root_.GebMirror.Metalogic.«HoleConditions.hypothesis»
                                            (_root_.GebMirror.Metalogic.«HoleCertificates.claimsOf» x4)
                                            x5));
    x5

def «$285365712e7265766572736520486f6c65506c616e2e50726f6f664e6f646529» :=
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

def «HoleCertificates.candidate» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«HolePlan.plan»
                                          x0
                                          x1
                                          x2
                                          x7
                                          x6;
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
                                          let x12 : _root_.Geb.Kernel.Tree := x10;
                                          let x13 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x12;
                                          let x14 : _root_.List _root_.Geb.Kernel.Tree := x13;
                                          let x15 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
                                            (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«HoleConditions.condition» x3 (x5 x15))
                                            (_root_.GebMirror.Metalogic.«ProofHoles.holes» x7);
                                          let x16 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            (fun (x16 : _root_.Geb.Kernel.Tree)
                                               (x17 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«HoleCertificates.andThen»
                                                x17
                                                (_root_.GebMirror.Metalogic.«HoleCertificates.synthesize»
                                                  x0
                                                  x1
                                                  x2
                                                  x3
                                                  x4
                                                  x16))
                                            (_root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420486f6c654365727469666963617465732e4c656467657229»
                                              (_root_.GebMirror.Metalogic.«HoleCertificates.ledger»
                                                (_root_.GebMirror.Metalogic.«Derivation.terms» x15)
                                                (_root_.GebMirror.Metalogic.«Derivation.terms»
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                            (_root_.GebMirror.Metalogic.«$285365712e7265766572736520486f6c65506c616e2e50726f6f664e6f646529»
                                              x14);
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
                                            _root_.GebMirror.Metalogic.«HoleCertificates.assemble»
                                              x3
                                              x4
                                              x15
                                              x6
                                              x18
                                          else
                                            _root_.GebMirror.Metalogic.«Prelude.none»
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x8

def «HoleCertificates.certify» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«ProofHoles.checks»
      x0
      x1
      x2
      x5
      x6
      x7).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«HoleCertificates.candidate» x0 x1 x2 x3 x4 x5 x6 x7)
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«Conversion.thmConvChecks»
            x0
            x1
            x2
            (_root_.GebMirror.Metalogic.«HoleConditions.conditional» x3 x5 x6 x7)
            x8).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» x8
          else
            _root_.GebMirror.Metalogic.«Prelude.none»)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x8

end GebMirror.Metalogic

end
