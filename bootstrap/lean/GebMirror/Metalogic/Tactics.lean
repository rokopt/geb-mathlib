module

public import GebMirror.Metalogic.Conversion

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Tactics.bindTh» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.bindAT» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.pr0» :=
  _root_.GebMirror.Metalogic.«Language.pr»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Tactics.nfr0» :=
  _root_.GebMirror.Metalogic.«Prover.nfr»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Prover.mark»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0))

def «Tactics.ttL» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mDefn»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «Tactics.impL» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mDefn»
      (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2» x2 x1);
    x3

def «Tactics.trueI» :=
  _root_.GebMirror.Metalogic.«Prover.dNode»
    (_root_.Geb.Kernel.leaf 23)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    (_root_.GebMirror.Metalogic.«Theory.l2»
      (_root_.GebMirror.Metalogic.«Prover.dNode»
        (_root_.Geb.Kernel.leaf 8)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«Prover.dNode»
        (_root_.Geb.Kernel.leaf 18)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Theory.l2»
          (_root_.GebMirror.Metalogic.«Prover.dNode»
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          (_root_.GebMirror.Metalogic.«Prover.dNode»
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            ([] : _root_.List _root_.Geb.Kernel.Tree)))))

def «Tactics.impI» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 23)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 8)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          ([] : _root_.List _root_.Geb.Kernel.Tree))
        (_root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 25)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«Theory.l2»
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 27)
              (_root_.GebMirror.Metalogic.«Theory.l3»
                (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 2))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  (_root_.GebMirror.Metalogic.«Theory.l2» x3 x2)))
              (_root_.GebMirror.Metalogic.«Prelude.single»
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 21)
                  (_root_.GebMirror.Metalogic.«Prelude.single» x1)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))))
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 27)
              (_root_.GebMirror.Metalogic.«Theory.l3»
                (_root_.Geb.Kernel.Const.add x0 (_root_.Geb.Kernel.leaf 1))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  (_root_.GebMirror.Metalogic.«Theory.l2» x3 x2)))
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 21)
                  (_root_.GebMirror.Metalogic.«Prelude.single» x1)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
                x4)))));
    x5

def «Tactics.apps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        x3 (_root_.GebMirror.Metalogic.«Language.app» x4 x2))
      (fun (x2 : _root_.Geb.Kernel.Tree) => x2)
      x1
      x0;
    x2

def «Tactics.byMode» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.joinBy»
        (_root_.GebMirror.Metalogic.«Prover.eval»
          x1
          x2
          x3
          x4
          (_root_.Geb.Kernel.leaf 4096)
          x0)
        x5
        x6
        x7
        x8);
    x5

def «Tactics.byWeak» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.byMode»
      (_root_.Geb.Kernel.leaf 1)
      x0
      x1
      x2
      x3;
    x4

def «Tactics.byNF» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.bindNT»
        (_root_.GebMirror.Metalogic.«Prover.eval»
          x0
          x1
          x2
          x3
          (_root_.Geb.Kernel.leaf 4096)
          x4
          x6
          x7
          x8)
        (fun (x10 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.bindNT»
            (_root_.GebMirror.Metalogic.«Prover.eval»
              x0
              x1
              x2
              x3
              (_root_.Geb.Kernel.leaf 4096)
              x4
              x6
              x7
              x9)
            (fun (x11 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Base.mapO»
                (fun (x12 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Prover.dNode»
                    (_root_.Geb.Kernel.leaf 23)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Theory.l2»
                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 2)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                            (_root_.GebMirror.Metalogic.«Prover.nfMarked» x10))
                          (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                            (_root_.GebMirror.Metalogic.«Prover.nfMarked» x11))))
                      x12))
                (x5
                  x6
                  x7
                  (_root_.GebMirror.Metalogic.«Prover.nfTerm» x10)
                  (_root_.GebMirror.Metalogic.«Prover.nfTerm» x11)))));
    x6

def «Tactics.appendNR» :=
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

def «Tactics.hypRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nrHyp» x0;
    x1

def «Tactics.hypRules» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((_root_.GebMirror.Metalogic.«Tactics.hypRule» x1) :: x2))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Base.range» x0);
    x1

def «Tactics.normH» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.byNormW»
        x0
        x1
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.Metalogic.«Tactics.appendNR»
          (_root_.GebMirror.Metalogic.«Tactics.hypRules»
            (_root_.GebMirror.Metalogic.«Prelude.length» x4))
          x2)
        (_root_.Geb.Kernel.leaf 1024)
        x3
        x4
        x5
        x6);
    x3

def «Tactics.funExts» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.byFunExt» x1 (_root_.Geb.Kernel.leaf 0) x3)
      x2
      x0;
    x3

def «Tactics.byListIndWeak» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        x5
        _root_.GebMirror.Metalogic.«Prelude.none»
        (fun (x9 : _root_.Geb.Kernel.Tree)
           (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Language.listPart» x9)
            (fun (x11 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.bindHT»
                (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x2 x10 x6)
                (fun (x12 : _root_.Geb.Kernel.Tree) =>
                  let x13 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x12;
                  let x14 : _root_.List _root_.Geb.Kernel.Tree := (x9 :: (x11 :: x10));
                  let x15 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
                    _root_.GebMirror.Metalogic.«Derivation.weaken2»
                    x13;
                  _root_.GebMirror.Metalogic.«Base.bindO»
                    (_root_.GebMirror.Metalogic.«Tactics.byWeak»
                      x0
                      x1
                      x2
                      x4
                      x10
                      x13
                      (_root_.GebMirror.Metalogic.«Prover.instAt»
                        (_root_.Geb.Kernel.leaf 0)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x11)
                        x7)
                      (_root_.GebMirror.Metalogic.«Prover.instAt»
                        (_root_.Geb.Kernel.leaf 0)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x11)
                        x8))
                    (fun (x16 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.bindO»
                        (_root_.GebMirror.Metalogic.«Tactics.byWeak»
                          x0
                          x1
                          x2
                          x4
                          x14
                          x15
                          (_root_.GebMirror.Metalogic.«Derivation.listConsAt»
                            (_root_.Geb.Kernel.leaf 1)
                            x11
                            x7)
                          (_root_.GebMirror.Metalogic.«Language.subst»
                            x3
                            (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                              (_root_.GebMirror.Metalogic.«Derivation.weakenElem» x7))))
                        (fun (x17 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Base.mapO»
                            (fun (x18 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 20)
                                (_root_.GebMirror.Metalogic.«Theory.l3»
                                  (_root_.Geb.Kernel.leaf 0)
                                  (_root_.Geb.Kernel.leaf 1)
                                  x3)
                                (_root_.GebMirror.Metalogic.«Theory.l3» x16 x17 x18))
                            (_root_.GebMirror.Metalogic.«Tactics.byWeak»
                              x0
                              x1
                              x2
                              x4
                              x14
                              x15
                              (_root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                (_root_.Geb.Kernel.leaf 1)
                                x11
                                x8)
                              (_root_.GebMirror.Metalogic.«Language.subst»
                                x3
                                (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                  (_root_.GebMirror.Metalogic.«Derivation.weakenElem» x8))))))))));
    x5

def «Tactics.byRoseIndWith» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (_ : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree) =>
      if (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
          x4
          (_root_.Geb.Kernel.leaf 0);
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Language.roseLabel» x8)
          (fun (x9 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Base.bindO»
              (_root_.GebMirror.Metalogic.«Derivation.typeIn» x0 x1 x4 x6)
              (fun (x10 : _root_.Geb.Kernel.Tree) =>
                let x11 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l2»
                  (_root_.GebMirror.Metalogic.«Theory.list» x8)
                  x9;
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (x3
                    x11
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt»
                      (_root_.Geb.Kernel.leaf 2)
                      x8
                      x9
                      x6)
                    (_root_.GebMirror.Metalogic.«Language.subst»
                      x2
                      (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                        (_root_.GebMirror.Metalogic.«Derivation.roseMapAt»
                          (_root_.Geb.Kernel.leaf 0)
                          (_root_.Geb.Kernel.leaf 1)
                          x10
                          x6))))
                  (fun (x12 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Base.mapO»
                      (fun (x13 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 32)
                          (_root_.GebMirror.Metalogic.«Theory.l4»
                            (_root_.Geb.Kernel.leaf 2)
                            (_root_.Geb.Kernel.leaf 0)
                            (_root_.Geb.Kernel.leaf 1)
                            x2)
                          (_root_.GebMirror.Metalogic.«Theory.l2» x12 x13))
                      (x3
                        x11
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt»
                          (_root_.Geb.Kernel.leaf 2)
                          x8
                          x9
                          x7)
                        (_root_.GebMirror.Metalogic.«Language.subst»
                          x2
                          (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                            (_root_.GebMirror.Metalogic.«Derivation.roseMapAt»
                              (_root_.Geb.Kernel.leaf 0)
                              (_root_.Geb.Kernel.leaf 1)
                              x10
                              x7)))))))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

def «Tactics.applyAbs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 22)
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Language.mEq» x2 x3))
      (_root_.GebMirror.Metalogic.«Theory.l2»
        x4
        (_root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 24)
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Language.mEq»
              (_root_.GebMirror.Metalogic.«Language.app» x2 x0)
              (_root_.GebMirror.Metalogic.«Language.app» x3 x0)))
          (_root_.GebMirror.Metalogic.«Theory.l2»
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 2)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 3)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 3)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))))
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 18)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 2)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 17)
                      (_root_.GebMirror.Metalogic.«Theory.l2» x1 (_root_.Geb.Kernel.leaf 0))
                      ([] : _root_.List _root_.Geb.Kernel.Tree))
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 0)
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      ([] : _root_.List _root_.Geb.Kernel.Tree))))
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)))))));
    x5

def «Tactics.byListSplit» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x5 x2)
        (fun (x9 : _root_.Geb.Kernel.Tree) =>
          let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
            x2
            x9
            x7;
          let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
            x2
            x9
            x8;
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x12 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Tactics.applyAbs»
                (_root_.GebMirror.Metalogic.«Language.var» x2)
                (_root_.GebMirror.Metalogic.«Prelude.length» x6)
                x10
                x11
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 26)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Prelude.single» x12)))
            (_root_.GebMirror.Metalogic.«Prover.byListIndWith»
              x0
              x1
              (_root_.Geb.Kernel.leaf 0)
              (_root_.Geb.Kernel.leaf 1)
              x3
              x4
              (x9 :: x5)
              (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x6)
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Derivation.weaken1» x10)
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Derivation.weaken1» x11)
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))));
    x5

def «Tactics.bySplit2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x5 x2)
        (fun (x9 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Derivation.bindPT»
            (_root_.GebMirror.Metalogic.«Language.coprodParts» x9)
            (fun (x10 : _root_.Geb.Kernel.Tree) =>
              let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x10;
              let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p2» x10;
              let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
                x2
                x9
                x7;
              let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
                x2
                x9
                x8;
              let x15 : _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree := (fun (x15 : _root_.Geb.Kernel.Tree)
                                               (x16 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Derivation.weaken1» x16)
                  (_root_.GebMirror.Metalogic.«Language.mArr»
                    x15
                    (_root_.GebMirror.Metalogic.«Theory.l2» x11 x12)
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))));
              _root_.GebMirror.Metalogic.«Base.bindO»
                (x3
                  (x11 :: x5)
                  (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x6)
                  (x15 x0 x13)
                  (x15 x0 x14))
                (fun (x16 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Base.mapO»
                    (fun (x17 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Tactics.applyAbs»
                        (_root_.GebMirror.Metalogic.«Language.var» x2)
                        (_root_.GebMirror.Metalogic.«Prelude.length» x6)
                        x13
                        x14
                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 26)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 34)
                              (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1)
                              (_root_.GebMirror.Metalogic.«Theory.l2» x16 x17)))))
                    (x4
                      (x12 :: x5)
                      (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x6)
                      (x15 x1 x13)
                      (x15 x1 x14))))));
    x5

def «Tactics.byListCases» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.byListIndWith»
      x0
      x1
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      x2
      x2;
    x3

def «Tactics.bitsInd» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.byListIndWith»
      x0
      x1
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      x2
      (_root_.GebMirror.Metalogic.«Prover.bySplit»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 4)
        (_root_.Geb.Kernel.leaf 1)
        x3);
    x4

def «Tactics.bitsCases» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.bitsInd»
      x0
      x1
      x2
      x2;
    x3

def «Tactics.byBits» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.byListSplit»
          x0
          (_root_.Geb.Kernel.leaf 0)
          x4
          x1
          (_root_.GebMirror.Metalogic.«Tactics.bySplit2»
            (_root_.Geb.Kernel.leaf 3)
            (_root_.Geb.Kernel.leaf 4)
            (_root_.Geb.Kernel.leaf 1)
            (x3 (_root_.Geb.Kernel.leaf 1))
            (x3 (_root_.Geb.Kernel.leaf 1))))
      (fun (_ : _root_.Geb.Kernel.Tree) => x1)
      x2;
    x3

def «Tactics.byLength3» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.byListSplit»
      x0
      (_root_.Geb.Kernel.leaf 0)
      x1
      x3
      (_root_.GebMirror.Metalogic.«Tactics.byListSplit»
        x0
        (_root_.Geb.Kernel.leaf 0)
        (_root_.Geb.Kernel.leaf 0)
        x3
        (_root_.GebMirror.Metalogic.«Tactics.byListSplit»
          x0
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.leaf 0)
          x3
          (_root_.GebMirror.Metalogic.«Tactics.byListSplit»
            x0
            (_root_.Geb.Kernel.leaf 0)
            (_root_.Geb.Kernel.leaf 0)
            x2
            x3)));
    x4

def «Tactics.rules» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Tactics.frames» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Tactics.wh» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «$284f7074696f6e2e6e6f7468696e6720546163746963732e574829» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420546163746963732e574829» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Tactics.bindPW» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e574829»);
    x2

def «Tactics.bindNW» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e574829»);
    x2

def «Tactics.weakHyps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x8 : _root_.Geb.Kernel.Tree)
         (x9 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x10 : _root_.List _root_.Geb.Kernel.Tree)
         (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.bindPW»
          (_root_.GebMirror.Metalogic.«Language.bindTP»
            (_root_.GebMirror.Metalogic.«Prelude.nth» x10 x8)
            _root_.GebMirror.Metalogic.«Derivation.eqParts»)
          (fun (x12 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Tactics.bindNW»
              (_root_.GebMirror.Metalogic.«Prover.eval»
                x0
                x1
                x2
                x3
                (_root_.Geb.Kernel.leaf 4096)
                x5
                x6
                x10
                (_root_.GebMirror.Metalogic.«Language.p1» x12))
              (fun (x13 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Tactics.bindNW»
                  (_root_.GebMirror.Metalogic.«Prover.eval»
                    x0
                    x1
                    x2
                    x3
                    (_root_.Geb.Kernel.leaf 4096)
                    x5
                    x6
                    x10
                    (_root_.GebMirror.Metalogic.«Language.p2» x12))
                  (fun (x14 : _root_.Geb.Kernel.Tree) =>
                    let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                      (_root_.GebMirror.Metalogic.«Prover.nfTerm» x13)
                      (_root_.GebMirror.Metalogic.«Prover.nfTerm» x14);
                    let x16 : _root_.Geb.Kernel.Tree := x9
                      (_root_.GebMirror.Metalogic.«Prelude.append»
                        x10
                        (_root_.GebMirror.Metalogic.«Prelude.single» x15))
                      (_root_.GebMirror.Metalogic.«Tactics.appendNR»
                        x11
                        ((_root_.GebMirror.Metalogic.«Tactics.hypRule»
                          (_root_.GebMirror.Metalogic.«Prelude.length» x10)) ::
                          ([] : _root_.List _root_.Geb.Kernel.Tree)));
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
                      let x20 : _root_.Geb.Kernel.Tree := x18;
                      let x21 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x20;
                      let x22 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        x21
                        (_root_.Geb.Kernel.leaf 0)
                        (fun (x22 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          x22);
                      let x23 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.List _root_.Geb.Kernel.Tree)
                        x21
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (fun (_ : _root_.Geb.Kernel.Tree)
                           (x24 : _root_.List _root_.Geb.Kernel.Tree) =>
                          x24);
                      let x24 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        x23
                        (_root_.Geb.Kernel.leaf 0)
                        (fun (x24 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          x24);
                      let x25 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.List _root_.Geb.Kernel.Tree)
                        x23
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (fun (_ : _root_.Geb.Kernel.Tree)
                           (x26 : _root_.List _root_.Geb.Kernel.Tree) =>
                          x26);
                      let x26 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        x25
                        (_root_.Geb.Kernel.leaf 0)
                        (fun (x26 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          x26);
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.List _root_.Geb.Kernel.Tree)
                        x25
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (fun (_ : _root_.Geb.Kernel.Tree)
                           (x28 : _root_.List _root_.Geb.Kernel.Tree) =>
                          x28);
                      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420546163746963732e574829»
                        (_root_.GebMirror.Metalogic.«Tactics.wh»
                          x22
                          x24
                          (_root_.GebMirror.Metalogic.«Tactics.frames»
                            ((_root_.GebMirror.Metalogic.«Language.pr»
                              x15
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 24)
                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                  (_root_.GebMirror.Metalogic.«Language.mEq»
                                    (_root_.GebMirror.Metalogic.«Language.p1» x12)
                                    (_root_.GebMirror.Metalogic.«Language.p2» x12)))
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                    (_root_.Geb.Kernel.leaf 2)
                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                    (_root_.GebMirror.Metalogic.«Theory.l2»
                                      (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x13))
                                      (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x14))))
                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                    (_root_.Geb.Kernel.leaf 21)
                                    (_root_.GebMirror.Metalogic.«Prelude.single» x8)
                                    ([] : _root_.List _root_.Geb.Kernel.Tree))))) ::
                              (let x28 : _root_.Geb.Kernel.Tree := x26;
                               let x29 : _root_.List
                                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x28;
                               let x30 : _root_.List _root_.Geb.Kernel.Tree := x29; x30))))
                    else
                      let _ : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e574829»))))
      (fun (x8 : _root_.List _root_.Geb.Kernel.Tree)
         (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420546163746963732e574829»
          (_root_.GebMirror.Metalogic.«Tactics.wh»
            (_root_.GebMirror.Metalogic.«Derivation.terms» x8)
            (_root_.GebMirror.Metalogic.«Tactics.rules» x9)
            (_root_.GebMirror.Metalogic.«Tactics.frames»
              ([] : _root_.List _root_.Geb.Kernel.Tree))))
      x4
      x7
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x8

def «Tactics.withWeakHyps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree) =>
      let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.weakHyps»
        x0
        x1
        x2
        x3
        x4
        x6
        x7
        x8;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x11)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x12 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x11;
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
        let x15 : _root_.Geb.Kernel.Tree := x13;
        let x16 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
        let x17 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x16
          (_root_.Geb.Kernel.leaf 0)
          (fun (x17 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x17);
        let x18 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x16
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x19 : _root_.List _root_.Geb.Kernel.Tree) =>
            x19);
        let x19 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x18
          (_root_.Geb.Kernel.leaf 0)
          (fun (x19 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x19);
        let x20 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x18
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x21 : _root_.List _root_.Geb.Kernel.Tree) =>
            x21);
        let x21 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x20
          (_root_.Geb.Kernel.leaf 0)
          (fun (x21 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x21);
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x20
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x23 : _root_.List _root_.Geb.Kernel.Tree) =>
            x23);
        _root_.GebMirror.Metalogic.«Base.mapO»
          (fun (x23 : _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.Const.foldr
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              (fun (x24 : _root_.Geb.Kernel.Tree) (x25 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 22)
                  (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.GebMirror.Metalogic.«Language.p1» x24))
                  (_root_.GebMirror.Metalogic.«Theory.l2» (_root_.GebMirror.Metalogic.«Language.p2» x24) x25))
              x23
              (let x24 : _root_.Geb.Kernel.Tree := x21;
               let x25 : _root_.List
                 _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x24;
               let x26 : _root_.List _root_.Geb.Kernel.Tree := x25; x26))
          (x5
            (let x23 : _root_.Geb.Kernel.Tree := x19;
             let x24 : _root_.List
               _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x23;
             let x25 : _root_.List _root_.Geb.Kernel.Tree := x24; x25)
            x7
            (_root_.GebMirror.Metalogic.«Prover.termsOf» x17)
            x9
            x10)
      else
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x11;
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x7

def «Tactics.byListIndHypWeak» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.byListIndWith»
      x0
      x2
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Tactics.byWeak» x0 x1 x2 x3)
      (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree)
         (x6 : _root_.Geb.Kernel.Tree)
         (x7 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.withWeakHyps»
          x0
          x1
          x2
          x3
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.Geb.Kernel.Const.sub
              (_root_.GebMirror.Metalogic.«Prelude.length» x5)
              (_root_.Geb.Kernel.leaf 1)))
          (fun (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Tactics.byWeak»
              x0
              x1
              x2
              (_root_.GebMirror.Metalogic.«Tactics.appendNR» x8 x3))
          (_root_.Geb.Kernel.leaf 1)
          x4
          x5
          x6
          x7);
    x4

def «Tactics.byBitsIndHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.byListIndWith»
      x0
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Tactics.byMode»
        x3
        x0
        x1
        (_root_.Geb.Kernel.leaf 0)
        x2)
      (_root_.GebMirror.Metalogic.«Prover.bySplit»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 4)
        (_root_.Geb.Kernel.leaf 1)
        (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
           (x5 : _root_.List _root_.Geb.Kernel.Tree)
           (x6 : _root_.Geb.Kernel.Tree)
           (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Tactics.withWeakHyps»
            x0
            x1
            (_root_.Geb.Kernel.leaf 0)
            x2
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.Geb.Kernel.Const.sub
                (_root_.GebMirror.Metalogic.«Prelude.length» x5)
                (_root_.Geb.Kernel.leaf 1)))
            (fun (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Tactics.byMode»
                x3
                x0
                x1
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Tactics.appendNR» x8 x2))
            x3
            x4
            x5
            x6
            x7));
    x4

def «Tactics.rwFun» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 2)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«Theory.l2»
            x2
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 0)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              ([] : _root_.List _root_.Geb.Kernel.Tree))))
      (_root_.GebMirror.Metalogic.«Prover.dNode»
        (_root_.Geb.Kernel.leaf 17)
        (_root_.GebMirror.Metalogic.«Theory.l2» x0 (_root_.Geb.Kernel.leaf 0))
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x1;
    x2

def «Tactics.instEqs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((_root_.GebMirror.Metalogic.«Language.mEq»
          (_root_.GebMirror.Metalogic.«Tactics.apps» x0 x3)
          (_root_.GebMirror.Metalogic.«Tactics.apps» x1 x3)) ::
          x4))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x2;
    x3

def «Tactics.cutInsts» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
         (x6 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 22)
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Language.mEq»
              (_root_.GebMirror.Metalogic.«Tactics.apps» x0 x5)
              (_root_.GebMirror.Metalogic.«Tactics.apps» x1 x5)))
          (_root_.GebMirror.Metalogic.«Theory.l2»
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 18)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Tactics.rwFun»
                  x2
                  (_root_.GebMirror.Metalogic.«Prelude.length» x5))
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))))
            x6))
      x4
      x3;
    x5

def «Tactics.withInsts» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree)
                                         (x11 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Derivation.bindPT»
        (_root_.GebMirror.Metalogic.«Language.bindTP»
          (_root_.GebMirror.Metalogic.«Prelude.nth» x9 x4)
          _root_.GebMirror.Metalogic.«Derivation.eqParts»)
        (fun (x12 : _root_.Geb.Kernel.Tree) =>
          let x13 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.instEqs»
            (_root_.GebMirror.Metalogic.«Language.p1» x12)
            (_root_.GebMirror.Metalogic.«Language.p2» x12)
            x5;
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x14 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Tactics.cutInsts»
                (_root_.GebMirror.Metalogic.«Language.p1» x12)
                (_root_.GebMirror.Metalogic.«Language.p2» x12)
                x4
                x5
                x14)
            (_root_.GebMirror.Metalogic.«Tactics.withWeakHyps»
              x0
              x1
              x2
              x3
              (_root_.GebMirror.Metalogic.«Base.mapT»
                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                  _root_.Geb.Kernel.Const.add (_root_.GebMirror.Metalogic.«Prelude.length» x9) x14)
                (_root_.GebMirror.Metalogic.«Base.range» (_root_.GebMirror.Metalogic.«Prelude.length» x13)))
              x6
              x7
              x8
              (_root_.GebMirror.Metalogic.«Prelude.append» x9 x13)
              x10
              x11)));
    x8

def «Tactics.nthOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 8)
      (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Theory.omega»)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.GebMirror.Metalogic.«Language.mEq»
          _root_.GebMirror.Metalogic.«Language.mStar»
          _root_.GebMirror.Metalogic.«Language.mStar»)
        (_root_.Geb.Kernel.Const.iter
          (α := _root_.Geb.Kernel.Tree)
          (fun (x2 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Translation.call»
              (_root_.Geb.Kernel.leaf 7)
              (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Theory.omega»)
              (_root_.GebMirror.Metalogic.«Prelude.single» x2))
          x0
          x1));
    x2

def «Tactics.withChildHyps» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree →
      _root_.List (_root_.List _root_.Geb.Kernel.Tree))
    (x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree)
                                         (x11 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Derivation.bindPT»
        (_root_.GebMirror.Metalogic.«Language.bindTP»
          (_root_.GebMirror.Metalogic.«Prelude.nth» x9 x4)
          _root_.GebMirror.Metalogic.«Derivation.eqParts»)
        (fun (x12 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.foldr
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
            (fun (x13 : _root_.Geb.Kernel.Tree)
               (x14 : _root_.List _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
               (x15 : _root_.List _root_.Geb.Kernel.Tree)
               (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
              let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.nthOf»
                (_root_.GebMirror.Metalogic.«Language.p1» x12)
                x13;
              let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.nthOf»
                (_root_.GebMirror.Metalogic.«Language.p2» x12)
                x13;
              _root_.GebMirror.Metalogic.«Prover.bindNT»
                (_root_.GebMirror.Metalogic.«Prover.eval»
                  x0
                  x1
                  x2
                  x3
                  (_root_.Geb.Kernel.leaf 4096)
                  (_root_.Geb.Kernel.leaf 1)
                  x8
                  x15
                  x17)
                (fun (x19 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Prover.bindNT»
                    (_root_.GebMirror.Metalogic.«Prover.eval»
                      x0
                      x1
                      x2
                      x3
                      (_root_.Geb.Kernel.leaf 4096)
                      (_root_.Geb.Kernel.leaf 1)
                      x8
                      x15
                      x18)
                    (fun (x20 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Prover.bindNT»
                        (_root_.GebMirror.Metalogic.«Prover.eval»
                          x0
                          x1
                          x2
                          ((_root_.GebMirror.Metalogic.«Tactics.hypRule» x4) ::
                            ([] : _root_.List _root_.Geb.Kernel.Tree))
                          (_root_.Geb.Kernel.leaf 4096)
                          (_root_.Geb.Kernel.leaf 1)
                          x8
                          x15
                          x17)
                        (fun (x21 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Derivation.bindPT»
                            (_root_.GebMirror.Metalogic.«Derivation.eqParts»
                              (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19))
                            (fun (x22 : _root_.Geb.Kernel.Tree) =>
                              let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                x15;
                              let x24 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                                x23
                                (_root_.Geb.Kernel.leaf 1);
                              let x25 : _root_.List (_root_.List _root_.Geb.Kernel.Tree) := x6 x13;
                              let x26 : _root_.List
                                _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.instEqs»
                                (_root_.GebMirror.Metalogic.«Language.p1» x22)
                                (_root_.GebMirror.Metalogic.«Language.p2» x22)
                                x25;
                              _root_.GebMirror.Metalogic.«Base.mapO»
                                (fun (x27 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«Prover.dNode»
                                    (_root_.Geb.Kernel.leaf 22)
                                    (_root_.GebMirror.Metalogic.«Prelude.single»
                                      (_root_.GebMirror.Metalogic.«Language.mEq»
                                        (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19)
                                        (_root_.GebMirror.Metalogic.«Prover.nfTerm» x20)))
                                    (_root_.GebMirror.Metalogic.«Theory.l2»
                                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                                        (_root_.Geb.Kernel.leaf 24)
                                        (_root_.GebMirror.Metalogic.«Prelude.single»
                                          (_root_.GebMirror.Metalogic.«Language.mEq» x17 x18))
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                            (_root_.Geb.Kernel.leaf 2)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                                (_root_.GebMirror.Metalogic.«Prover.nfMarked» x19))
                                              (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                                (_root_.GebMirror.Metalogic.«Prover.nfMarked» x20))))
                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                            (_root_.Geb.Kernel.leaf 18)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                                (_root_.GebMirror.Metalogic.«Prover.nfMarked» x21))
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 0)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree))))))
                                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                                        (_root_.Geb.Kernel.leaf 22)
                                        (_root_.GebMirror.Metalogic.«Prelude.single»
                                          (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19))
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                            (_root_.Geb.Kernel.leaf 23)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 17)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  x23
                                                  (_root_.Geb.Kernel.leaf 0))
                                                ([] : _root_.List _root_.Geb.Kernel.Tree))
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 18)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree))))))
                                          (_root_.GebMirror.Metalogic.«Tactics.cutInsts»
                                            (_root_.GebMirror.Metalogic.«Language.p1» x22)
                                            (_root_.GebMirror.Metalogic.«Language.p2» x22)
                                            x24
                                            x25
                                            x27)))))
                                (x14
                                  (_root_.GebMirror.Metalogic.«Prelude.append»
                                    (_root_.GebMirror.Metalogic.«Prelude.append»
                                      x15
                                      (_root_.GebMirror.Metalogic.«Theory.l2»
                                        (_root_.GebMirror.Metalogic.«Language.mEq»
                                          (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19)
                                          (_root_.GebMirror.Metalogic.«Prover.nfTerm» x20))
                                        (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19)))
                                    x26)
                                  (_root_.GebMirror.Metalogic.«Prelude.append»
                                    x16
                                    (_root_.GebMirror.Metalogic.«Base.mapT»
                                      (fun (x27 : _root_.Geb.Kernel.Tree) =>
                                        _root_.Geb.Kernel.Const.add
                                          (_root_.Geb.Kernel.Const.add
                                            x24
                                            (_root_.Geb.Kernel.leaf 1))
                                          x27)
                                      (_root_.GebMirror.Metalogic.«Base.range»
                                        (_root_.GebMirror.Metalogic.«Prelude.length» x26))))))))))
            (fun (x13 : _root_.List _root_.Geb.Kernel.Tree)
               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7 x14 x8 x13 x10 x11)
            x5
            x9
            ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x8

def «Tactics.subVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.subst»
      (_root_.GebMirror.Metalogic.«Derivation.weaken1» x1)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          x2
          (_root_.Geb.Kernel.Const.add
            x0
            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)
        else
          _root_.GebMirror.Metalogic.«Language.var» x2);
    x2

def «Tactics.revertCase» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree)
                                         (x11 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x8 x4)
        (fun (x12 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Language.listPart» x12)
            (fun (x13 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Base.bindO»
                (_root_.GebMirror.Metalogic.«Prelude.nth» x9 x5)
                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                  let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                    x10
                    x11;
                  let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.ttL» x2;
                  let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
                    x4
                    x12
                    (_root_.GebMirror.Metalogic.«Tactics.impL» x2 x14 x15);
                  let x18 : _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree := (fun (x18 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Tactics.subVar» x4 x18);
                  let x19 : _root_.Geb.Kernel.Tree := x18 x14;
                  let x20 : _root_.Geb.Kernel.Tree := x18 x15;
                  _root_.GebMirror.Metalogic.«Prover.bindHT»
                    (_root_.GebMirror.Metalogic.«Derivation.lowerHyps»
                      x0
                      x1
                      x8
                      (_root_.GebMirror.Metalogic.«Prelude.append»
                        (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x9)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x16)))
                    (fun (x21 : _root_.Geb.Kernel.Tree) =>
                      let x22 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x21;
                      let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.instAt»
                        (_root_.Geb.Kernel.leaf 0)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x13)
                        x19;
                      let x24 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.instAt»
                        (_root_.Geb.Kernel.leaf 0)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x13)
                        x20;
                      _root_.GebMirror.Metalogic.«Derivation.bindPT»
                        (_root_.GebMirror.Metalogic.«Derivation.eqParts» x24)
                        (fun (x25 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Base.bindO»
                            (x6
                              x8
                              (_root_.GebMirror.Metalogic.«Prelude.append»
                                x22
                                (_root_.GebMirror.Metalogic.«Prelude.single» x23))
                              (_root_.GebMirror.Metalogic.«Language.p1» x25)
                              (_root_.GebMirror.Metalogic.«Language.p2» x25))
                            (fun (x26 : _root_.Geb.Kernel.Tree) =>
                              let x27 : _root_.List
                                _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
                                (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken2» x22)
                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                  (_root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                    (_root_.GebMirror.Metalogic.«Tactics.impL» x2 x19 x20)));
                              let x28 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                (_root_.Geb.Kernel.leaf 1)
                                x13
                                x19;
                              let x29 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.listConsAt»
                                (_root_.Geb.Kernel.leaf 1)
                                x13
                                x20;
                              _root_.GebMirror.Metalogic.«Derivation.bindPT»
                                (_root_.GebMirror.Metalogic.«Derivation.eqParts» x29)
                                (fun (x30 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«Base.mapO»
                                    (fun (x31 : _root_.Geb.Kernel.Tree) =>
                                      let x32 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                        (_root_.Geb.Kernel.leaf 29)
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          (_root_.Geb.Kernel.leaf 0)
                                          (_root_.Geb.Kernel.leaf 1))
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          (_root_.GebMirror.Metalogic.«Tactics.impI»
                                            x3
                                            (_root_.GebMirror.Metalogic.«Prelude.length» x22)
                                            x23
                                            x24
                                            x26)
                                          (_root_.GebMirror.Metalogic.«Tactics.impI»
                                            x3
                                            (_root_.GebMirror.Metalogic.«Prelude.length» x27)
                                            x28
                                            x29
                                            x31));
                                      let x33 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
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
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 3)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 3)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 25)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  _root_.GebMirror.Metalogic.«Tactics.trueI»
                                                  x32)))));
                                      let x34 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                        (_root_.Geb.Kernel.leaf 22)
                                        (_root_.GebMirror.Metalogic.«Prelude.single»
                                          (_root_.GebMirror.Metalogic.«Language.mEq»
                                            x17
                                            (_root_.GebMirror.Metalogic.«Language.mLam» x12 x16)))
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          x33
                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                            (_root_.Geb.Kernel.leaf 24)
                                            (_root_.GebMirror.Metalogic.«Prelude.single»
                                              (_root_.GebMirror.Metalogic.«Language.app»
                                                x17
                                                (_root_.GebMirror.Metalogic.«Language.var» x4)))
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 3)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree))
                                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                (_root_.Geb.Kernel.leaf 23)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 1)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (_root_.GebMirror.Metalogic.«Theory.l2»
                                                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                        (_root_.Geb.Kernel.leaf 2)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                            (_root_.Geb.Kernel.leaf 17)
                                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                                              (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                              (_root_.Geb.Kernel.leaf 0))
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                            (_root_.Geb.Kernel.leaf 0)
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                        (_root_.Geb.Kernel.leaf 3)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                                  _root_.GebMirror.Metalogic.«Tactics.trueI»)))));
                                      _root_.GebMirror.Metalogic.«Prover.dNode»
                                        (_root_.Geb.Kernel.leaf 27)
                                        (_root_.GebMirror.Metalogic.«Theory.l3»
                                          (_root_.Geb.Kernel.Const.add
                                            x3
                                            (_root_.Geb.Kernel.leaf 4))
                                          (_root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree))
                                          (_root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Theory.l2» x15 x14)))
                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                          x34
                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                            (_root_.Geb.Kernel.leaf 21)
                                            (_root_.GebMirror.Metalogic.«Prelude.single» x5)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                    (x7
                                      (x12 :: (x13 :: x8))
                                      (_root_.GebMirror.Metalogic.«Prelude.append»
                                        x27
                                        (_root_.GebMirror.Metalogic.«Prelude.single» x28))
                                      (_root_.GebMirror.Metalogic.«Language.p1» x30)
                                      (_root_.GebMirror.Metalogic.«Language.p2» x30))))))))));
    x8

def «Tactics.betaRule» :=
  ((_root_.GebMirror.Metalogic.«Prover.nrRule»
    (_root_.Geb.Kernel.leaf 3)
    (_root_.GebMirror.Metalogic.«Derivation.terms»
      ([] : _root_.List _root_.Geb.Kernel.Tree))) ::
    ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Tactics.byImpI» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.bindNT»
        (_root_.GebMirror.Metalogic.«Prover.eval»
          x0
          x1
          (_root_.Geb.Kernel.leaf 0)
          _root_.GebMirror.Metalogic.«Tactics.betaRule»
          (_root_.Geb.Kernel.leaf 4096)
          (_root_.Geb.Kernel.leaf 0)
          x5
          x6
          x7)
        (fun (x9 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.bindNT»
            (_root_.GebMirror.Metalogic.«Prover.eval»
              x0
              x1
              (_root_.Geb.Kernel.leaf 0)
              _root_.GebMirror.Metalogic.«Tactics.betaRule»
              (_root_.Geb.Kernel.leaf 4096)
              (_root_.Geb.Kernel.leaf 0)
              x5
              x6
              x8)
            (fun (x10 : _root_.Geb.Kernel.Tree) =>
              let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm» x9;
              let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                x10;
              if (_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.GebMirror.Metalogic.«Language.mIs»
                  (_root_.Geb.Kernel.leaf 11)
                  (_root_.Geb.Kernel.leaf 2)
                  x11)
                (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x12)
                  (_root_.Geb.Kernel.leaf 11))).label ≠ 0 then
                if (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.Geb.Kernel.Const.eq
                    (_root_.GebMirror.Metalogic.«Language.mD» x11 (_root_.Geb.Kernel.leaf 0))
                    (_root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 2)))
                  (_root_.Geb.Kernel.Const.eq
                    (_root_.GebMirror.Metalogic.«Language.mD» x12 (_root_.Geb.Kernel.leaf 0))
                    x2)).label ≠ 0 then
                  let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                    x11
                    (_root_.Geb.Kernel.leaf 0);
                  let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                    x11
                    (_root_.Geb.Kernel.leaf 1);
                  _root_.GebMirror.Metalogic.«Derivation.bindPT»
                    (_root_.GebMirror.Metalogic.«Derivation.eqParts» x13)
                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.mapO»
                        (fun (x16 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 23)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 2)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                    (_root_.GebMirror.Metalogic.«Prover.nfMarked» x9))
                                  (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                    (_root_.GebMirror.Metalogic.«Prover.nfMarked» x10))))
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 25)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  _root_.GebMirror.Metalogic.«Tactics.trueI»
                                  (_root_.GebMirror.Metalogic.«Tactics.impI»
                                    x3
                                    (_root_.Geb.Kernel.Const.add
                                      (_root_.GebMirror.Metalogic.«Prelude.length» x6)
                                      (_root_.Geb.Kernel.leaf 1))
                                    x14
                                    x13
                                    x16)))))
                        (x4
                          x5
                          (_root_.GebMirror.Metalogic.«Prelude.append»
                            x6
                            (_root_.GebMirror.Metalogic.«Theory.l2» (_root_.GebMirror.Metalogic.«Tactics.ttL» x2) x14))
                          (_root_.GebMirror.Metalogic.«Language.p1» x15)
                          (_root_.GebMirror.Metalogic.«Language.p2» x15)))
                else
                  _root_.GebMirror.Metalogic.«Prelude.none»
              else
                _root_.GebMirror.Metalogic.«Prelude.none»)));
    x5

def «Tactics.withImpElim» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (fun (x9 : _root_.Geb.Kernel.Tree)
           (x10 : _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x11 : _root_.List _root_.Geb.Kernel.Tree)
           (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Derivation.bindPT»
            (_root_.GebMirror.Metalogic.«Language.bindTP»
              (_root_.GebMirror.Metalogic.«Prelude.nth» x11 x9)
              _root_.GebMirror.Metalogic.«Derivation.eqParts»)
            (fun (x13 : _root_.Geb.Kernel.Tree) =>
              let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x13;
              if (_root_.GebMirror.Metalogic.«Language.mIs»
                (_root_.Geb.Kernel.leaf 11)
                (_root_.Geb.Kernel.leaf 2)
                x14).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.GebMirror.Metalogic.«Language.mD» x14 (_root_.Geb.Kernel.leaf 0))
                  (_root_.Geb.Kernel.Const.add
                    x0
                    (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                  let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                    x14
                    (_root_.Geb.Kernel.leaf 0);
                  let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                    x14
                    (_root_.Geb.Kernel.leaf 1);
                  _root_.GebMirror.Metalogic.«Base.mapO»
                    (fun (x17 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 22)
                        (_root_.GebMirror.Metalogic.«Prelude.single» x15)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 27)
                            (_root_.GebMirror.Metalogic.«Theory.l3»
                              (_root_.Geb.Kernel.Const.add x1 (_root_.Geb.Kernel.leaf 4))
                              (_root_.Geb.Kernel.Const.node
                                (_root_.Geb.Kernel.leaf 0)
                                ([] : _root_.List _root_.Geb.Kernel.Tree))
                              (_root_.Geb.Kernel.Const.node
                                (_root_.Geb.Kernel.leaf 0)
                                (_root_.GebMirror.Metalogic.«Theory.l2» x15 x16)))
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 23)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                    (_root_.Geb.Kernel.leaf 17)
                                    (_root_.GebMirror.Metalogic.«Theory.l2» x9 (_root_.Geb.Kernel.leaf 0))
                                    ([] : _root_.List _root_.Geb.Kernel.Tree))
                                  _root_.GebMirror.Metalogic.«Tactics.trueI»))
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 21)
                                (_root_.GebMirror.Metalogic.«Prelude.single» x2)
                                ([] : _root_.List _root_.Geb.Kernel.Tree))))
                          x17))
                    (x10
                      (_root_.GebMirror.Metalogic.«Prelude.append»
                        x11
                        (_root_.GebMirror.Metalogic.«Prelude.single» x15))
                      (_root_.GebMirror.Metalogic.«Tactics.appendNR»
                        x12
                        ((_root_.GebMirror.Metalogic.«Tactics.hypRule»
                          (_root_.GebMirror.Metalogic.«Prelude.length» x11)) ::
                          ([] : _root_.List _root_.Geb.Kernel.Tree))))
                else
                  _root_.GebMirror.Metalogic.«Prelude.none»
              else
                _root_.GebMirror.Metalogic.«Prelude.none»))
        (fun (x9 : _root_.List _root_.Geb.Kernel.Tree)
           (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
          x4 x10 x5 x9 x7 x8)
        x3
        x6
        ([] : _root_.List _root_.Geb.Kernel.Tree));
    x5

def «Tactics.hypIndex» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
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
                                          _root_.GebMirror.Metalogic.«Prelude.some» x3
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Tactics.succPredRw» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 6)
      (_root_.Geb.Kernel.leaf 2)
      x2).label ≠ 0 then
      let x3 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0));
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
        (_root_.GebMirror.Metalogic.«Language.pr»
          (_root_.GebMirror.Metalogic.«Language.app»
            (_root_.GebMirror.Metalogic.«Language.mArg» x2 (_root_.Geb.Kernel.leaf 0))
            (_root_.GebMirror.Metalogic.«Derivation.instTerm»
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              x3
              x1))
          (_root_.GebMirror.Metalogic.«Prover.dNode»
            (_root_.Geb.Kernel.leaf 2)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2»
              (_root_.GebMirror.Metalogic.«Prover.dNode»
                (_root_.Geb.Kernel.leaf 0)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                ([] : _root_.List _root_.Geb.Kernel.Tree))
              (_root_.GebMirror.Metalogic.«Prover.dNode»
                (_root_.Geb.Kernel.leaf 16)
                (_root_.GebMirror.Metalogic.«Theory.l4»
                  x0
                  (_root_.Geb.Kernel.Const.node
                    (_root_.Geb.Kernel.leaf 0)
                    ([] : _root_.List _root_.Geb.Kernel.Tree))
                  (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x3)
                  (_root_.Geb.Kernel.leaf 1))
                ([] : _root_.List _root_.Geb.Kernel.Tree)))))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»);
    x3

def «Tactics.bySuccPred» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Tactics.bindTh»
        (_root_.GebMirror.Metalogic.«Derivation.thmAt» x0 x1)
        (fun (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Derivation.bindPT»
            (_root_.GebMirror.Metalogic.«Derivation.eqParts»
              (_root_.GebMirror.Metalogic.«Derivation.thConcl» x7))
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Derivation.bindPT»
                (_root_.GebMirror.Metalogic.«Tactics.succPredRw»
                  x1
                  (_root_.GebMirror.Metalogic.«Language.p1» x8)
                  x5)
                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Derivation.bindPT»
                    (_root_.GebMirror.Metalogic.«Tactics.succPredRw»
                      x1
                      (_root_.GebMirror.Metalogic.«Language.p1» x8)
                      x6)
                    (fun (x10 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.mapO»
                        (fun (x11 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 23)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 2)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  (_root_.GebMirror.Metalogic.«Language.p2» x9)
                                  (_root_.GebMirror.Metalogic.«Language.p2» x10)))
                              x11))
                        (x2
                          x3
                          x4
                          (_root_.GebMirror.Metalogic.«Language.p1» x9)
                          (_root_.GebMirror.Metalogic.«Language.p1» x10)))))));
    x3

def «Tactics.tailTss» :=
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

def «Tactics.concatTss» :=
  fun (x0 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.append» x1 x2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x0;
    x1

def «Tactics.subtermsStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                   x0;
                                 (x0 ::
                                   (if (_root_.Geb.Kernel.Const.eq
                                     x2
                                     (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   else
                                     if (_root_.GebMirror.Metalogic.«Prelude.or»
                                       (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 8))
                                       (_root_.Geb.Kernel.Const.eq
                                         x2
                                         (_root_.Geb.Kernel.leaf 9))).label ≠ 0 then
                                       _root_.GebMirror.Metalogic.«Tactics.concatTss»
                                         (_root_.Geb.Kernel.Const.iter
                                           (α := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                           _root_.GebMirror.Metalogic.«Tactics.tailTss»
                                           x1
                                           (_root_.Geb.Kernel.leaf 3))
                                     else
                                       if (_root_.Geb.Kernel.Const.eq
                                         x2
                                         (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                         _root_.GebMirror.Metalogic.«Tactics.concatTss»
                                           (_root_.Geb.Kernel.Const.iter
                                             (α := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                             _root_.GebMirror.Metalogic.«Tactics.tailTss»
                                             x1
                                             (_root_.Geb.Kernel.leaf 2))
                                       else
                                         _root_.GebMirror.Metalogic.«Tactics.concatTss»
                                           (_root_.GebMirror.Metalogic.«Tactics.tailTss» x1))));
    x2

def «Tactics.openSubterms» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Tactics.subtermsStep»
      x0;
    x1

def «Tactics.findSomeT» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x0 x2;
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x4).label ≠ 0 then x4 else x3)
      _root_.GebMirror.Metalogic.«Prelude.none»
      x1;
    x2

def «Tactics.varUnless» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x1)
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
        x1
        (_root_.Geb.Kernel.leaf 0);
      if (x0 x2).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.none»
      else
        _root_.GebMirror.Metalogic.«Prelude.some» x2
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.scrutVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 6)
      (_root_.Geb.Kernel.leaf 2)
      x1).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
        x1
        (_root_.Geb.Kernel.leaf 0);
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 7))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.leaf 5))).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Tactics.varUnless»
          x0
          (_root_.GebMirror.Metalogic.«Language.mArg» x1 (_root_.Geb.Kernel.leaf 1))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.datumVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 8)
        (_root_.Geb.Kernel.leaf 3)
        x1)
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 9)
        (_root_.Geb.Kernel.leaf 3)
        x1)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Tactics.varUnless»
        x0
        (_root_.GebMirror.Metalogic.«Language.mArg» x1 (_root_.Geb.Kernel.leaf 2))
    else
      if (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 10)
        (_root_.Geb.Kernel.leaf 2)
        x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Tactics.varUnless»
          x0
          (_root_.GebMirror.Metalogic.«Language.mArg» x1 (_root_.Geb.Kernel.leaf 1))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.stuckVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.openSubterms»
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.findSomeT»
                                          (_root_.GebMirror.Metalogic.«Tactics.scrutVar» x0)
                                          x2;
                                        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x3).label ≠ 0 then
                                          x3
                                        else
                                          _root_.GebMirror.Metalogic.«Tactics.findSomeT»
                                            (_root_.GebMirror.Metalogic.«Tactics.datumVar» x0)
                                            x2);
    x2

def «Tactics.mentions» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lt
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prover.uses» x0 x1);
    x2

def «Tactics.eraseDupsTss» :=
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
        if (_root_.Geb.Kernel.Const.foldr
          (α := _root_.List _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
             (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prelude.or» (_root_.GebMirror.Metalogic.«Base.equalTs» x4 x1) x5)
          (_root_.Geb.Kernel.leaf 0)
          x3).label ≠ 0 then
          x2 x3
        else
          x2 (x1 :: x3))
      (fun (x1 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
        _root_.Geb.Kernel.Const.foldr
          (α := _root_.List _root_.Geb.Kernel.Tree)
          (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
            _root_.List (_root_.List _root_.Geb.Kernel.Tree))
          (fun (x2 : _root_.List _root_.Geb.Kernel.Tree)
             (x3 : _root_.List (_root_.List _root_.Geb.Kernel.Tree) →
               _root_.List (_root_.List _root_.Geb.Kernel.Tree))
             (x4 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
            x3 (x2 :: x4))
          (fun (x2 : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) => x2)
          x1
          ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree)))
      x0
      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree));
    x1

def «Tactics.matchesWith» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := (let x3 : _root_.List
                                      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
                                      (fun (x3 : _root_.Geb.Kernel.Tree) =>
                                        if (_root_.Geb.Kernel.Const.lt x3 x1).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prelude.none»
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.some»
                                            (_root_.GebMirror.Metalogic.«Language.var»
                                              (_root_.Geb.Kernel.Const.sub x3 x1)))
                                      (_root_.GebMirror.Metalogic.«Base.range»
                                        (_root_.Geb.Kernel.Const.add
                                          x1
                                          (_root_.Geb.Kernel.leaf 64)));
                                    _root_.GebMirror.Metalogic.«Tactics.eraseDupsTss»
                                      (_root_.Geb.Kernel.Const.foldr
                                        (α := _root_.Geb.Kernel.Tree)
                                        (β := _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                        (fun (x4 : _root_.Geb.Kernel.Tree)
                                           (x5 : _root_.List
                                             (_root_.List _root_.Geb.Kernel.Tree)) =>
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.bindAT»
                                            (x0 (_root_.Geb.Kernel.leaf 0) x4 x3)
                                            (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Base.allSomeT»
                                                (_root_.GebMirror.Metalogic.«Base.take»
                                                  x1
                                                  (_root_.GebMirror.Metalogic.«Prover.assigned» x6)));
                                          if (_root_.GebMirror.Metalogic.«Prelude.isSome» x6).label ≠ 0 then
                                            ((_root_.GebMirror.Metalogic.«Prelude.reverse»
                                              (_root_.Geb.Kernel.Const.children
                                                (_root_.GebMirror.Metalogic.«Prelude.get» x6))) ::
                                              x5)
                                          else
                                            x5)
                                        ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                        (_root_.GebMirror.Metalogic.«Tactics.openSubterms» x2)));
    x3

def «Tactics.matchesOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := _root_.GebMirror.Metalogic.«Tactics.matchesWith»
      (_root_.GebMirror.Metalogic.«Prover.matchTerm» x0)
      x1
      x2;
    x3

def «Tactics.appendTss» :=
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

def «$284f7074696f6e2e69734a7573742050726f7665722e4e465229» :=
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

def «$284f7074696f6e2e66726f6d4d617962652050726f7665722e4e465229» :=
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

def «Tactics.instArgs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.List
      (_root_.List
        _root_.Geb.Kernel.Tree) := (let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.bindTP»
                                      (_root_.GebMirror.Metalogic.«Prelude.nth» x6 x9)
                                      _root_.GebMirror.Metalogic.«Derivation.eqParts»;
                                    if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e545061697229»
                                      x10).label ≠ 0 then
                                      let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1»
                                        (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265204c616e67756167652e545061697229»
                                          _root_.GebMirror.Metalogic.«Tactics.pr0»
                                          x10);
                                      if (_root_.GebMirror.Metalogic.«Language.mIs»
                                        (_root_.Geb.Kernel.leaf 5)
                                        (_root_.Geb.Kernel.leaf 1)
                                        x11).label ≠ 0 then
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.eval»
                                          x1
                                          x2
                                          x3
                                          x4
                                          (_root_.Geb.Kernel.leaf 4096)
                                          x0
                                          ((_root_.GebMirror.Metalogic.«Language.mD»
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)) ::
                                            x5)
                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                            _root_.GebMirror.Metalogic.«Derivation.weaken1»
                                            x6)
                                          (_root_.GebMirror.Metalogic.«Language.mArg»
                                            x11
                                            (_root_.Geb.Kernel.leaf 0));
                                        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a7573742050726f7665722e4e465229»
                                          x12).label ≠ 0 then
                                          let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                                            (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d617962652050726f7665722e4e465229»
                                              _root_.GebMirror.Metalogic.«Tactics.nfr0»
                                              x12);
                                          _root_.GebMirror.Metalogic.«Tactics.eraseDupsTss»
                                            (_root_.GebMirror.Metalogic.«Tactics.appendTss»
                                              (_root_.GebMirror.Metalogic.«Tactics.matchesOf»
                                                x13
                                                (_root_.Geb.Kernel.leaf 1)
                                                x7)
                                              (_root_.GebMirror.Metalogic.«Tactics.matchesOf»
                                                x13
                                                (_root_.Geb.Kernel.leaf 1)
                                                x8))
                                        else
                                          ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                      else
                                        ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                                    else
                                      ([] : _root_.List (_root_.List _root_.Geb.Kernel.Tree)));
    x10

def «Tactics.byInstsOnce» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.bindNT»
        (_root_.GebMirror.Metalogic.«Prover.eval»
          x1
          x2
          x3
          x4
          (_root_.Geb.Kernel.leaf 4096)
          x0
          x7
          x8
          x9)
        (fun (x11 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.bindNT»
            (_root_.GebMirror.Metalogic.«Prover.eval»
              x1
              x2
              x3
              x4
              (_root_.Geb.Kernel.leaf 4096)
              x0
              x7
              x8
              x10)
            (fun (x12 : _root_.Geb.Kernel.Tree) =>
              let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                x11;
              let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                x12;
              if (_root_.Geb.Kernel.Const.equal x13 x14).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Tactics.byMode» x0 x1 x2 x3 x4 x7 x8 x9 x10
              else
                let x15 : _root_.List
                  (_root_.Geb.Kernel.Tree ×
                    _root_.List
                      (_root_.List
                        _root_.Geb.Kernel.Tree)) := _root_.Geb.Kernel.Const.foldr
                  (α := _root_.Geb.Kernel.Tree)
                  (β := _root_.List
                    (_root_.Geb.Kernel.Tree ×
                      _root_.List (_root_.List _root_.Geb.Kernel.Tree)))
                  (fun (x15 : _root_.Geb.Kernel.Tree)
                     (x16 : _root_.List
                       (_root_.Geb.Kernel.Tree ×
                         _root_.List (_root_.List _root_.Geb.Kernel.Tree))) =>
                    let x17 : _root_.List
                      (_root_.List
                        _root_.Geb.Kernel.Tree) := _root_.GebMirror.Metalogic.«Tactics.instArgs»
                      x0
                      x1
                      x2
                      x3
                      x4
                      x7
                      x8
                      x13
                      x14
                      x15;
                    _root_.Geb.Kernel.Const.lcase
                      (α := _root_.List _root_.Geb.Kernel.Tree)
                      (β := _root_.List
                        (_root_.Geb.Kernel.Tree ×
                          _root_.List (_root_.List _root_.Geb.Kernel.Tree)))
                      x17
                      x16
                      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
                         (_ : _root_.List (_root_.List _root_.Geb.Kernel.Tree)) =>
                        ((x15, x17) :: x16)))
                  ([] : _root_.List (_root_.Geb.Kernel.Tree ×
                    _root_.List (_root_.List _root_.Geb.Kernel.Tree)))
                  (_root_.GebMirror.Metalogic.«Base.range»
                    (if (_root_.Geb.Kernel.Const.lt
                      x5
                      (_root_.GebMirror.Metalogic.«Prelude.length» x8)).label ≠ 0 then
                      x5
                    else
                      _root_.GebMirror.Metalogic.«Prelude.length» x8));
                _root_.Geb.Kernel.Const.lcase
                  (α := _root_.Geb.Kernel.Tree ×
                    _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                  (β := _root_.Geb.Kernel.Tree)
                  x15
                  _root_.GebMirror.Metalogic.«Prelude.none»
                  (fun (_ : _root_.Geb.Kernel.Tree ×
                       _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                     (_ : _root_.List
                       (_root_.Geb.Kernel.Tree ×
                         _root_.List (_root_.List _root_.Geb.Kernel.Tree))) =>
                    _root_.Geb.Kernel.Const.foldr
                      (α := _root_.Geb.Kernel.Tree ×
                        _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                      (β := _root_.List _root_.Geb.Kernel.Tree →
                        _root_.List _root_.Geb.Kernel.Tree →
                          _root_.List _root_.Geb.Kernel.Tree →
                            _root_.Geb.Kernel.Tree →
                              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                      (fun (x18 : _root_.Geb.Kernel.Tree ×
                           _root_.List (_root_.List _root_.Geb.Kernel.Tree))
                         (x19 : _root_.List _root_.Geb.Kernel.Tree →
                           _root_.List _root_.Geb.Kernel.Tree →
                             _root_.List _root_.Geb.Kernel.Tree →
                               _root_.Geb.Kernel.Tree →
                                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                         (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Tactics.withInsts»
                          x1
                          x2
                          x3
                          x4
                          (x18).1
                          (x18).2
                          (fun (x21 : _root_.List _root_.Geb.Kernel.Tree) =>
                            x19 (_root_.GebMirror.Metalogic.«Tactics.appendNR» x20 x21))
                          x0)
                      x6
                      x15
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      x7
                      x8
                      x9
                      x10))));
    x7

def «Tactics.instsLast» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Tactics.byMode»
        x0
        x1
        x2
        x3
        (_root_.GebMirror.Metalogic.«Tactics.appendNR» x5 x4));
    x5

def «Tactics.instsRound» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x10 : _root_.Geb.Kernel.Tree)
                                           (x11 : _root_.Geb.Kernel.Tree) =>
      let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.byMode»
        x0
        x1
        x2
        x3
        (_root_.GebMirror.Metalogic.«Tactics.appendNR» x7 x4)
        x8
        x9
        x10
        x11;
      if (_root_.GebMirror.Metalogic.«Prelude.isSome» x12).label ≠ 0 then
        x12
      else
        _root_.GebMirror.Metalogic.«Tactics.byInstsOnce»
          x0
          x1
          x2
          x3
          (_root_.GebMirror.Metalogic.«Tactics.appendNR» x7 x4)
          x5
          (fun (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
            x6 (_root_.GebMirror.Metalogic.«Tactics.appendNR» x7 x13))
          x8
          x9
          x10
          x11);
    x7

def «Tactics.byInsts» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.instsRound»
      x0
      x1
      x2
      x3
      x4
      x5
      (_root_.GebMirror.Metalogic.«Tactics.instsRound»
        x0
        x1
        x2
        x3
        x4
        x5
        (_root_.GebMirror.Metalogic.«Tactics.instsRound»
          x0
          x1
          x2
          x3
          x4
          x5
          (_root_.GebMirror.Metalogic.«Tactics.instsLast» x0 x1 x2 x3 x4)))
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x6

def «Tactics.orO» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      x0
    else
      x1);
    x2

def «Tactics.byAuto» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree) =>
      let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
        x7;
      _root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (fun (x11 : _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x12 : _root_.List _root_.Geb.Kernel.Tree)
           (x13 : _root_.List _root_.Geb.Kernel.Tree)
           (x14 : _root_.Geb.Kernel.Tree)
           (x15 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Tactics.orO»
            (_root_.GebMirror.Metalogic.«Tactics.byInsts» x5 x0 x1 x2 x3 x10 x12 x13 x14 x15)
            (_root_.GebMirror.Metalogic.«Prover.bindNT»
              (_root_.GebMirror.Metalogic.«Prover.eval»
                x0
                x1
                x2
                x3
                (_root_.Geb.Kernel.leaf 4096)
                x5
                x12
                x13
                x14)
              (fun (x16 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Prover.bindNT»
                  (_root_.GebMirror.Metalogic.«Prover.eval»
                    x0
                    x1
                    x2
                    x3
                    (_root_.Geb.Kernel.leaf 4096)
                    x5
                    x12
                    x13
                    x15)
                  (fun (x17 : _root_.Geb.Kernel.Tree) =>
                    let x18 : _root_.Geb.Kernel.Tree →
                      _root_.Geb.Kernel.Tree := (fun (x18 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.anyT»
                        (fun (x19 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Tactics.mentions» x19 x18)
                        (_root_.GebMirror.Metalogic.«Base.take» x10 x13));
                    let x19 : _root_.Geb.Kernel.Tree →
                      _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) =>
                      _root_.Geb.Kernel.leaf 0);
                    _root_.GebMirror.Metalogic.«Base.bindO»
                      (_root_.GebMirror.Metalogic.«Tactics.orO»
                        (_root_.GebMirror.Metalogic.«Tactics.orO»
                          (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                            x18
                            (_root_.GebMirror.Metalogic.«Prover.nfTerm» x16))
                          (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                            x18
                            (_root_.GebMirror.Metalogic.«Prover.nfTerm» x17)))
                        (_root_.GebMirror.Metalogic.«Tactics.orO»
                          (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                            x19
                            (_root_.GebMirror.Metalogic.«Prover.nfTerm» x16))
                          (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                            x19
                            (_root_.GebMirror.Metalogic.«Prover.nfTerm» x17))))
                      (fun (x20 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Base.bindO»
                          (_root_.GebMirror.Metalogic.«Prelude.nth» x12 x20)
                          (fun (x21 : _root_.Geb.Kernel.Tree) =>
                            if (_root_.GebMirror.Metalogic.«Prelude.isSome»
                              (_root_.GebMirror.Metalogic.«Language.listPart» x21)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«Tactics.byListSplit» x0 x2 x20 x11 x11 x12 x13 x14 x15
                            else
                              if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e545061697229»
                                (_root_.GebMirror.Metalogic.«Language.coprodParts» x21)).label ≠ 0 then
                                _root_.GebMirror.Metalogic.«Tactics.bySplit2»
                                  (_root_.Geb.Kernel.leaf 3)
                                  (_root_.Geb.Kernel.leaf 4)
                                  x20
                                  x11
                                  x11
                                  x12
                                  x13
                                  x14
                                  x15
                              else
                                _root_.GebMirror.Metalogic.«Prelude.none»))))))
        (_root_.GebMirror.Metalogic.«Tactics.byInsts» x5 x0 x1 x2 x3 x10)
        x4
        x6
        x7
        x8
        x9);
    x6

def «Tactics.condOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 :: (x2 :: (x3 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))

def «$284f7074696f6e2e6e6f7468696e6720546163746963732e436f6e6429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420546163746963732e436f6e6429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Tactics.bindCT» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Tactics.condParts» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 11)
        (_root_.Geb.Kernel.leaf 3)
        x0)
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.leaf 6))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.Geb.Kernel.Const.children
              (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 1))))
          (_root_.Geb.Kernel.leaf 1)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420546163746963732e436f6e6429»
        (_root_.GebMirror.Metalogic.«Tactics.condOf»
          (_root_.GebMirror.Metalogic.«Prelude.at»
            (_root_.Geb.Kernel.Const.children
              (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 1)))
            (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 0)))
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e436f6e6429»);
    x1

def «Tactics.condVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.bindCT»
      (_root_.GebMirror.Metalogic.«Tactics.condParts» x1)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.varUnless»
          x0
          (_root_.GebMirror.Metalogic.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x2)
            (_root_.Geb.Kernel.leaf 1)));
    x2

def «Tactics.stuckVarC» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.orO»
      (_root_.GebMirror.Metalogic.«Tactics.findSomeT»
        (_root_.GebMirror.Metalogic.«Tactics.condVar» x0)
        (_root_.GebMirror.Metalogic.«Tactics.openSubterms» x1))
      (_root_.GebMirror.Metalogic.«Tactics.stuckVar» x0 x1);
    x2

def «Tactics.isApps2» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 6)
        (_root_.Geb.Kernel.leaf 2)
        x1)
      (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
         x1
         (_root_.Geb.Kernel.leaf 0);
       _root_.GebMirror.Metalogic.«Prelude.and»
         (_root_.GebMirror.Metalogic.«Language.mIs»
           (_root_.Geb.Kernel.leaf 6)
           (_root_.Geb.Kernel.leaf 2)
           x2)
         (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
            x2
            (_root_.Geb.Kernel.leaf 0);
          _root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x3)
              (_root_.Geb.Kernel.leaf 11))
            (_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.Geb.Kernel.Const.eq
                (_root_.GebMirror.Metalogic.«Language.mD» x3 (_root_.Geb.Kernel.leaf 0))
                x0)
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.mD» x3 (_root_.Geb.Kernel.leaf 1))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))))));
    x2

def «Tactics.appsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Tactics.isApps2» x0 x2).label ≠ 0 then
          (x2 :: x3)
        else
          x3)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Tactics.openSubterms» x1);
    x2

def «Tactics.ldefn0» :=
  _root_.GebMirror.Metalogic.«Language.ldefn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Language.objs»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Tactics.unnodeTy» :=
  _root_.GebMirror.Metalogic.«Theory.prod»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)

def «$284f7074696f6e2e6e74684f66204c616e67756167652e4c4465666e29» :=
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
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e4c4465666e29»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e4c4465666e29»
          x2);
    x2

def «$284f7074696f6e2e69734a757374204c616e67756167652e4c4465666e29» :=
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

def «$284f7074696f6e2e66726f6d4d61796265204c616e67756167652e4c4465666e29» :=
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

def «Tactics.unnodeStep» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66204c616e67756167652e4c4465666e29»
    _root_.GebMirror.Metalogic.«Translation.lib»
    (_root_.Geb.Kernel.leaf 4);
  if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e4c4465666e29»
    x0).label ≠ 0 then
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Language.mArgs»
        (_root_.GebMirror.Metalogic.«Language.ldBody»
          (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265204c616e67756167652e4c4465666e29»
            _root_.GebMirror.Metalogic.«Tactics.ldefn0»
            x0)))
      _root_.GebMirror.Metalogic.«Language.mStar»
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x1)
  else
    _root_.GebMirror.Metalogic.«Language.mStar»

def «Tactics.unnodeU» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mRoseRec»
      _root_.GebMirror.Metalogic.«Tactics.unnodeTy»
      _root_.GebMirror.Metalogic.«Tactics.unnodeStep»
      x0;
    x1

def «Tactics.anyBound» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          _root_.Geb.Kernel.leaf 1
        else
          _root_.Geb.Kernel.leaf 0
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            _root_.Geb.Kernel.leaf 2
          else
            _root_.Geb.Kernel.leaf 0
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.Geb.Kernel.leaf 1
            else
              _root_.Geb.Kernel.leaf 0
          else
            _root_.Geb.Kernel.leaf 0);
    x2

def «Tactics.kidsAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree) =>
        ((x2
          (_root_.Geb.Kernel.Const.add
            x4
            (_root_.GebMirror.Metalogic.«Tactics.anyBound» x0 x5))) ::
          (x3 x4 (_root_.Geb.Kernel.Const.add x5 (_root_.Geb.Kernel.leaf 1)))))
      (fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«$284c697374732e7461696c20284172726f77205420542929»
        x1);
    x2

def «Tactics.occStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                   x2;
                                 let x5 : _root_.Geb.Kernel.Tree →
                                   _root_.Geb.Kernel.Tree →
                                     _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.kidsAt»
                                   x4
                                   x3;
                                 fun (x6 : _root_.Geb.Kernel.Tree) =>
                                   let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                     (_root_.Geb.Kernel.leaf 0)
                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                     ([] : _root_.List _root_.Geb.Kernel.Tree);
                                   let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                                     x1
                                     x6;
                                   if (_root_.Geb.Kernel.Const.eq
                                     x4
                                     (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
                                       x8).label ≠ 0 then
                                       _root_.GebMirror.Metalogic.«Prover.dNode»
                                         (_root_.Geb.Kernel.leaf 1)
                                         ([] : _root_.List _root_.Geb.Kernel.Tree)
                                         (_root_.GebMirror.Metalogic.«Theory.l2»
                                           (_root_.GebMirror.Metalogic.«Prover.dNode»
                                             (_root_.Geb.Kernel.leaf 2)
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (_root_.GebMirror.Metalogic.«Prelude.single»
                                               (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                 (_root_.Geb.Kernel.leaf 6)
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree))))
                                           (_root_.GebMirror.Metalogic.«Prover.dNode»
                                             (_root_.Geb.Kernel.leaf 16)
                                             (_root_.GebMirror.Metalogic.«Theory.l4»
                                               x0
                                               (_root_.Geb.Kernel.Const.node
                                                 (_root_.Geb.Kernel.leaf 0)
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree))
                                               (_root_.Geb.Kernel.Const.node
                                                 (_root_.Geb.Kernel.leaf 0)
                                                 (_root_.GebMirror.Metalogic.«Prelude.single»
                                                   (_root_.GebMirror.Metalogic.«Language.var» x8)))
                                               (_root_.Geb.Kernel.leaf 0))
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                     else
                                       x7
                                   else
                                     if (_root_.GebMirror.Metalogic.«Prelude.or»
                                       (_root_.Geb.Kernel.Const.eq x4 (_root_.Geb.Kernel.leaf 5))
                                       (_root_.GebMirror.Metalogic.«Prelude.or»
                                         (_root_.Geb.Kernel.Const.eq x4 (_root_.Geb.Kernel.leaf 8))
                                         (_root_.GebMirror.Metalogic.«Prelude.or»
                                           (_root_.Geb.Kernel.Const.eq
                                             x4
                                             (_root_.Geb.Kernel.leaf 9))
                                           (_root_.Geb.Kernel.Const.eq
                                             x4
                                             (_root_.Geb.Kernel.leaf 10))))).label ≠ 0 then
                                       _root_.GebMirror.Metalogic.«Prover.dNode»
                                         (_root_.Geb.Kernel.leaf 2)
                                         ([] : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 x6 (_root_.Geb.Kernel.leaf 0))
                                     else
                                       if (_root_.GebMirror.Metalogic.«Base.allT»
                                         (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                           _root_.Geb.Kernel.Const.eq
                                             (_root_.GebMirror.Metalogic.«Prover.uses» x9 x8)
                                             (_root_.Geb.Kernel.leaf 0))
                                         (_root_.GebMirror.Metalogic.«Language.mArgs» x2)).label ≠ 0 then
                                         x7
                                       else
                                         _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 2)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (x5 x6 (_root_.Geb.Kernel.leaf 0)));
    x4

def «Tactics.occRewrite» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Tactics.occStep» x0 x1)
      x2
      x3;
    x4

def «Tactics.byTreeSplit» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x3 x1)
        (fun (x7 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal
            x7
            _root_.GebMirror.Metalogic.«Translation.treeTy»).label ≠ 0 then
            let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
              x1
              x7
              x5;
            let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
              x1
              x7
              x6;
            let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.nodeT»
              (_root_.GebMirror.Metalogic.«Language.mPair»
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1))
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)));
            let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.app»
              (_root_.GebMirror.Metalogic.«Derivation.weaken2» x8)
              x10;
            let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.app»
              (_root_.GebMirror.Metalogic.«Derivation.weaken2» x9)
              x10;
            _root_.GebMirror.Metalogic.«Base.mapO»
              (fun (x13 : _root_.Geb.Kernel.Tree) =>
                let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
                  _root_.GebMirror.Metalogic.«Translation.bitsTy»
                  (_root_.GebMirror.Metalogic.«Language.mLam»
                    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                    x11);
                let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
                  _root_.GebMirror.Metalogic.«Translation.bitsTy»
                  (_root_.GebMirror.Metalogic.«Language.mLam»
                    (_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy»)
                    x12);
                let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 3)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree);
                let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  ([] : _root_.List _root_.Geb.Kernel.Tree);
                let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 2)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Theory.l2» x16 x16);
                let x19 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 26)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 23)
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.Metalogic.«Theory.l2»
                        x18
                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 26)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 23)
                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                              (_root_.GebMirror.Metalogic.«Theory.l2» x18 x13)))))));
                let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.unnodeU»
                  (_root_.GebMirror.Metalogic.«Language.var» x1);
                let x21 : _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree := (fun (x21 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Language.app»
                    (_root_.GebMirror.Metalogic.«Language.app»
                      x21
                      (_root_.GebMirror.Metalogic.«Language.mFst» x20))
                    (_root_.GebMirror.Metalogic.«Language.mSnd» x20));
                let x22 : _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree := (fun (x22 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Prover.dNode»
                    (_root_.Geb.Kernel.leaf 1)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    (_root_.GebMirror.Metalogic.«Theory.l2»
                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 2)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2» x16 x17))
                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 1)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          x16
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 1)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              x16
                              (_root_.GebMirror.Metalogic.«Tactics.occRewrite»
                                x0
                                x1
                                x22
                                (_root_.Geb.Kernel.leaf 0))))))));
                let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 18)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 2)
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.Metalogic.«Theory.l2»
                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 2)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Theory.l2»
                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 17)
                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                (_root_.GebMirror.Metalogic.«Prelude.length» x4)
                                (_root_.Geb.Kernel.leaf 0))
                              ([] : _root_.List _root_.Geb.Kernel.Tree))
                            x17))
                        x17))
                    x17);
                _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 22)
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.GebMirror.Metalogic.«Language.mEq» x14 x15))
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    x19
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 24)
                      (_root_.GebMirror.Metalogic.«Prelude.single»
                        (_root_.GebMirror.Metalogic.«Language.mEq» (x21 x14) (x21 x15)))
                      (_root_.GebMirror.Metalogic.«Theory.l2»
                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 2)
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (_root_.GebMirror.Metalogic.«Theory.l2» (x22 x5) (x22 x6)))
                        x23))))
              (x2
                ((_root_.GebMirror.Metalogic.«Theory.list» _root_.GebMirror.Metalogic.«Translation.treeTy») ::
                  (_root_.GebMirror.Metalogic.«Translation.bitsTy» :: x3))
                (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken2» x4)
                x11
                x12)
          else
            _root_.GebMirror.Metalogic.«Prelude.none»));
    x3

def «Tactics.splitStuck» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.bindO»
      (_root_.GebMirror.Metalogic.«Prelude.nth» x6 x3)
      (fun (x10 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.isSome»
          (_root_.GebMirror.Metalogic.«Language.listPart» x10)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Tactics.byListSplit» x0 x1 x3 x4 x5 x6 x7 x8 x9
        else
          if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Language.coprodParts» x10)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Tactics.bySplit2»
              (_root_.Geb.Kernel.leaf 3)
              (_root_.Geb.Kernel.leaf 4)
              x3
              x4
              x5
              x6
              x7
              x8
              x9
          else
            if (_root_.Geb.Kernel.Const.equal
              x10
              _root_.GebMirror.Metalogic.«Translation.treeTy»).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Tactics.byTreeSplit» x2 x3 x4 x6 x7 x8 x9
            else
              _root_.GebMirror.Metalogic.«Prelude.none»);
    x10

def «Tactics.byAutoT» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree)
                                         (x10 : _root_.Geb.Kernel.Tree) =>
      let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
        x8;
      let x12 : _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x12 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x13 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x14 : _root_.Geb.Kernel.Tree)
                                           (x15 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.bindNT»
          (_root_.GebMirror.Metalogic.«Prover.eval»
            x0
            x1
            x2
            x4
            (_root_.Geb.Kernel.leaf 4096)
            x6
            x12
            x13
            x14)
          (fun (x16 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prover.bindNT»
              (_root_.GebMirror.Metalogic.«Prover.eval»
                x0
                x1
                x2
                x4
                (_root_.Geb.Kernel.leaf 4096)
                x6
                x12
                x13
                x15)
              (fun (x17 : _root_.Geb.Kernel.Tree) =>
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Prover.nfTerm» x16)
                  (_root_.GebMirror.Metalogic.«Prover.nfTerm» x17)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Prelude.some»
                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                      (_root_.Geb.Kernel.leaf 18)
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.Metalogic.«Theory.l2»
                        (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                          (_root_.GebMirror.Metalogic.«Prover.nfMarked» x16))
                        (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                          (_root_.GebMirror.Metalogic.«Prover.nfMarked» x17))))
                else
                  _root_.GebMirror.Metalogic.«Prelude.none»)));
      let x13 : _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x13 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x14 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x15 : _root_.Geb.Kernel.Tree)
                                           (x16 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq
          x11
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.none»
        else
          _root_.GebMirror.Metalogic.«Tactics.byInsts» x6 x0 x1 x2 x4 x11 x13 x14 x15 x16);
      _root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (fun (x14 : _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x15 : _root_.List _root_.Geb.Kernel.Tree)
           (x16 : _root_.List _root_.Geb.Kernel.Tree)
           (x17 : _root_.Geb.Kernel.Tree)
           (x18 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.bindNT»
            (_root_.GebMirror.Metalogic.«Prover.eval»
              x0
              x1
              x2
              x4
              (_root_.Geb.Kernel.leaf 4096)
              x6
              x15
              x16
              x17)
            (fun (x19 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.bindNT»
                (_root_.GebMirror.Metalogic.«Prover.eval»
                  x0
                  x1
                  x2
                  x4
                  (_root_.Geb.Kernel.leaf 4096)
                  x6
                  x15
                  x16
                  x18)
                (fun (x20 : _root_.Geb.Kernel.Tree) =>
                  if (_root_.Geb.Kernel.Const.equal
                    (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19)
                    (_root_.GebMirror.Metalogic.«Prover.nfTerm» x20)).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«Prelude.some»
                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 18)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                            (_root_.GebMirror.Metalogic.«Prover.nfMarked» x19))
                          (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                            (_root_.GebMirror.Metalogic.«Prover.nfMarked» x20))))
                  else
                    _root_.GebMirror.Metalogic.«Tactics.orO»
                      (x13 x15 x16 x17 x18)
                      (let x21 : _root_.Geb.Kernel.Tree →
                         _root_.Geb.Kernel.Tree := (fun (x21 : _root_.Geb.Kernel.Tree) =>
                         _root_.GebMirror.Metalogic.«Base.anyT»
                           (fun (x22 : _root_.Geb.Kernel.Tree) =>
                             _root_.GebMirror.Metalogic.«Tactics.mentions» x22 x21)
                           (_root_.GebMirror.Metalogic.«Base.take» x11 x16));
                       let x22 : _root_.Geb.Kernel.Tree →
                         _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) =>
                         _root_.Geb.Kernel.leaf 0);
                       _root_.GebMirror.Metalogic.«Base.bindO»
                         (_root_.GebMirror.Metalogic.«Tactics.orO»
                           (_root_.GebMirror.Metalogic.«Tactics.orO»
                             (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                               x21
                               (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19))
                             (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                               x21
                               (_root_.GebMirror.Metalogic.«Prover.nfTerm» x20)))
                           (_root_.GebMirror.Metalogic.«Tactics.orO»
                             (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                               x22
                               (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19))
                             (_root_.GebMirror.Metalogic.«Tactics.stuckVar»
                               x22
                               (_root_.GebMirror.Metalogic.«Prover.nfTerm» x20))))
                         (fun (x23 : _root_.Geb.Kernel.Tree) =>
                           _root_.GebMirror.Metalogic.«Tactics.splitStuck»
                             x0
                             x2
                             x3
                             x23
                             x14
                             x14
                             x15
                             x16
                             x17
                             x18)))))
        (fun (x14 : _root_.List _root_.Geb.Kernel.Tree)
           (x15 : _root_.List _root_.Geb.Kernel.Tree)
           (x16 : _root_.Geb.Kernel.Tree)
           (x17 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Tactics.orO»
            (x12 x14 x15 x16 x17)
            (x13 x14 x15 x16 x17))
        x5
        x7
        x8
        x9
        x10);
    x7

def «Tactics.byAutoC» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x6 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree)
         (x8 : _root_.List _root_.Geb.Kernel.Tree)
         (x9 : _root_.Geb.Kernel.Tree)
         (x10 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.orO»
          (_root_.GebMirror.Metalogic.«Tactics.byWeak» x0 x1 x2 x4 x7 x8 x9 x10)
          (_root_.GebMirror.Metalogic.«Prover.bindNT»
            (_root_.GebMirror.Metalogic.«Prover.eval»
              x0
              x1
              x2
              x4
              (_root_.Geb.Kernel.leaf 4096)
              (_root_.Geb.Kernel.leaf 1)
              x7
              x8
              x9)
            (fun (x11 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.bindNT»
                (_root_.GebMirror.Metalogic.«Prover.eval»
                  x0
                  x1
                  x2
                  x4
                  (_root_.Geb.Kernel.leaf 4096)
                  (_root_.Geb.Kernel.leaf 1)
                  x7
                  x8
                  x10)
                (fun (x12 : _root_.Geb.Kernel.Tree) =>
                  let x13 : _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) =>
                    _root_.Geb.Kernel.leaf 0);
                  _root_.GebMirror.Metalogic.«Base.bindO»
                    (_root_.GebMirror.Metalogic.«Tactics.orO»
                      (_root_.GebMirror.Metalogic.«Tactics.stuckVarC»
                        x13
                        (_root_.GebMirror.Metalogic.«Prover.nfTerm» x11))
                      (_root_.GebMirror.Metalogic.«Tactics.stuckVarC»
                        x13
                        (_root_.GebMirror.Metalogic.«Prover.nfTerm» x12)))
                    (fun (x14 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Tactics.splitStuck»
                        x0
                        x2
                        x3
                        x14
                        x6
                        x6
                        x7
                        x8
                        x9
                        x10)))))
      (_root_.GebMirror.Metalogic.«Tactics.byWeak» x0 x1 x2 x4)
      x5;
    x6

def «Tactics.absStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                   x1;
                                 let x4 : _root_.Geb.Kernel.Tree →
                                   _root_.Geb.Kernel.Tree →
                                     _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.kidsAt»
                                   x3
                                   x2;
                                 fun (x5 : _root_.Geb.Kernel.Tree) =>
                                   if (_root_.Geb.Kernel.Const.equal
                                     x1
                                     (_root_.GebMirror.Metalogic.«Language.rename»
                                       x0
                                       (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                         _root_.Geb.Kernel.Const.add x6 x5))).label ≠ 0 then
                                     _root_.GebMirror.Metalogic.«Language.var» x5
                                   else
                                     _root_.Geb.Kernel.Const.node
                                       x3
                                       ((_root_.Geb.Kernel.Const.child
                                         x1
                                         (_root_.Geb.Kernel.leaf 0)) ::
                                         (x4 x5 (_root_.Geb.Kernel.leaf 0))));
    x3

def «Tactics.abstractTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
      x0
      (_root_.Geb.Kernel.Const.para
        (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Tactics.absStep»
          (_root_.GebMirror.Metalogic.«Derivation.weaken1» x1))
        (_root_.GebMirror.Metalogic.«Derivation.weaken1» x2)
        (_root_.Geb.Kernel.leaf 0));
    x3

def «Tactics.maskRwD» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.Geb.Kernel.Tree := (let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.abstractTerm»
                                           x1
                                           x6
                                           x9;
                                         let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 0)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree);
                                         let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 3)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree);
                                         let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                                           (_root_.GebMirror.Metalogic.«Translation.condT»
                                             x0
                                             x4
                                             (_root_.GebMirror.Metalogic.«Language.app» x10 x6)
                                             x5)
                                           (_root_.GebMirror.Metalogic.«Translation.condT»
                                             x0
                                             x4
                                             (_root_.GebMirror.Metalogic.«Language.app» x10 x7)
                                             x5);
                                         let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 18)
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (_root_.GebMirror.Metalogic.«Theory.l2»
                                             (_root_.GebMirror.Metalogic.«Prover.dNode»
                                               (_root_.Geb.Kernel.leaf 1)
                                               ([] : _root_.List _root_.Geb.Kernel.Tree)
                                               (_root_.GebMirror.Metalogic.«Theory.l2»
                                                 (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                   (_root_.Geb.Kernel.leaf 16)
                                                   (_root_.GebMirror.Metalogic.«Theory.l4»
                                                     x2
                                                     (_root_.Geb.Kernel.Const.node
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1))
                                                     (_root_.Geb.Kernel.Const.node
                                                       (_root_.Geb.Kernel.leaf 0)
                                                       (_root_.GebMirror.Metalogic.«Theory.l5» x4 x5 x6 x8 x10))
                                                     (_root_.Geb.Kernel.leaf 1))
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree))
                                                 (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                   (_root_.Geb.Kernel.leaf 1)
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (_root_.GebMirror.Metalogic.«Theory.l2»
                                                     (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                       (_root_.Geb.Kernel.leaf 2)
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                       (_root_.GebMirror.Metalogic.«Theory.l3»
                                                         x11
                                                         (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                           (_root_.Geb.Kernel.leaf 2)
                                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                           (_root_.GebMirror.Metalogic.«Theory.l2» x11 x3))
                                                         x11))
                                                     (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                       (_root_.Geb.Kernel.leaf 16)
                                                       (_root_.GebMirror.Metalogic.«Theory.l4»
                                                         x2
                                                         (_root_.Geb.Kernel.Const.node
                                                           (_root_.Geb.Kernel.leaf 0)
                                                           (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1))
                                                         (_root_.Geb.Kernel.Const.node
                                                           (_root_.Geb.Kernel.leaf 0)
                                                           (_root_.GebMirror.Metalogic.«Theory.l5»
                                                             x4
                                                             x5
                                                             x7
                                                             x8
                                                             x10))
                                                         (_root_.Geb.Kernel.leaf 0))
                                                       ([] : _root_.List _root_.Geb.Kernel.Tree))))))
                                             x11);
                                         _root_.GebMirror.Metalogic.«Prover.dNode»
                                           (_root_.Geb.Kernel.leaf 24)
                                           (_root_.GebMirror.Metalogic.«Prelude.single» x13)
                                           (_root_.GebMirror.Metalogic.«Theory.l2»
                                             (_root_.GebMirror.Metalogic.«Prover.dNode»
                                               (_root_.Geb.Kernel.leaf 2)
                                               ([] : _root_.List _root_.Geb.Kernel.Tree)
                                               (_root_.GebMirror.Metalogic.«Theory.l2»
                                                 (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                   (_root_.Geb.Kernel.leaf 2)
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (_root_.GebMirror.Metalogic.«Theory.l3» x11 x12 x11))
                                                 (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                   (_root_.Geb.Kernel.leaf 2)
                                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                   (_root_.GebMirror.Metalogic.«Theory.l3» x11 x12 x11))))
                                             x14));
    x10

def «Tactics.maskRw» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree)
    (x11 : _root_.Geb.Kernel.Tree) =>
    let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.maskRwD»
      x0
      x1
      x2
      (_root_.GebMirror.Metalogic.«Prover.dNode»
        (_root_.Geb.Kernel.leaf 16)
        (_root_.GebMirror.Metalogic.«Theory.l4»
          x3
          (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x4)
          (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x5)
          (_root_.Geb.Kernel.leaf 0))
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x6
      x7
      x8
      x9
      x10
      x11;
    x12

def «Tactics.maskStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «Tactics.cond0» :=
  _root_.GebMirror.Metalogic.«Tactics.condOf»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Tactics.mask0» :=
  _root_.GebMirror.Metalogic.«Tactics.maskStep»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420546163746963732e4d61736b29» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Tactics.bindPM» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»);
    x2

def «Tactics.bindCM» :=
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
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»);
    x2

def «Tactics.bindTM» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.Metalogic.«Prelude.get» x0)
    else
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»);
    x2

def «$284f7074696f6e2e69734a75737420546163746963732e4d61736b29» :=
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

def «Tactics.findMask» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x0 x2;
        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420546163746963732e4d61736b29»
          x4).label ≠ 0 then
          x4
        else
          x3)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»
      x1;
    x2

def «Tactics.orMask» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420546163746963732e4d61736b29»
      x0).label ≠ 0 then
      x0
    else
      x1);
    x2

def «$284f7074696f6e2e69734a75737420546163746963732e436f6e6429» :=
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

def «$284f7074696f6e2e66726f6d4d6179626520546163746963732e436f6e6429» :=
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

def «Tactics.maskAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.bindPM»
      (_root_.GebMirror.Metalogic.«Language.bindTP»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x2 x8)
        _root_.GebMirror.Metalogic.«Derivation.eqParts»)
      (fun (x9 : _root_.Geb.Kernel.Tree) =>
        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x9;
        let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p2» x9;
        _root_.GebMirror.Metalogic.«Tactics.bindCM»
          (_root_.GebMirror.Metalogic.«Tactics.condParts» x10)
          (fun (x12 : _root_.Geb.Kernel.Tree) =>
            let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x12)
              (_root_.Geb.Kernel.leaf 0);
            let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x12)
              (_root_.Geb.Kernel.leaf 2);
            let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x12)
              (_root_.Geb.Kernel.leaf 3);
            if (_root_.GebMirror.Metalogic.«Base.not»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x12)
                  (_root_.Geb.Kernel.leaf 1))
                x4)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»
            else
              _root_.GebMirror.Metalogic.«Tactics.bindPM»
                (let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.condParts»
                   x11;
                 if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420546163746963732e436f6e6429»
                   x16).label ≠ 0 then
                   let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520546163746963732e436f6e6429»
                     _root_.GebMirror.Metalogic.«Tactics.cond0»
                     x16;
                   if (_root_.GebMirror.Metalogic.«Prelude.and»
                     (_root_.Geb.Kernel.Const.equal
                       (_root_.GebMirror.Metalogic.«Prelude.at»
                         (_root_.Geb.Kernel.Const.children x17)
                         (_root_.Geb.Kernel.leaf 1))
                       x4)
                     (_root_.Geb.Kernel.Const.equal
                       (_root_.GebMirror.Metalogic.«Prelude.at»
                         (_root_.Geb.Kernel.Const.children x17)
                         (_root_.Geb.Kernel.leaf 3))
                       x15)).label ≠ 0 then
                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                       (_root_.GebMirror.Metalogic.«Language.pr»
                         (_root_.GebMirror.Metalogic.«Prelude.at»
                           (_root_.Geb.Kernel.Const.children x17)
                           (_root_.Geb.Kernel.leaf 2))
                         (_root_.GebMirror.Metalogic.«Prover.dNode»
                           (_root_.Geb.Kernel.leaf 17)
                           (_root_.GebMirror.Metalogic.«Theory.l2» x8 (_root_.Geb.Kernel.leaf 0))
                           ([] : _root_.List _root_.Geb.Kernel.Tree)))
                   else
                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
                 else
                   if (_root_.Geb.Kernel.Const.equal x11 x15).label ≠ 0 then
                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                       (_root_.GebMirror.Metalogic.«Language.pr»
                         x11
                         (_root_.GebMirror.Metalogic.«Prover.dNode»
                           (_root_.Geb.Kernel.leaf 1)
                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                           (_root_.GebMirror.Metalogic.«Theory.l2»
                             (_root_.GebMirror.Metalogic.«Prover.dNode»
                               (_root_.Geb.Kernel.leaf 17)
                               (_root_.GebMirror.Metalogic.«Theory.l2» x8 (_root_.Geb.Kernel.leaf 0))
                               ([] : _root_.List _root_.Geb.Kernel.Tree))
                             (_root_.GebMirror.Metalogic.«Prover.dNode»
                               (_root_.Geb.Kernel.leaf 16)
                               (_root_.GebMirror.Metalogic.«Theory.l4»
                                 x1
                                 (_root_.Geb.Kernel.Const.node
                                   (_root_.Geb.Kernel.leaf 0)
                                   (_root_.GebMirror.Metalogic.«Prelude.single» x13))
                                 (_root_.Geb.Kernel.Const.node
                                   (_root_.Geb.Kernel.leaf 0)
                                   (_root_.GebMirror.Metalogic.«Theory.l2» x4 x11))
                                 (_root_.Geb.Kernel.leaf 1))
                               ([] : _root_.List _root_.Geb.Kernel.Tree)))))
                   else
                     _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»)
                (fun (x16 : _root_.Geb.Kernel.Tree) =>
                  let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x16;
                  if (_root_.Geb.Kernel.Const.equal x14 x17).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»
                  else
                    let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.abstractTerm»
                      x13
                      x14
                      x5;
                    _root_.GebMirror.Metalogic.«Tactics.bindTM»
                      (_root_.Geb.Kernel.Const.lcase
                        (α := _root_.Geb.Kernel.Tree)
                        (β := _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Language.mArgs» x18)
                        _root_.GebMirror.Metalogic.«Prelude.none»
                        (fun (x19 : _root_.Geb.Kernel.Tree)
                           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Prelude.some» x19))
                      (fun (x19 : _root_.Geb.Kernel.Tree) =>
                        if (_root_.Geb.Kernel.Const.eq
                          (_root_.GebMirror.Metalogic.«Prover.uses» x19 (_root_.Geb.Kernel.leaf 0))
                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720546163746963732e4d61736b29»
                        else
                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420546163746963732e4d61736b29»
                            (_root_.GebMirror.Metalogic.«Tactics.maskStep»
                              x7
                              (_root_.GebMirror.Metalogic.«Translation.condT»
                                x3
                                x4
                                (_root_.GebMirror.Metalogic.«Language.subst»
                                  x19
                                  (_root_.GebMirror.Metalogic.«Derivation.instVar» x17))
                                x6)
                              (_root_.GebMirror.Metalogic.«Tactics.maskRwD»
                                x3
                                x13
                                x0
                                (_root_.GebMirror.Metalogic.«Language.p2» x16)
                                x4
                                x6
                                x14
                                x17
                                x15
                                x5))))));
    x9

def «Tactics.maskSub» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.findMask»
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.bindCM»
          (_root_.GebMirror.Metalogic.«Tactics.condParts» x4)
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Tactics.findMask»
              (_root_.GebMirror.Metalogic.«Tactics.maskAt»
                x0
                x1
                x2
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x5)
                  (_root_.Geb.Kernel.leaf 0))
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x5)
                  (_root_.Geb.Kernel.leaf 1))
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x5)
                  (_root_.Geb.Kernel.leaf 2))
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x5)
                  (_root_.Geb.Kernel.leaf 3))
                x4)
              (_root_.GebMirror.Metalogic.«Prelude.reverse»
                (_root_.GebMirror.Metalogic.«Base.range» (_root_.GebMirror.Metalogic.«Prelude.length» x2)))))
      (_root_.GebMirror.Metalogic.«Tactics.openSubterms» x3);
    x4

def «$284f7074696f6e2e66726f6d4d6179626520546163746963732e4d61736b29» :=
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

def «Tactics.byMaskSubs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        (_root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x6 : _root_.List _root_.Geb.Kernel.Tree →
           (_root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree)
         (x8 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Tactics.byNF»
          x0
          x1
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Metalogic.«Tactics.appendNR» x7 x4)
          (_root_.Geb.Kernel.leaf 1)
          (fun (x9 : _root_.List _root_.Geb.Kernel.Tree)
             (x10 : _root_.List _root_.Geb.Kernel.Tree)
             (x11 : _root_.Geb.Kernel.Tree)
             (x12 : _root_.Geb.Kernel.Tree) =>
            let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.orMask»
              (_root_.GebMirror.Metalogic.«Tactics.maskSub» x2 x3 x10 x11)
              (_root_.GebMirror.Metalogic.«Tactics.maskSub» x2 x3 x10 x12);
            if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420546163746963732e4d61736b29»
              x13).label ≠ 0 then
              let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                (_root_.Geb.Kernel.Const.children
                  (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520546163746963732e4d61736b29»
                    _root_.GebMirror.Metalogic.«Tactics.mask0»
                    x13))
                (_root_.Geb.Kernel.leaf 0);
              let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                (_root_.Geb.Kernel.Const.children
                  (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520546163746963732e4d61736b29»
                    _root_.GebMirror.Metalogic.«Tactics.mask0»
                    x13))
                (_root_.Geb.Kernel.leaf 1);
              _root_.GebMirror.Metalogic.«Base.mapO»
                (fun (x16 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Prover.dNode»
                    (_root_.Geb.Kernel.leaf 22)
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.mEq» x14 x15))
                    (_root_.GebMirror.Metalogic.«Theory.l2»
                      (_root_.GebMirror.Metalogic.«Prelude.at»
                        (_root_.Geb.Kernel.Const.children
                          (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520546163746963732e4d61736b29»
                            _root_.GebMirror.Metalogic.«Tactics.mask0»
                            x13))
                        (_root_.Geb.Kernel.leaf 2))
                      x16))
                (x6
                  ((_root_.GebMirror.Metalogic.«Tactics.hypRule»
                    (_root_.GebMirror.Metalogic.«Prelude.length» x10)) ::
                    x7)
                  x8
                  x9
                  (_root_.GebMirror.Metalogic.«Prelude.append»
                    x10
                    (_root_.GebMirror.Metalogic.«Prelude.single»
                      (_root_.GebMirror.Metalogic.«Language.mEq» x14 x15)))
                  x11
                  x12)
            else
              x8 x7 x9 x10 x11 x12))
      (fun (x6 : _root_.List _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        x7 x6)
      x5
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x6

def «Tactics.byGeneralize» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree) =>
      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.abstractTerm»
        x0
        x1
        x5;
      let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Tactics.abstractTerm»
        x0
        x1
        x6;
      _root_.GebMirror.Metalogic.«Base.mapO»
        (fun (x9 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Tactics.applyAbs»
            x1
            (_root_.GebMirror.Metalogic.«Prelude.length» x4)
            x7
            x8
            (_root_.GebMirror.Metalogic.«Prover.dNode»
              (_root_.Geb.Kernel.leaf 26)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Prelude.single» x9)))
        (x2
          (x0 :: x3)
          (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x4)
          (_root_.GebMirror.Metalogic.«Language.app»
            (_root_.GebMirror.Metalogic.«Derivation.weaken1» x7)
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Language.app»
            (_root_.GebMirror.Metalogic.«Derivation.weaken1» x8)
            (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))));
    x3

end GebMirror.Metalogic

end
