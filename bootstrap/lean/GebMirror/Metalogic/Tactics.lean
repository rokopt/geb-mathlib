module

public import GebMirror.Metalogic.Prover

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Tactics.ttL» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mDefn» x0 ([] : List T) ([] : List T); x1

def «Tactics.impL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 2))
      ([] : List T)
      («Theory.l2» x2 x1);
    x3

def «Tactics.trueI» :=
  «Prover.dNode»
    (leaf 23)
    ([] : List T)
    («Theory.l2»
      («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
      («Prover.dNode»
        (leaf 18)
        ([] : List T)
        («Theory.l2»
          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))
          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T)))))

def «Tactics.impI» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Prover.dNode»
      (leaf 23)
      ([] : List T)
      («Theory.l2»
        («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
        («Prover.dNode»
          (leaf 25)
          ([] : List T)
          («Theory.l2»
            («Prover.dNode»
              (leaf 27)
              («Theory.l3»
                (Const.add x0 (leaf 2))
                (Const.node (leaf 0) ([] : List T))
                (Const.node (leaf 0) («Theory.l2» x3 x2)))
              («Prelude.single»
                («Prover.dNode» (leaf 21) («Prelude.single» x1) ([] : List T))))
            («Prover.dNode»
              (leaf 27)
              («Theory.l3»
                (Const.add x0 (leaf 1))
                (Const.node (leaf 0) ([] : List T))
                (Const.node (leaf 0) («Theory.l2» x3 x2)))
              («Theory.l2»
                («Prover.dNode» (leaf 21) («Prelude.single» x1) ([] : List T))
                x4)))));
    x5

def «Tactics.mApps» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T → T)
      (fun (x2 : T) (x3 : T → T) (x4 : T) => x3 («Language.mApp» x4 x2))
      (fun (x2 : T) => x2)
      x1
      x0;
    x2

def «Tactics.byMode» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T))) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      «Prover.joinBy»
        («Prover.eval» x1 x2 x3 x4 (leaf 4096) x0)
        x5
        x6
        x7
        x8);
    x5

def «Tactics.byWeak» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T))) =>
    let x4 : List T →
      List T → T → T → T := «Tactics.byMode» (leaf 1) x0 x1 x2 x3;
    x4

def «Tactics.byNF» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : List T → List T → T → T → T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      «Base.bindO»
        («Prover.eval» x0 x1 x2 x3 (leaf 4096) x4 x6 x7 x8)
        (fun (x10 : T) =>
          «Base.bindO»
            («Prover.eval» x0 x1 x2 x3 (leaf 4096) x4 x6 x7 x9)
            (fun (x11 : T) =>
              «Base.mapO»
                (fun (x12 : T) =>
                  «Prover.dNode»
                    (leaf 23)
                    ([] : List T)
                    («Theory.l2»
                      («Prover.dNode»
                        (leaf 2)
                        ([] : List T)
                        («Theory.l2»
                          («Language.p1» («Language.p2» x10))
                          («Language.p1» («Language.p2» x11))))
                      x12))
                (x5 x6 x7 («Language.p1» x10) («Language.p1» x11)))));
    x6

def «Tactics.appendNR» :=
  fun (x0 : List (T × (T → T → List T → T)))
    (x1 : List (T × (T → T → List T → T))) =>
    let x2 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T × (T → T → List T → T))
      (β := List (T × (T → T → List T → T)))
      (fun (x2 : T × (T → T → List T → T))
         (x3 : List (T × (T → T → List T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Tactics.hypRule» :=
  fun (x0 : T) =>
    let x1 : T ×
      (T →
        T →
          List T →
            T) := (Const.node (leaf 6) («Prelude.single» x0),
      «Prover.noMatch»);
    x1

def «Tactics.hypRules» :=
  fun (x0 : T) =>
    let x1 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T)
      (β := List (T × (T → T → List T → T)))
      (fun (x1 : T) (x2 : List (T × (T → T → List T → T))) =>
        ((«Tactics.hypRule» x1) :: x2))
      ([] : List (T × (T → T → List T → T)))
      («Base.range» x0);
    x1

def «Tactics.normH» :=
  fun (x0 : T) (x1 : List T) (x2 : List (T × (T → T → List T → T))) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «Prover.byNormW»
        x0
        x1
        (leaf 0)
        («Tactics.appendNR» («Tactics.hypRules» («Prelude.length» x4)) x2)
        (leaf 1024)
        x3
        x4
        x5
        x6);
    x3

def «Tactics.funExts» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := Const.iter
      (α := List T → List T → T → T → T)
      (fun (x3 : List T → List T → T → T → T) =>
        «Prover.byFunExt» x1 (leaf 0) x3)
      x2
      x0;
    x3

def «Tactics.byListIndWeak» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T))) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      Const.lcase
        (α := T)
        (β := T)
        x5
        «Prelude.none»
        (fun (x9 : T) (x10 : List T) =>
          «Base.bindO»
            («Language.listPart» x9)
            (fun (x11 : T) =>
              «Base.bindO»
                («Derivation.lowerHyps» x0 x2 x10 x6)
                (fun (x12 : T) =>
                  let x13 : List T := Const.children x12;
                  let x14 : List T := (x9 :: (x11 :: x10));
                  let x15 : List T := «Base.mapT» «Derivation.weaken2» x13;
                  «Base.bindO»
                    («Tactics.byWeak»
                      x0
                      x1
                      x2
                      x4
                      x10
                      x13
                      («Prover.instAt» (leaf 0) («Prelude.single» x11) x7)
                      («Prover.instAt» (leaf 0) («Prelude.single» x11) x8))
                    (fun (x16 : T) =>
                      «Base.bindO»
                        («Tactics.byWeak»
                          x0
                          x1
                          x2
                          x4
                          x14
                          x15
                          («Derivation.listConsAt» (leaf 1) x11 x7)
                          («Language.subst»
                            x3
                            («Derivation.atVar0» («Derivation.weakenElem» x7))))
                        (fun (x17 : T) =>
                          «Base.mapO»
                            (fun (x18 : T) =>
                              «Prover.dNode»
                                (leaf 20)
                                («Theory.l3» (leaf 0) (leaf 1) x3)
                                («Theory.l3» x16 x17 x18))
                            («Tactics.byWeak»
                              x0
                              x1
                              x2
                              x4
                              x14
                              x15
                              («Derivation.listConsAt» (leaf 1) x11 x8)
                              («Language.subst»
                                x3
                                («Derivation.atVar0» («Derivation.weakenElem» x8))))))))));
    x5

def «Tactics.byRoseIndWith» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (_ : List T) (x6 : T) (x7 : T) =>
      if (Const.eq («Prelude.length» x4) (leaf 1)).label ≠ 0 then
        let x8 : T := «Prelude.at» x4 (leaf 0);
        «Base.bindO»
          («Language.roseLabel» x8)
          (fun (x9 : T) =>
            «Base.bindO»
              («Derivation.mTypeIn» x0 x1 x4 x6)
              (fun (x10 : T) =>
                let x11 : List T := «Theory.l2» («Theory.list» x8) x9;
                «Base.bindO»
                  (x3
                    x11
                    ([] : List T)
                    («Derivation.roseNodeAt» (leaf 2) x8 x9 x6)
                    («Language.subst»
                      x2
                      («Derivation.atVar0»
                        («Derivation.roseMapAt» (leaf 0) (leaf 1) x10 x6))))
                  (fun (x12 : T) =>
                    «Base.mapO»
                      (fun (x13 : T) =>
                        «Prover.dNode»
                          (leaf 32)
                          («Theory.l4» (leaf 2) (leaf 0) (leaf 1) x2)
                          («Theory.l2» x12 x13))
                      (x3
                        x11
                        ([] : List T)
                        («Derivation.roseNodeAt» (leaf 2) x8 x9 x7)
                        («Language.subst»
                          x2
                          («Derivation.atVar0»
                            («Derivation.roseMapAt» (leaf 0) (leaf 1) x10 x7)))))))
      else
        «Prelude.none»);
    x4

def «Tactics.applyAbs» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Prover.dNode»
      (leaf 22)
      («Prelude.single» («Language.mEq» x2 x3))
      («Theory.l2»
        x4
        («Prover.dNode»
          (leaf 24)
          («Prelude.single»
            («Language.mEq» («Language.mApp» x2 x0) («Language.mApp» x3 x0)))
          («Theory.l2»
            («Prover.dNode»
              (leaf 2)
              ([] : List T)
              («Theory.l2»
                («Prover.dNode» (leaf 3) ([] : List T) ([] : List T))
                («Prover.dNode» (leaf 3) ([] : List T) ([] : List T))))
            («Prover.dNode»
              (leaf 18)
              ([] : List T)
              («Theory.l2»
                («Prover.dNode»
                  (leaf 2)
                  ([] : List T)
                  («Theory.l2»
                    («Prover.dNode» (leaf 17) («Theory.l2» x1 (leaf 0)) ([] : List T))
                    («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                («Prover.dNode» (leaf 0) ([] : List T) ([] : List T)))))));
    x5

def «Tactics.byListSplit» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T → List T → T → T → T)
    (x4 : List T → List T → T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      «Base.bindO»
        («Prelude.nth» x5 x2)
        (fun (x9 : T) =>
          let x10 : T := «Prover.abstractVar» x2 x9 x7;
          let x11 : T := «Prover.abstractVar» x2 x9 x8;
          «Base.mapO»
            (fun (x12 : T) =>
              «Tactics.applyAbs»
                («Language.mVar» x2)
                («Prelude.length» x6)
                x10
                x11
                («Prover.dNode» (leaf 26) ([] : List T) («Prelude.single» x12)))
            («Prover.byListIndWith»
              x0
              x1
              (leaf 0)
              (leaf 1)
              x3
              x4
              (x9 :: x5)
              («Base.mapT» «Derivation.weaken1» x6)
              («Language.mApp»
                («Derivation.weaken1» x10)
                («Language.mVar» (leaf 0)))
              («Language.mApp»
                («Derivation.weaken1» x11)
                («Language.mVar» (leaf 0))))));
    x5

def «Tactics.bySplit2» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T → List T → T → T → T)
    (x4 : List T → List T → T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      «Base.bindO»
        («Prelude.nth» x5 x2)
        (fun (x9 : T) =>
          «Base.bindO»
            («Language.coprodParts» x9)
            (fun (x10 : T) =>
              let x11 : T := «Language.p1» x10;
              let x12 : T := «Language.p2» x10;
              let x13 : T := «Prover.abstractVar» x2 x9 x7;
              let x14 : T := «Prover.abstractVar» x2 x9 x8;
              let x15 : T →
                T →
                  T := (fun (x15 : T) (x16 : T) =>
                «Language.mApp»
                  («Derivation.weaken1» x16)
                  («Language.mArr»
                    x15
                    («Theory.l2» x11 x12)
                    («Language.mVar» (leaf 0))));
              «Base.bindO»
                (x3
                  (x11 :: x5)
                  («Base.mapT» «Derivation.weaken1» x6)
                  (x15 x0 x13)
                  (x15 x0 x14))
                (fun (x16 : T) =>
                  «Base.mapO»
                    (fun (x17 : T) =>
                      «Tactics.applyAbs»
                        («Language.mVar» x2)
                        («Prelude.length» x6)
                        x13
                        x14
                        («Prover.dNode»
                          (leaf 26)
                          ([] : List T)
                          («Prelude.single»
                            («Prover.dNode»
                              (leaf 34)
                              («Theory.l2» x0 x1)
                              («Theory.l2» x16 x17)))))
                    (x4
                      (x12 :: x5)
                      («Base.mapT» «Derivation.weaken1» x6)
                      (x15 x1 x13)
                      (x15 x1 x14))))));
    x5

def «Tactics.byListCases» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T → T → T := «Prover.byListIndWith» x0 x1 (leaf 0) (leaf 1) x2 x2;
    x3

def «Tactics.bitsInd» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T → T)
    (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «Prover.byListIndWith»
      x0
      x1
      (leaf 0)
      (leaf 1)
      x2
      («Prover.bySplit» (leaf 3) (leaf 4) (leaf 1) x3);
    x4

def «Tactics.bitsCases» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T → List T → T → T → T := «Tactics.bitsInd» x0 x1 x2 x2;
    x3

def «Tactics.byBits» :=
  fun (x0 : T) (x1 : List T → List T → T → T → T) (x2 : T) =>
    let x3 : T →
      List T →
        List T →
          T →
            T →
              T := Const.iter
      (α := T → List T → List T → T → T → T)
      (fun (x3 : T → List T → List T → T → T → T) (x4 : T) =>
        «Tactics.byListSplit»
          x0
          (leaf 0)
          x4
          x1
          («Tactics.bySplit2»
            (leaf 3)
            (leaf 4)
            (leaf 1)
            (x3 (leaf 1))
            (x3 (leaf 1))))
      (fun (_ : T) => x1)
      x2;
    x3

def «Tactics.byLength3» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T → T)
    (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «Tactics.byListSplit»
      x0
      (leaf 0)
      x1
      x3
      («Tactics.byListSplit»
        x0
        (leaf 0)
        (leaf 0)
        x3
        («Tactics.byListSplit»
          x0
          (leaf 0)
          (leaf 0)
          x3
          («Tactics.byListSplit» x0 (leaf 0) (leaf 0) x2 x3)));
    x4

def «Tactics.withWeakHyps» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : List T)
    (x5 : List (T × (T → T → List T → T)) → List T → List T → T → T → T)
    (x6 : T) =>
    let x7 : List T →
      List T →
        T →
          T →
            T := (fun (x7 : List T) (x8 : List T) (x9 : T) (x10 : T) =>
      Const.foldr
        (α := T)
        (β := List T → List (T × (T → T → List T → T)) → T)
        (fun (x11 : T)
           (x12 : List T → List (T × (T → T → List T → T)) → T)
           (x13 : List T)
           (x14 : List (T × (T → T → List T → T))) =>
          «Base.bindO»
            («Base.bindO» («Prelude.nth» x13 x11) «Derivation.eqParts»)
            (fun (x15 : T) =>
              «Base.bindO»
                («Prover.eval» x0 x1 x2 x3 (leaf 4096) x6 x7 x13 («Language.p1» x15))
                (fun (x16 : T) =>
                  «Base.bindO»
                    («Prover.eval» x0 x1 x2 x3 (leaf 4096) x6 x7 x13 («Language.p2» x15))
                    (fun (x17 : T) =>
                      let x18 : T := «Language.mEq» («Language.p1» x16) («Language.p1» x17);
                      «Base.mapO»
                        (fun (x19 : T) =>
                          «Prover.dNode»
                            (leaf 22)
                            («Prelude.single» x18)
                            («Theory.l2»
                              («Prover.dNode»
                                (leaf 24)
                                («Prelude.single»
                                  («Language.mEq» («Language.p1» x15) («Language.p2» x15)))
                                («Theory.l2»
                                  («Prover.dNode»
                                    (leaf 2)
                                    ([] : List T)
                                    («Theory.l2»
                                      («Language.p1» («Language.p2» x16))
                                      («Language.p1» («Language.p2» x17))))
                                  («Prover.dNode» (leaf 21) («Prelude.single» x11) ([] : List T))))
                              x19))
                        (x12
                          («Prelude.append» x13 («Prelude.single» x18))
                          («Tactics.appendNR»
                            x14
                            ((«Tactics.hypRule» («Prelude.length» x13)) ::
                              ([] : List (T × (T → T → List T → T))))))))))
        (fun (x11 : List T) (x12 : List (T × (T → T → List T → T))) =>
          x5 x12 x7 x11 x9 x10)
        x4
        x8
        ([] : List (T × (T → T → List T → T))));
    x7

def «Tactics.byListIndHypWeak» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T))) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «Prover.byListIndWith»
      x0
      x2
      (leaf 0)
      (leaf 1)
      («Tactics.byWeak» x0 x1 x2 x3)
      (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
        «Tactics.withWeakHyps»
          x0
          x1
          x2
          x3
          («Prelude.single» (Const.sub («Prelude.length» x5) (leaf 1)))
          (fun (x8 : List (T × (T → T → List T → T))) =>
            «Tactics.byWeak» x0 x1 x2 («Tactics.appendNR» x8 x3))
          (leaf 1)
          x4
          x5
          x6
          x7);
    x4

def «Tactics.byBitsIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List (T × (T → T → List T → T)))
    (x3 : T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «Prover.byListIndWith»
      x0
      (leaf 0)
      (leaf 0)
      (leaf 1)
      («Tactics.byMode» x3 x0 x1 (leaf 0) x2)
      («Prover.bySplit»
        (leaf 3)
        (leaf 4)
        (leaf 1)
        (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
          «Tactics.withWeakHyps»
            x0
            x1
            (leaf 0)
            x2
            («Prelude.single» (Const.sub («Prelude.length» x5) (leaf 1)))
            (fun (x8 : List (T × (T → T → List T → T))) =>
              «Tactics.byMode» x3 x0 x1 (leaf 0) («Tactics.appendNR» x8 x2))
            x3
            x4
            x5
            x6
            x7));
    x4

def «Tactics.rwFun» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.iter
      (α := T)
      (fun (x2 : T) =>
        «Prover.dNode»
          (leaf 2)
          ([] : List T)
          («Theory.l2»
            x2
            («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
      («Prover.dNode» (leaf 17) («Theory.l2» x0 (leaf 0)) ([] : List T))
      x1;
    x2

def «Tactics.instEqs» :=
  fun (x0 : T) (x1 : T) (x2 : List (List T)) =>
    let x3 : List
      T := Const.foldr
      (α := List T)
      (β := List T)
      (fun (x3 : List T) (x4 : List T) =>
        ((«Language.mEq» («Tactics.mApps» x0 x3) («Tactics.mApps» x1 x3)) ::
          x4))
      ([] : List T)
      x2;
    x3

def «Tactics.cutInsts» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (List T)) (x4 : T) =>
    let x5 : T := Const.foldr
      (α := List T)
      (β := T)
      (fun (x5 : List T) (x6 : T) =>
        «Prover.dNode»
          (leaf 22)
          («Prelude.single»
            («Language.mEq» («Tactics.mApps» x0 x5) («Tactics.mApps» x1 x5)))
          («Theory.l2»
            («Prover.dNode»
              (leaf 18)
              ([] : List T)
              («Theory.l2»
                («Tactics.rwFun» x2 («Prelude.length» x5))
                («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
            x6))
      x4
      x3;
    x5

def «Tactics.withInsts» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : List (List T))
    (x6 : List (T × (T → T → List T → T)) → List T → List T → T → T → T)
    (x7 : T) =>
    let x8 : List T →
      List T →
        T →
          T →
            T := (fun (x8 : List T) (x9 : List T) (x10 : T) (x11 : T) =>
      «Base.bindO»
        («Base.bindO» («Prelude.nth» x9 x4) «Derivation.eqParts»)
        (fun (x12 : T) =>
          let x13 : List
            T := «Tactics.instEqs» («Language.p1» x12) («Language.p2» x12) x5;
          «Base.mapO»
            (fun (x14 : T) =>
              «Tactics.cutInsts» («Language.p1» x12) («Language.p2» x12) x4 x5 x14)
            («Tactics.withWeakHyps»
              x0
              x1
              x2
              x3
              («Base.mapT»
                (fun (x14 : T) => Const.add («Prelude.length» x9) x14)
                («Base.range» («Prelude.length» x13)))
              x6
              x7
              x8
              («Prelude.append» x9 x13)
              x10
              x11)));
    x8

def «Tactics.nthOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Translation.call»
      (leaf 8)
      («Prelude.single» «Theory.omega»)
      («Theory.l2»
        («Language.mEq» «Language.mStar» «Language.mStar»)
        (Const.iter
          (α := T)
          (fun (x2 : T) =>
            «Translation.call»
              (leaf 7)
              («Prelude.single» «Theory.omega»)
              («Prelude.single» x2))
          x0
          x1));
    x2

def «Tactics.withChildHyps» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : List T)
    (x6 : T → List (List T))
    (x7 : List T → List T → List T → T → T → T) =>
    let x8 : List T →
      List T →
        T →
          T →
            T := (fun (x8 : List T) (x9 : List T) (x10 : T) (x11 : T) =>
      «Base.bindO»
        («Base.bindO» («Prelude.nth» x9 x4) «Derivation.eqParts»)
        (fun (x12 : T) =>
          Const.foldr
            (α := T)
            (β := List T → List T → T)
            (fun (x13 : T)
               (x14 : List T → List T → T)
               (x15 : List T)
               (x16 : List T) =>
              let x17 : T := «Tactics.nthOf» («Language.p1» x12) x13;
              let x18 : T := «Tactics.nthOf» («Language.p2» x12) x13;
              «Base.bindO»
                («Prover.eval» x0 x1 x2 x3 (leaf 4096) (leaf 1) x8 x15 x17)
                (fun (x19 : T) =>
                  «Base.bindO»
                    («Prover.eval» x0 x1 x2 x3 (leaf 4096) (leaf 1) x8 x15 x18)
                    (fun (x20 : T) =>
                      «Base.bindO»
                        («Prover.eval»
                          x0
                          x1
                          x2
                          ((«Tactics.hypRule» x4) :: ([] : List (T × (T → T → List T → T))))
                          (leaf 4096)
                          (leaf 1)
                          x8
                          x15
                          x17)
                        (fun (x21 : T) =>
                          «Base.bindO»
                            («Derivation.eqParts» («Language.p1» x19))
                            (fun (x22 : T) =>
                              let x23 : T := «Prelude.length» x15;
                              let x24 : T := Const.add x23 (leaf 1);
                              let x25 : List (List T) := x6 x13;
                              let x26 : List
                                T := «Tactics.instEqs» («Language.p1» x22) («Language.p2» x22) x25;
                              «Base.mapO»
                                (fun (x27 : T) =>
                                  «Prover.dNode»
                                    (leaf 22)
                                    («Prelude.single»
                                      («Language.mEq» («Language.p1» x19) («Language.p1» x20)))
                                    («Theory.l2»
                                      («Prover.dNode»
                                        (leaf 24)
                                        («Prelude.single» («Language.mEq» x17 x18))
                                        («Theory.l2»
                                          («Prover.dNode»
                                            (leaf 2)
                                            ([] : List T)
                                            («Theory.l2»
                                              («Language.p1» («Language.p2» x19))
                                              («Language.p1» («Language.p2» x20))))
                                          («Prover.dNode»
                                            (leaf 18)
                                            ([] : List T)
                                            («Theory.l2»
                                              («Language.p1» («Language.p2» x21))
                                              («Prover.dNode»
                                                (leaf 0)
                                                ([] : List T)
                                                ([] : List T))))))
                                      («Prover.dNode»
                                        (leaf 22)
                                        («Prelude.single» («Language.p1» x19))
                                        («Theory.l2»
                                          («Prover.dNode»
                                            (leaf 23)
                                            ([] : List T)
                                            («Theory.l2»
                                              («Prover.dNode»
                                                (leaf 17)
                                                («Theory.l2» x23 (leaf 0))
                                                ([] : List T))
                                              («Prover.dNode»
                                                (leaf 18)
                                                ([] : List T)
                                                («Theory.l2»
                                                  («Prover.dNode»
                                                    (leaf 0)
                                                    ([] : List T)
                                                    ([] : List T))
                                                  («Prover.dNode»
                                                    (leaf 0)
                                                    ([] : List T)
                                                    ([] : List T))))))
                                          («Tactics.cutInsts»
                                            («Language.p1» x22)
                                            («Language.p2» x22)
                                            x24
                                            x25
                                            x27)))))
                                (x14
                                  («Prelude.append»
                                    («Prelude.append»
                                      x15
                                      («Theory.l2»
                                        («Language.mEq» («Language.p1» x19) («Language.p1» x20))
                                        («Language.p1» x19)))
                                    x26)
                                  («Prelude.append»
                                    x16
                                    («Base.mapT»
                                      (fun (x27 : T) => Const.add (Const.add x24 (leaf 1)) x27)
                                      («Base.range» («Prelude.length» x26))))))))))
            (fun (x13 : List T) (x14 : List T) => x7 x14 x8 x13 x10 x11)
            x5
            x9
            ([] : List T)));
    x8

def «Tactics.subVar» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.subst»
      («Derivation.weaken1» x1)
      (fun (x2 : T) =>
        if (Const.eq x2 (Const.add x0 (leaf 1))).label ≠ 0 then
          «Language.mVar» (leaf 0)
        else
          «Language.mVar» x2);
    x2

def «Tactics.revertCase» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : List T → List T → T → T → T)
    (x7 : List T → List T → T → T → T) =>
    let x8 : List T →
      List T →
        T →
          T →
            T := (fun (x8 : List T) (x9 : List T) (x10 : T) (x11 : T) =>
      «Base.bindO»
        («Prelude.nth» x8 x4)
        (fun (x12 : T) =>
          «Base.bindO»
            («Language.listPart» x12)
            (fun (x13 : T) =>
              «Base.bindO»
                («Prelude.nth» x9 x5)
                (fun (x14 : T) =>
                  let x15 : T := «Language.mEq» x10 x11;
                  let x16 : T := «Tactics.ttL» x2;
                  let x17 : T := «Prover.abstractVar»
                    x4
                    x12
                    («Tactics.impL» x2 x14 x15);
                  let x18 : T → T := (fun (x18 : T) => «Tactics.subVar» x4 x18);
                  let x19 : T := x18 x14;
                  let x20 : T := x18 x15;
                  «Base.bindO»
                    («Derivation.lowerHyps»
                      x0
                      x1
                      x8
                      («Prelude.append»
                        («Base.mapT» «Derivation.weaken1» x9)
                        («Prelude.single» x16)))
                    (fun (x21 : T) =>
                      let x22 : List T := Const.children x21;
                      let x23 : T := «Prover.instAt» (leaf 0) («Prelude.single» x13) x19;
                      let x24 : T := «Prover.instAt» (leaf 0) («Prelude.single» x13) x20;
                      «Base.bindO»
                        («Derivation.eqParts» x24)
                        (fun (x25 : T) =>
                          «Base.bindO»
                            (x6
                              x8
                              («Prelude.append» x22 («Prelude.single» x23))
                              («Language.p1» x25)
                              («Language.p2» x25))
                            (fun (x26 : T) =>
                              let x27 : List
                                T := «Prelude.append»
                                («Base.mapT» «Derivation.weaken2» x22)
                                («Prelude.single»
                                  («Derivation.weakenElem» («Tactics.impL» x2 x19 x20)));
                              let x28 : T := «Derivation.listConsAt» (leaf 1) x13 x19;
                              let x29 : T := «Derivation.listConsAt» (leaf 1) x13 x20;
                              «Base.bindO»
                                («Derivation.eqParts» x29)
                                (fun (x30 : T) =>
                                  «Base.mapO»
                                    (fun (x31 : T) =>
                                      let x32 : T := «Prover.dNode»
                                        (leaf 29)
                                        («Theory.l2» (leaf 0) (leaf 1))
                                        («Theory.l2»
                                          («Tactics.impI» x3 («Prelude.length» x22) x23 x24 x26)
                                          («Tactics.impI» x3 («Prelude.length» x27) x28 x29 x31));
                                      let x33 : T := «Prover.dNode»
                                        (leaf 26)
                                        ([] : List T)
                                        («Prelude.single»
                                          («Prover.dNode»
                                            (leaf 23)
                                            ([] : List T)
                                            («Theory.l2»
                                              («Prover.dNode»
                                                (leaf 2)
                                                ([] : List T)
                                                («Theory.l2»
                                                  («Prover.dNode»
                                                    (leaf 3)
                                                    ([] : List T)
                                                    ([] : List T))
                                                  («Prover.dNode»
                                                    (leaf 3)
                                                    ([] : List T)
                                                    ([] : List T))))
                                              («Prover.dNode»
                                                (leaf 25)
                                                ([] : List T)
                                                («Theory.l2» «Tactics.trueI» x32)))));
                                      let x34 : T := «Prover.dNode»
                                        (leaf 22)
                                        («Prelude.single»
                                          («Language.mEq» x17 («Language.mLam» x12 x16)))
                                        («Theory.l2»
                                          x33
                                          («Prover.dNode»
                                            (leaf 24)
                                            («Prelude.single»
                                              («Language.mApp» x17 («Language.mVar» x4)))
                                            («Theory.l2»
                                              («Prover.dNode» (leaf 3) ([] : List T) ([] : List T))
                                              («Prover.dNode»
                                                (leaf 23)
                                                ([] : List T)
                                                («Theory.l2»
                                                  («Prover.dNode»
                                                    (leaf 1)
                                                    ([] : List T)
                                                    («Theory.l2»
                                                      («Prover.dNode»
                                                        (leaf 2)
                                                        ([] : List T)
                                                        («Theory.l2»
                                                          («Prover.dNode»
                                                            (leaf 17)
                                                            («Theory.l2»
                                                              («Prelude.length» x9)
                                                              (leaf 0))
                                                            ([] : List T))
                                                          («Prover.dNode»
                                                            (leaf 0)
                                                            ([] : List T)
                                                            ([] : List T))))
                                                      («Prover.dNode»
                                                        (leaf 3)
                                                        ([] : List T)
                                                        ([] : List T))))
                                                  «Tactics.trueI»)))));
                                      «Prover.dNode»
                                        (leaf 27)
                                        («Theory.l3»
                                          (Const.add x3 (leaf 4))
                                          (Const.node (leaf 0) ([] : List T))
                                          (Const.node (leaf 0) («Theory.l2» x15 x14)))
                                        («Theory.l2»
                                          x34
                                          («Prover.dNode»
                                            (leaf 21)
                                            («Prelude.single» x5)
                                            ([] : List T))))
                                    (x7
                                      (x12 :: (x13 :: x8))
                                      («Prelude.append» x27 («Prelude.single» x28))
                                      («Language.p1» x30)
                                      («Language.p2» x30))))))))));
    x8

def «Tactics.betaRule» :=
  ((Const.node
    (leaf 0)
    («Theory.l2» (leaf 3) (Const.node (leaf 0) ([] : List T))),
    «Prover.noMatch») ::
    ([] : List (T × (T → T → List T → T))))

def «Tactics.byImpI» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      «Base.bindO»
        («Prover.eval»
          x0
          x1
          (leaf 0)
          «Tactics.betaRule»
          (leaf 4096)
          (leaf 0)
          x5
          x6
          x7)
        (fun (x9 : T) =>
          «Base.bindO»
            («Prover.eval»
              x0
              x1
              (leaf 0)
              «Tactics.betaRule»
              (leaf 4096)
              (leaf 0)
              x5
              x6
              x8)
            (fun (x10 : T) =>
              let x11 : T := «Language.p1» x9;
              let x12 : T := «Language.p1» x10;
              if («Prelude.and»
                («Language.mIs» (leaf 11) (leaf 2) x11)
                (Const.eq (Const.label x12) (leaf 11))).label ≠ 0 then
                if («Prelude.and»
                  (Const.eq («Language.mD» x11 (leaf 0)) (Const.add x2 (leaf 2)))
                  (Const.eq («Language.mD» x12 (leaf 0)) x2)).label ≠ 0 then
                  let x13 : T := «Language.mArg» x11 (leaf 0);
                  let x14 : T := «Language.mArg» x11 (leaf 1);
                  «Base.bindO»
                    («Derivation.eqParts» x13)
                    (fun (x15 : T) =>
                      «Base.mapO»
                        (fun (x16 : T) =>
                          «Prover.dNode»
                            (leaf 23)
                            ([] : List T)
                            («Theory.l2»
                              («Prover.dNode»
                                (leaf 2)
                                ([] : List T)
                                («Theory.l2»
                                  («Language.p1» («Language.p2» x9))
                                  («Language.p1» («Language.p2» x10))))
                              («Prover.dNode»
                                (leaf 25)
                                ([] : List T)
                                («Theory.l2»
                                  «Tactics.trueI»
                                  («Tactics.impI»
                                    x3
                                    (Const.add («Prelude.length» x6) (leaf 1))
                                    x14
                                    x13
                                    x16)))))
                        (x4
                          x5
                          («Prelude.append» x6 («Theory.l2» («Tactics.ttL» x2) x14))
                          («Language.p1» x15)
                          («Language.p2» x15)))
                else
                  «Prelude.none»
              else
                «Prelude.none»)));
    x5

def «Tactics.withImpElim» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T)
    (x4 : List (T × (T → T → List T → T)) →
      List T → List T → T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T →
            T := (fun (x5 : List T) (x6 : List T) (x7 : T) (x8 : T) =>
      Const.foldr
        (α := T)
        (β := List T → List (T × (T → T → List T → T)) → T)
        (fun (x9 : T)
           (x10 : List T → List (T × (T → T → List T → T)) → T)
           (x11 : List T)
           (x12 : List (T × (T → T → List T → T))) =>
          «Base.bindO»
            («Base.bindO» («Prelude.nth» x11 x9) «Derivation.eqParts»)
            (fun (x13 : T) =>
              let x14 : T := «Language.p1» x13;
              if («Language.mIs» (leaf 11) (leaf 2) x14).label ≠ 0 then
                if (Const.eq
                  («Language.mD» x14 (leaf 0))
                  (Const.add x0 (leaf 2))).label ≠ 0 then
                  let x15 : T := «Language.mArg» x14 (leaf 0);
                  let x16 : T := «Language.mArg» x14 (leaf 1);
                  «Base.mapO»
                    (fun (x17 : T) =>
                      «Prover.dNode»
                        (leaf 22)
                        («Prelude.single» x15)
                        («Theory.l2»
                          («Prover.dNode»
                            (leaf 27)
                            («Theory.l3»
                              (Const.add x1 (leaf 4))
                              (Const.node (leaf 0) ([] : List T))
                              (Const.node (leaf 0) («Theory.l2» x15 x16)))
                            («Theory.l2»
                              («Prover.dNode»
                                (leaf 23)
                                ([] : List T)
                                («Theory.l2»
                                  («Prover.dNode» (leaf 17) («Theory.l2» x9 (leaf 0)) ([] : List T))
                                  «Tactics.trueI»))
                              («Prover.dNode» (leaf 21) («Prelude.single» x2) ([] : List T))))
                          x17))
                    (x10
                      («Prelude.append» x11 («Prelude.single» x15))
                      («Tactics.appendNR»
                        x12
                        ((«Tactics.hypRule» («Prelude.length» x11)) ::
                          ([] : List (T × (T → T → List T → T))))))
                else
                  «Prelude.none»
              else
                «Prelude.none»))
        (fun (x9 : List T) (x10 : List (T × (T → T → List T → T))) =>
          x4 x10 x5 x9 x7 x8)
        x3
        x6
        ([] : List (T × (T → T → List T → T))));
    x5

def «Tactics.hypIndex» :=
  fun (x0 : T × (T → T → List T → T)) =>
    let x1 : T := (let x1 : T := (x0).1;
                   if (Const.eq (Const.label x1) (leaf 6)).label ≠ 0 then
                     «Prelude.some» (Const.child x1 (leaf 0))
                   else
                     «Prelude.none»);
    x1

def «Tactics.succPredRw» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if («Language.mIs» (leaf 6) (leaf 2) x2).label ≠ 0 then
      let x3 : List
        T := «Theory.l2»
        («Language.mVar» (leaf 1))
        («Language.mVar» (leaf 0));
      «Prelude.some»
        («Language.pr»
          («Language.mApp»
            («Language.mArg» x2 (leaf 0))
            («Derivation.instTerm» ([] : List T) x3 x1))
          («Prover.dNode»
            (leaf 2)
            ([] : List T)
            («Theory.l2»
              («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))
              («Prover.dNode»
                (leaf 16)
                («Theory.l4»
                  x0
                  (Const.node (leaf 0) ([] : List T))
                  (Const.node (leaf 0) x3)
                  (leaf 1))
                ([] : List T)))))
    else
      «Prelude.none»);
    x3

def «Tactics.bySuccPred» :=
  fun (x0 : List T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «Base.bindO»
        («Base.bindO» («Prelude.nth» x0 x1) «Derivation.entryLanguage»)
        (fun (x7 : T) =>
          «Base.bindO»
            («Derivation.eqParts» («Derivation.thConcl» x7))
            (fun (x8 : T) =>
              «Base.bindO»
                («Tactics.succPredRw» x1 («Language.p1» x8) x5)
                (fun (x9 : T) =>
                  «Base.bindO»
                    («Tactics.succPredRw» x1 («Language.p1» x8) x6)
                    (fun (x10 : T) =>
                      «Base.mapO»
                        (fun (x11 : T) =>
                          «Prover.dNode»
                            (leaf 23)
                            ([] : List T)
                            («Theory.l2»
                              («Prover.dNode»
                                (leaf 2)
                                ([] : List T)
                                («Theory.l2» («Language.p2» x9) («Language.p2» x10)))
                              x11))
                        (x2 x3 x4 («Language.p1» x9) («Language.p1» x10)))))));
    x3

def «Tactics.tailTss» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      (List
        T) := Const.lcase
      (α := List T)
      (β := List (List T))
      x0
      ([] : List (List T))
      (fun (_ : List T) (x2 : List (List T)) => x2);
    x1

def «Tactics.concatTss» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      T := Const.foldr
      (α := List T)
      (β := List T)
      (fun (x1 : List T) (x2 : List T) => «Prelude.append» x1 x2)
      ([] : List T)
      x0;
    x1

def «Tactics.subtermsStep» :=
  fun (x0 : T) (x1 : List (List T)) =>
    let x2 : List
      T := (let x2 : T := Const.label x0;
            (x0 ::
              (if (Const.eq x2 (leaf 5)).label ≠ 0 then
                ([] : List T)
              else
                if («Prelude.or»
                  (Const.eq x2 (leaf 8))
                  (Const.eq x2 (leaf 9))).label ≠ 0 then
                  «Tactics.concatTss»
                    (Const.iter (α := List (List T)) «Tactics.tailTss» x1 (leaf 3))
                else
                  if (Const.eq x2 (leaf 10)).label ≠ 0 then
                    «Tactics.concatTss»
                      (Const.iter (α := List (List T)) «Tactics.tailTss» x1 (leaf 2))
                  else
                    «Tactics.concatTss» («Tactics.tailTss» x1))));
    x2

def «Tactics.openSubterms» :=
  fun (x0 : T) =>
    let x1 : List T := Const.para (α := List T) «Tactics.subtermsStep» x0;
    x1

def «Tactics.findSomeT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x0 x2;
        if («Prelude.isSome» x4).label ≠ 0 then x4 else x3)
      «Prelude.none»
      x1;
    x2

def «Tactics.varUnless» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
      let x2 : T := «Language.mD» x1 (leaf 0);
      if (x0 x2).label ≠ 0 then «Prelude.none» else «Prelude.some» x2
    else
      «Prelude.none»);
    x2

def «Tactics.scrutVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Language.mIs» (leaf 6) (leaf 2) x1).label ≠ 0 then
      let x2 : T := «Language.mArg» x1 (leaf 0);
      if («Prelude.and»
        (Const.eq (Const.label x2) (leaf 7))
        (Const.eq («Language.mD» x2 (leaf 0)) (leaf 5))).label ≠ 0 then
        «Tactics.varUnless» x0 («Language.mArg» x1 (leaf 1))
      else
        «Prelude.none»
    else
      «Prelude.none»);
    x2

def «Tactics.datumVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Prelude.or»
      («Language.mIs» (leaf 8) (leaf 3) x1)
      («Language.mIs» (leaf 9) (leaf 3) x1)).label ≠ 0 then
      «Tactics.varUnless» x0 («Language.mArg» x1 (leaf 2))
    else
      if («Language.mIs» (leaf 10) (leaf 2) x1).label ≠ 0 then
        «Tactics.varUnless» x0 («Language.mArg» x1 (leaf 1))
      else
        «Prelude.none»);
    x2

def «Tactics.stuckVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «Tactics.openSubterms» x1;
                   let x3 : T := «Tactics.findSomeT» («Tactics.scrutVar» x0) x2;
                   if («Prelude.isSome» x3).label ≠ 0 then
                     x3
                   else
                     «Tactics.findSomeT» («Tactics.datumVar» x0) x2);
    x2

def «Tactics.mentions» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.lt (leaf 0) («Prover.uses» x0 x1); x2

def «Tactics.eraseDupsTss» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      (List
        T) := Const.foldr
      (α := List T)
      (β := List (List T) → List (List T))
      (fun (x1 : List T)
         (x2 : List (List T) → List (List T))
         (x3 : List (List T)) =>
        if (Const.foldr
          (α := List T)
          (β := T)
          (fun (x4 : List T) (x5 : T) => «Prelude.or» («Base.equalTs» x4 x1) x5)
          (leaf 0)
          x3).label ≠ 0 then
          x2 x3
        else
          x2 (x1 :: x3))
      (fun (x1 : List (List T)) =>
        Const.foldr
          (α := List T)
          (β := List (List T) → List (List T))
          (fun (x2 : List T)
             (x3 : List (List T) → List (List T))
             (x4 : List (List T)) =>
            x3 (x2 :: x4))
          (fun (x2 : List (List T)) => x2)
          x1
          ([] : List (List T)))
      x0
      ([] : List (List T));
    x1

def «Tactics.matchesWith» :=
  fun (x0 : T → T → List T → T) (x1 : T) (x2 : T) =>
    let x3 : List
      (List
        T) := (let x3 : List
                 T := «Base.mapT»
                 (fun (x3 : T) =>
                   if (Const.lt x3 x1).label ≠ 0 then
                     «Prelude.none»
                   else
                     «Prelude.some» («Language.mVar» (Const.sub x3 x1)))
                 («Base.range» (Const.add x1 (leaf 64)));
               «Tactics.eraseDupsTss»
                 (Const.foldr
                   (α := T)
                   (β := List (List T))
                   (fun (x4 : T) (x5 : List (List T)) =>
                     let x6 : T := «Base.bindO»
                       (x0 (leaf 0) x4 x3)
                       (fun (x6 : T) =>
                         «Base.allSomeT» («Base.take» x1 (Const.children x6)));
                     if («Prelude.isSome» x6).label ≠ 0 then
                       ((«Prelude.reverse» (Const.children («Prelude.get» x6))) :: x5)
                     else
                       x5)
                   ([] : List (List T))
                   («Tactics.openSubterms» x2)));
    x3

def «Tactics.matchesOf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List
      (List T) := «Tactics.matchesWith» («Prover.matchTerm» x0) x1 x2;
    x3

def «Tactics.appendTss» :=
  fun (x0 : List (List T)) (x1 : List (List T)) =>
    let x2 : List
      (List
        T) := Const.foldr
      (α := List T)
      (β := List (List T))
      (fun (x2 : List T) (x3 : List (List T)) => (x2 :: x3))
      x1
      x0;
    x2

def «Tactics.instArgs» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T)
    (x9 : T) =>
    let x10 : List
      (List
        T) := (let x10 : T := «Base.bindO»
                 («Prelude.nth» x6 x9)
                 «Derivation.eqParts»;
               if («Prelude.isSome» x10).label ≠ 0 then
                 let x11 : T := «Language.p1» («Prelude.get» x10);
                 if («Language.mIs» (leaf 5) (leaf 1) x11).label ≠ 0 then
                   let x12 : T := «Prover.eval»
                     x1
                     x2
                     x3
                     x4
                     (leaf 4096)
                     x0
                     ((«Language.mD» x11 (leaf 0)) :: x5)
                     («Base.mapT» «Derivation.weaken1» x6)
                     («Language.mArg» x11 (leaf 0));
                   if («Prelude.isSome» x12).label ≠ 0 then
                     let x13 : T := «Language.p1» («Prelude.get» x12);
                     «Tactics.eraseDupsTss»
                       («Tactics.appendTss»
                         («Tactics.matchesOf» x13 (leaf 1) x7)
                         («Tactics.matchesOf» x13 (leaf 1) x8))
                   else
                     ([] : List (List T))
                 else
                   ([] : List (List T))
               else
                 ([] : List (List T)));
    x10

def «Tactics.byInstsOnce» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T)
    (x6 : List (T × (T → T → List T → T)) →
      List T → List T → T → T → T) =>
    let x7 : List T →
      List T →
        T →
          T →
            T := (fun (x7 : List T) (x8 : List T) (x9 : T) (x10 : T) =>
      «Base.bindO»
        («Prover.eval» x1 x2 x3 x4 (leaf 4096) x0 x7 x8 x9)
        (fun (x11 : T) =>
          «Base.bindO»
            («Prover.eval» x1 x2 x3 x4 (leaf 4096) x0 x7 x8 x10)
            (fun (x12 : T) =>
              let x13 : T := «Language.p1» x11;
              let x14 : T := «Language.p1» x12;
              if (Const.equal x13 x14).label ≠ 0 then
                «Tactics.byMode» x0 x1 x2 x3 x4 x7 x8 x9 x10
              else
                let x15 : List
                  (T ×
                    List
                      (List
                        T)) := Const.foldr
                  (α := T)
                  (β := List (T × List (List T)))
                  (fun (x15 : T) (x16 : List (T × List (List T))) =>
                    let x17 : List
                      (List T) := «Tactics.instArgs» x0 x1 x2 x3 x4 x7 x8 x13 x14 x15;
                    Const.lcase
                      (α := List T)
                      (β := List (T × List (List T)))
                      x17
                      x16
                      (fun (_ : List T) (_ : List (List T)) => ((x15, x17) :: x16)))
                  ([] : List (T × List (List T)))
                  («Base.range»
                    (if (Const.lt x5 («Prelude.length» x8)).label ≠ 0 then
                      x5
                    else
                      «Prelude.length» x8));
                Const.lcase
                  (α := T × List (List T))
                  (β := T)
                  x15
                  «Prelude.none»
                  (fun (_ : T × List (List T)) (_ : List (T × List (List T))) =>
                    Const.foldr
                      (α := T × List (List T))
                      (β := List (T × (T → T → List T → T)) → List T → List T → T → T → T)
                      (fun (x18 : T × List (List T))
                         (x19 : List (T × (T → T → List T → T)) → List T → List T → T → T → T)
                         (x20 : List (T × (T → T → List T → T))) =>
                        «Tactics.withInsts»
                          x1
                          x2
                          x3
                          x4
                          (x18).1
                          (x18).2
                          (fun (x21 : List (T × (T → T → List T → T))) =>
                            x19 («Tactics.appendNR» x20 x21))
                          x0)
                      x6
                      x15
                      ([] : List (T × (T → T → List T → T)))
                      x7
                      x8
                      x9
                      x10))));
    x7

def «Tactics.instsLast» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T))) =>
    let x5 : List (T × (T → T → List T → T)) →
      List T →
        List T →
          T →
            T →
              T := (fun (x5 : List (T × (T → T → List T → T))) =>
      «Tactics.byMode» x0 x1 x2 x3 («Tactics.appendNR» x5 x4));
    x5

def «Tactics.instsRound» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T)
    (x6 : List (T × (T → T → List T → T)) →
      List T → List T → T → T → T) =>
    let x7 : List (T × (T → T → List T → T)) →
      List T →
        List T →
          T →
            T →
              T := (fun (x7 : List (T × (T → T → List T → T)))
                      (x8 : List T)
                      (x9 : List T)
                      (x10 : T)
                      (x11 : T) =>
      let x12 : T := «Tactics.byMode»
        x0
        x1
        x2
        x3
        («Tactics.appendNR» x7 x4)
        x8
        x9
        x10
        x11;
      if («Prelude.isSome» x12).label ≠ 0 then
        x12
      else
        «Tactics.byInstsOnce»
          x0
          x1
          x2
          x3
          («Tactics.appendNR» x7 x4)
          x5
          (fun (x13 : List (T × (T → T → List T → T))) =>
            x6 («Tactics.appendNR» x7 x13))
          x8
          x9
          x10
          x11);
    x7

def «Tactics.byInsts» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := «Tactics.instsRound»
      x0
      x1
      x2
      x3
      x4
      x5
      («Tactics.instsRound»
        x0
        x1
        x2
        x3
        x4
        x5
        («Tactics.instsRound»
          x0
          x1
          x2
          x3
          x4
          x5
          («Tactics.instsLast» x0 x1 x2 x3 x4)))
      ([] : List (T × (T → T → List T → T)));
    x6

def «Tactics.orO» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x0).label ≠ 0 then x0 else x1); x2

def «Tactics.byAuto» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      let x10 : T := «Prelude.length» x7;
      Const.iter
        (α := List T → List T → T → T → T)
        (fun (x11 : List T → List T → T → T → T)
           (x12 : List T)
           (x13 : List T)
           (x14 : T)
           (x15 : T) =>
          «Tactics.orO»
            («Tactics.byInsts» x5 x0 x1 x2 x3 x10 x12 x13 x14 x15)
            («Base.bindO»
              («Prover.eval» x0 x1 x2 x3 (leaf 4096) x5 x12 x13 x14)
              (fun (x16 : T) =>
                «Base.bindO»
                  («Prover.eval» x0 x1 x2 x3 (leaf 4096) x5 x12 x13 x15)
                  (fun (x17 : T) =>
                    let x18 : T →
                      T := (fun (x18 : T) =>
                      «Base.anyT»
                        (fun (x19 : T) => «Tactics.mentions» x19 x18)
                        («Base.take» x10 x13));
                    let x19 : T → T := (fun (_ : T) => leaf 0);
                    «Base.bindO»
                      («Tactics.orO»
                        («Tactics.orO»
                          («Tactics.stuckVar» x18 («Language.p1» x16))
                          («Tactics.stuckVar» x18 («Language.p1» x17)))
                        («Tactics.orO»
                          («Tactics.stuckVar» x19 («Language.p1» x16))
                          («Tactics.stuckVar» x19 («Language.p1» x17))))
                      (fun (x20 : T) =>
                        «Base.bindO»
                          («Prelude.nth» x12 x20)
                          (fun (x21 : T) =>
                            if («Prelude.isSome» («Language.listPart» x21)).label ≠ 0 then
                              «Tactics.byListSplit» x0 x2 x20 x11 x11 x12 x13 x14 x15
                            else
                              if («Prelude.isSome» («Language.coprodParts» x21)).label ≠ 0 then
                                «Tactics.bySplit2» (leaf 3) (leaf 4) x20 x11 x11 x12 x13 x14 x15
                              else
                                «Prelude.none»))))))
        («Tactics.byInsts» x5 x0 x1 x2 x3 x10)
        x4
        x6
        x7
        x8
        x9);
    x6

def «Tactics.condParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      («Language.mIs» (leaf 11) (leaf 3) x0)
      («Prelude.and»
        (Const.eq («Language.mD» x0 (leaf 0)) (leaf 6))
        (Const.eq
          («Prelude.length» (Const.children («Language.mD» x0 (leaf 1))))
          (leaf 1)))).label ≠ 0 then
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Theory.l4»
            («Prelude.at» (Const.children («Language.mD» x0 (leaf 1))) (leaf 0))
            («Language.mArg» x0 (leaf 2))
            («Language.mArg» x0 (leaf 1))
            («Language.mArg» x0 (leaf 0))))
    else
      «Prelude.none»);
    x1

def «Tactics.condVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «Base.bindO»
      («Tactics.condParts» x1)
      (fun (x2 : T) =>
        «Tactics.varUnless» x0 («Prelude.at» (Const.children x2) (leaf 1)));
    x2

def «Tactics.stuckVarC» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «Tactics.orO»
      («Tactics.findSomeT»
        («Tactics.condVar» x0)
        («Tactics.openSubterms» x1))
      («Tactics.stuckVar» x0 x1);
    x2

def «Tactics.isApps2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Language.mIs» (leaf 6) (leaf 2) x1)
      (let x2 : T := «Language.mArg» x1 (leaf 0);
       «Prelude.and»
         («Language.mIs» (leaf 6) (leaf 2) x2)
         (let x3 : T := «Language.mArg» x2 (leaf 0);
          «Prelude.and»
            (Const.eq (Const.label x3) (leaf 11))
            («Prelude.and»
              (Const.eq («Language.mD» x3 (leaf 0)) x0)
              (Const.equal
                («Language.mD» x3 (leaf 1))
                (Const.node (leaf 0) ([] : List T))))));
    x2

def «Tactics.appsOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («Tactics.isApps2» x0 x2).label ≠ 0 then (x2 :: x3) else x3)
      ([] : List T)
      («Tactics.openSubterms» x1);
    x2

def «Tactics.unnodeTy» :=
  «Theory.prod»
    «Translation.bitsTy»
    («Theory.list» «Translation.treeTy»)

def «Tactics.unnodeStep» :=
  let x0 : T := «Prelude.nth» «Translation.lib» (leaf 4);
  if («Prelude.isSome» x0).label ≠ 0 then
    Const.lcase
      (α := T)
      (β := T)
      («Language.mArgs» («Language.ldBody» («Prelude.get» x0)))
      «Language.mStar»
      (fun (x1 : T) (_ : List T) => x1)
  else
    «Language.mStar»

def «Tactics.unnodeU» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mRoseRec»
      «Tactics.unnodeTy»
      «Tactics.unnodeStep»
      x0;
    x1

def «Tactics.lenUF» :=
  fun (x0 : List (T → T)) =>
    let x1 : T := Const.foldr
      (α := T → T)
      (β := T)
      (fun (_ : T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Tactics.occStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T)) =>
    let x4 : T →
      T := (fun (x4 : T) =>
      let x5 : T := «Prover.dNode» (leaf 0) ([] : List T) ([] : List T);
      let x6 : T := Const.add x1 x4;
      let x7 : T := Const.label x2;
      if (Const.eq x7 (leaf 0)).label ≠ 0 then
        if (Const.eq («Language.mD» x2 (leaf 0)) x6).label ≠ 0 then
          «Prover.dNode»
            (leaf 1)
            ([] : List T)
            («Theory.l2»
              («Prover.dNode»
                (leaf 2)
                ([] : List T)
                («Prelude.single»
                  («Prover.dNode» (leaf 6) ([] : List T) ([] : List T))))
              («Prover.dNode»
                (leaf 16)
                («Theory.l4»
                  x0
                  (Const.node (leaf 0) ([] : List T))
                  (Const.node (leaf 0) («Prelude.single» («Language.mVar» x6)))
                  (leaf 0))
                ([] : List T)))
        else
          x5
      else
        if (Const.eq x7 (leaf 5)).label ≠ 0 then
          «Prover.dNode»
            (leaf 2)
            ([] : List T)
            (Const.foldr
              (α := T → T)
              (β := List T)
              (fun (x8 : T → T) (x9 : List T) =>
                ((x8 (Const.add x4 (leaf 1))) :: x9))
              ([] : List T)
              («Prover.ufTail» x3))
        else
          if («Prelude.or»
            (Const.eq x7 (leaf 8))
            (Const.eq x7 (leaf 9))).label ≠ 0 then
            «Prover.dNode»
              (leaf 2)
              ([] : List T)
              («Base.mapT»
                (fun (x8 : T) =>
                  if (Const.eq x8 (leaf 2)).label ≠ 0 then
                    «Prover.ufAt» x3 (Const.add x8 (leaf 1)) x4
                  else
                    x5)
                («Base.range» («Tactics.lenUF» («Prover.ufTail» x3))))
          else
            if (Const.eq x7 (leaf 10)).label ≠ 0 then
              «Prover.dNode»
                (leaf 2)
                ([] : List T)
                («Base.mapT»
                  (fun (x8 : T) =>
                    if (Const.eq x8 (leaf 1)).label ≠ 0 then
                      «Prover.ufAt» x3 (Const.add x8 (leaf 1)) x4
                    else
                      x5)
                  («Base.range» («Tactics.lenUF» («Prover.ufTail» x3))))
            else
              if («Base.allT»
                (fun (x8 : T) => Const.eq («Prover.uses» x8 x6) (leaf 0))
                («Language.mArgs» x2)).label ≠ 0 then
                x5
              else
                «Prover.dNode»
                  (leaf 2)
                  ([] : List T)
                  (Const.foldr
                    (α := T → T)
                    (β := List T)
                    (fun (x8 : T → T) (x9 : List T) => ((x8 x4) :: x9))
                    ([] : List T)
                    («Prover.ufTail» x3)));
    x4

def «Tactics.occRewrite» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := Const.para (α := T → T) («Tactics.occStep» x0 x1) x2 x3;
    x4

def «Tactics.byTreeSplit» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «Base.bindO»
        («Prelude.nth» x3 x1)
        (fun (x7 : T) =>
          if (Const.equal x7 «Translation.treeTy»).label ≠ 0 then
            let x8 : T := «Prover.abstractVar» x1 x7 x5;
            let x9 : T := «Prover.abstractVar» x1 x7 x6;
            let x10 : T := «Translation.nodeT»
              («Language.mPair»
                («Language.mVar» (leaf 1))
                («Language.mVar» (leaf 0)));
            let x11 : T := «Language.mApp» («Derivation.weaken2» x8) x10;
            let x12 : T := «Language.mApp» («Derivation.weaken2» x9) x10;
            «Base.mapO»
              (fun (x13 : T) =>
                let x14 : T := «Language.mLam»
                  «Translation.bitsTy»
                  («Language.mLam» («Theory.list» «Translation.treeTy») x11);
                let x15 : T := «Language.mLam»
                  «Translation.bitsTy»
                  («Language.mLam» («Theory.list» «Translation.treeTy») x12);
                let x16 : T := «Prover.dNode» (leaf 3) ([] : List T) ([] : List T);
                let x17 : T := «Prover.dNode» (leaf 0) ([] : List T) ([] : List T);
                let x18 : T := «Prover.dNode»
                  (leaf 2)
                  ([] : List T)
                  («Theory.l2» x16 x16);
                let x19 : T := «Prover.dNode»
                  (leaf 26)
                  ([] : List T)
                  («Prelude.single»
                    («Prover.dNode»
                      (leaf 23)
                      ([] : List T)
                      («Theory.l2»
                        x18
                        («Prover.dNode»
                          (leaf 26)
                          ([] : List T)
                          («Prelude.single»
                            («Prover.dNode» (leaf 23) ([] : List T) («Theory.l2» x18 x13)))))));
                let x20 : T := «Tactics.unnodeU» («Language.mVar» x1);
                let x21 : T →
                  T := (fun (x21 : T) =>
                  «Language.mApp»
                    («Language.mApp» x21 («Language.mFst» x20))
                    («Language.mSnd» x20));
                let x22 : T →
                  T := (fun (x22 : T) =>
                  «Prover.dNode»
                    (leaf 1)
                    ([] : List T)
                    («Theory.l2»
                      («Prover.dNode» (leaf 2) ([] : List T) («Theory.l2» x16 x17))
                      («Prover.dNode»
                        (leaf 1)
                        ([] : List T)
                        («Theory.l2»
                          x16
                          («Prover.dNode»
                            (leaf 1)
                            ([] : List T)
                            («Theory.l2» x16 («Tactics.occRewrite» x0 x1 x22 (leaf 0))))))));
                let x23 : T := «Prover.dNode»
                  (leaf 18)
                  ([] : List T)
                  («Theory.l2»
                    («Prover.dNode»
                      (leaf 2)
                      ([] : List T)
                      («Theory.l2»
                        («Prover.dNode»
                          (leaf 2)
                          ([] : List T)
                          («Theory.l2»
                            («Prover.dNode»
                              (leaf 17)
                              («Theory.l2» («Prelude.length» x4) (leaf 0))
                              ([] : List T))
                            x17))
                        x17))
                    x17);
                «Prover.dNode»
                  (leaf 22)
                  («Prelude.single» («Language.mEq» x14 x15))
                  («Theory.l2»
                    x19
                    («Prover.dNode»
                      (leaf 24)
                      («Prelude.single» («Language.mEq» (x21 x14) (x21 x15)))
                      («Theory.l2»
                        («Prover.dNode»
                          (leaf 2)
                          ([] : List T)
                          («Theory.l2» (x22 x5) (x22 x6)))
                        x23))))
              (x2
                ((«Theory.list» «Translation.treeTy») :: («Translation.bitsTy» :: x3))
                («Base.mapT» «Derivation.weaken2» x4)
                x11
                x12)
          else
            «Prelude.none»));
    x3

def «Tactics.splitStuck» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Base.bindO»
      («Prelude.nth» x5 x3)
      (fun (x9 : T) =>
        if («Prelude.isSome» («Language.listPart» x9)).label ≠ 0 then
          «Tactics.byListSplit» x0 x1 x3 x4 x4 x5 x6 x7 x8
        else
          if («Prelude.isSome» («Language.coprodParts» x9)).label ≠ 0 then
            «Tactics.bySplit2» (leaf 3) (leaf 4) x3 x4 x4 x5 x6 x7 x8
          else
            if (Const.equal x9 «Translation.treeTy»).label ≠ 0 then
              «Tactics.byTreeSplit» x2 x3 x4 x5 x6 x7 x8
            else
              «Prelude.none»);
    x9

def «Tactics.byAutoT» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T)
    (x6 : T) =>
    let x7 : List T →
      List T →
        T →
          T →
            T := (fun (x7 : List T) (x8 : List T) (x9 : T) (x10 : T) =>
      let x11 : T := «Prelude.length» x8;
      let x12 : List T →
        List T →
          T →
            T →
              T := (fun (x12 : List T) (x13 : List T) (x14 : T) (x15 : T) =>
        «Base.bindO»
          («Prover.eval» x0 x1 x2 x4 (leaf 4096) x6 x12 x13 x14)
          (fun (x16 : T) =>
            «Base.bindO»
              («Prover.eval» x0 x1 x2 x4 (leaf 4096) x6 x12 x13 x15)
              (fun (x17 : T) =>
                if (Const.equal
                  («Language.p1» x16)
                  («Language.p1» x17)).label ≠ 0 then
                  «Prelude.some»
                    («Prover.dNode»
                      (leaf 18)
                      ([] : List T)
                      («Theory.l2»
                        («Language.p1» («Language.p2» x16))
                        («Language.p1» («Language.p2» x17))))
                else
                  «Prelude.none»)));
      let x13 : List T →
        List T →
          T →
            T →
              T := (fun (x13 : List T) (x14 : List T) (x15 : T) (x16 : T) =>
        if (Const.eq x11 (leaf 0)).label ≠ 0 then
          «Prelude.none»
        else
          «Tactics.byInsts» x6 x0 x1 x2 x4 x11 x13 x14 x15 x16);
      Const.iter
        (α := List T → List T → T → T → T)
        (fun (x14 : List T → List T → T → T → T)
           (x15 : List T)
           (x16 : List T)
           (x17 : T)
           (x18 : T) =>
          «Base.bindO»
            («Prover.eval» x0 x1 x2 x4 (leaf 4096) x6 x15 x16 x17)
            (fun (x19 : T) =>
              «Base.bindO»
                («Prover.eval» x0 x1 x2 x4 (leaf 4096) x6 x15 x16 x18)
                (fun (x20 : T) =>
                  if (Const.equal
                    («Language.p1» x19)
                    («Language.p1» x20)).label ≠ 0 then
                    «Prelude.some»
                      («Prover.dNode»
                        (leaf 18)
                        ([] : List T)
                        («Theory.l2»
                          («Language.p1» («Language.p2» x19))
                          («Language.p1» («Language.p2» x20))))
                  else
                    «Tactics.orO»
                      (x13 x15 x16 x17 x18)
                      (let x21 : T →
                         T := (fun (x21 : T) =>
                         «Base.anyT»
                           (fun (x22 : T) => «Tactics.mentions» x22 x21)
                           («Base.take» x11 x16));
                       let x22 : T → T := (fun (_ : T) => leaf 0);
                       «Base.bindO»
                         («Tactics.orO»
                           («Tactics.orO»
                             («Tactics.stuckVar» x21 («Language.p1» x19))
                             («Tactics.stuckVar» x21 («Language.p1» x20)))
                           («Tactics.orO»
                             («Tactics.stuckVar» x22 («Language.p1» x19))
                             («Tactics.stuckVar» x22 («Language.p1» x20))))
                         (fun (x23 : T) =>
                           «Tactics.splitStuck» x0 x2 x3 x23 x14 x15 x16 x17 x18)))))
        (fun (x14 : List T) (x15 : List T) (x16 : T) (x17 : T) =>
          «Tactics.orO» (x12 x14 x15 x16 x17) (x13 x14 x15 x16 x17))
        x5
        x7
        x8
        x9
        x10);
    x7

def «Tactics.byAutoC» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := Const.iter
      (α := List T → List T → T → T → T)
      (fun (x6 : List T → List T → T → T → T)
         (x7 : List T)
         (x8 : List T)
         (x9 : T)
         (x10 : T) =>
        «Tactics.orO»
          («Tactics.byWeak» x0 x1 x2 x4 x7 x8 x9 x10)
          («Base.bindO»
            («Prover.eval» x0 x1 x2 x4 (leaf 4096) (leaf 1) x7 x8 x9)
            (fun (x11 : T) =>
              «Base.bindO»
                («Prover.eval» x0 x1 x2 x4 (leaf 4096) (leaf 1) x7 x8 x10)
                (fun (x12 : T) =>
                  let x13 : T → T := (fun (_ : T) => leaf 0);
                  «Base.bindO»
                    («Tactics.orO»
                      («Tactics.stuckVarC» x13 («Language.p1» x11))
                      («Tactics.stuckVarC» x13 («Language.p1» x12)))
                    (fun (x14 : T) =>
                      «Tactics.splitStuck» x0 x2 x3 x14 x6 x7 x8 x9 x10)))))
      («Tactics.byWeak» x0 x1 x2 x4)
      x5;
    x6

def «Tactics.absStep» :=
  fun (x0 : T) (x1 : T) (x2 : List (T → T)) =>
    let x3 : T →
      T := (fun (x3 : T) =>
      if (Const.equal
        x1
        («Language.rename»
          x0
          (fun (x4 : T) => Const.add x4 x3))).label ≠ 0 then
        «Language.mVar» x3
      else
        let x4 : T := Const.label x1;
        let x5 : List T := «Language.mArgs» x1;
        let x6 : List T →
          T := (fun (x6 : List T) =>
          Const.node x4 ((Const.child x1 (leaf 0)) :: x6));
        if (Const.eq x4 (leaf 5)).label ≠ 0 then
          x6
            (Const.foldr
              (α := T → T)
              (β := List T)
              (fun (x7 : T → T) (x8 : List T) =>
                ((x7 (Const.add x3 (leaf 1))) :: x8))
              ([] : List T)
              («Prover.ufTail» x2))
        else
          if («Prelude.or»
            (Const.eq x4 (leaf 8))
            (Const.eq x4 (leaf 9))).label ≠ 0 then
            x6
              («Base.mapT»
                (fun (x7 : T) =>
                  if (Const.eq x7 (leaf 2)).label ≠ 0 then
                    «Prover.ufAt» x2 (Const.add x7 (leaf 1)) x3
                  else
                    «Prelude.at» x5 x7)
                («Base.range» («Tactics.lenUF» («Prover.ufTail» x2))))
          else
            if (Const.eq x4 (leaf 10)).label ≠ 0 then
              x6
                («Base.mapT»
                  (fun (x7 : T) =>
                    if (Const.eq x7 (leaf 1)).label ≠ 0 then
                      «Prover.ufAt» x2 (Const.add x7 (leaf 1)) x3
                    else
                      «Prelude.at» x5 x7)
                  («Base.range» («Tactics.lenUF» («Prover.ufTail» x2))))
            else
              x6
                (Const.foldr
                  (α := T → T)
                  (β := List T)
                  (fun (x7 : T → T) (x8 : List T) => ((x7 x3) :: x8))
                  ([] : List T)
                  («Prover.ufTail» x2)));
    x3

def «Tactics.abstractTerm» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mLam»
      x0
      (Const.para
        (α := T → T)
        («Tactics.absStep» («Derivation.weaken1» x1))
        («Derivation.weaken1» x2)
        (leaf 0));
    x3

def «Tactics.maskRwD» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «Tactics.abstractTerm» x1 x6 x9;
                    let x11 : T := «Prover.dNode» (leaf 0) ([] : List T) ([] : List T);
                    let x12 : T := «Prover.dNode» (leaf 3) ([] : List T) ([] : List T);
                    let x13 : T := «Language.mEq»
                      («Translation.condT» x0 x4 («Language.mApp» x10 x6) x5)
                      («Translation.condT» x0 x4 («Language.mApp» x10 x7) x5);
                    let x14 : T := «Prover.dNode»
                      (leaf 18)
                      ([] : List T)
                      («Theory.l2»
                        («Prover.dNode»
                          (leaf 1)
                          ([] : List T)
                          («Theory.l2»
                            («Prover.dNode»
                              (leaf 16)
                              («Theory.l4»
                                x2
                                (Const.node (leaf 0) («Theory.l2» x0 x1))
                                (Const.node (leaf 0) («Theory.l5» x4 x5 x6 x8 x10))
                                (leaf 1))
                              ([] : List T))
                            («Prover.dNode»
                              (leaf 1)
                              ([] : List T)
                              («Theory.l2»
                                («Prover.dNode»
                                  (leaf 2)
                                  ([] : List T)
                                  («Theory.l3»
                                    x11
                                    («Prover.dNode» (leaf 2) ([] : List T) («Theory.l2» x11 x3))
                                    x11))
                                («Prover.dNode»
                                  (leaf 16)
                                  («Theory.l4»
                                    x2
                                    (Const.node (leaf 0) («Theory.l2» x0 x1))
                                    (Const.node (leaf 0) («Theory.l5» x4 x5 x7 x8 x10))
                                    (leaf 0))
                                  ([] : List T))))))
                        x11);
                    «Prover.dNode»
                      (leaf 24)
                      («Prelude.single» x13)
                      («Theory.l2»
                        («Prover.dNode»
                          (leaf 2)
                          ([] : List T)
                          («Theory.l2»
                            («Prover.dNode» (leaf 2) ([] : List T) («Theory.l3» x11 x12 x11))
                            («Prover.dNode» (leaf 2) ([] : List T) («Theory.l3» x11 x12 x11))))
                        x14));
    x10

def «Tactics.maskRw» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : T)
    (x8 : T)
    (x9 : T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := «Tactics.maskRwD»
      x0
      x1
      x2
      («Prover.dNode»
        (leaf 16)
        («Theory.l4»
          x3
          (Const.node (leaf 0) x4)
          (Const.node (leaf 0) x5)
          (leaf 0))
        ([] : List T))
      x6
      x7
      x8
      x9
      x10
      x11;
    x12

def «Tactics.maskAt» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Base.bindO»
      («Base.bindO» («Prelude.nth» x2 x8) «Derivation.eqParts»)
      (fun (x9 : T) =>
        let x10 : T := «Language.p1» x9;
        let x11 : T := «Language.p2» x9;
        «Base.bindO»
          («Tactics.condParts» x10)
          (fun (x12 : T) =>
            let x13 : T := «Prelude.at» (Const.children x12) (leaf 0);
            let x14 : T := «Prelude.at» (Const.children x12) (leaf 2);
            let x15 : T := «Prelude.at» (Const.children x12) (leaf 3);
            if («Base.not»
              (Const.equal
                («Prelude.at» (Const.children x12) (leaf 1))
                x4)).label ≠ 0 then
              «Prelude.none»
            else
              «Base.bindO»
                (let x16 : T := «Tactics.condParts» x11;
                 if («Prelude.isSome» x16).label ≠ 0 then
                   let x17 : T := «Prelude.get» x16;
                   if («Prelude.and»
                     (Const.equal («Prelude.at» (Const.children x17) (leaf 1)) x4)
                     (Const.equal
                       («Prelude.at» (Const.children x17) (leaf 3))
                       x15)).label ≠ 0 then
                     «Prelude.some»
                       («Language.pr»
                         («Prelude.at» (Const.children x17) (leaf 2))
                         («Prover.dNode» (leaf 17) («Theory.l2» x8 (leaf 0)) ([] : List T)))
                   else
                     «Prelude.none»
                 else
                   if (Const.equal x11 x15).label ≠ 0 then
                     «Prelude.some»
                       («Language.pr»
                         x11
                         («Prover.dNode»
                           (leaf 1)
                           ([] : List T)
                           («Theory.l2»
                             («Prover.dNode» (leaf 17) («Theory.l2» x8 (leaf 0)) ([] : List T))
                             («Prover.dNode»
                               (leaf 16)
                               («Theory.l4»
                                 x1
                                 (Const.node (leaf 0) («Prelude.single» x13))
                                 (Const.node (leaf 0) («Theory.l2» x4 x11))
                                 (leaf 1))
                               ([] : List T)))))
                   else
                     «Prelude.none»)
                (fun (x16 : T) =>
                  let x17 : T := «Language.p1» x16;
                  if (Const.equal x14 x17).label ≠ 0 then
                    «Prelude.none»
                  else
                    let x18 : T := «Tactics.abstractTerm» x13 x14 x5;
                    «Base.bindO»
                      (Const.lcase
                        (α := T)
                        (β := T)
                        («Language.mArgs» x18)
                        «Prelude.none»
                        (fun (x19 : T) (_ : List T) => «Prelude.some» x19))
                      (fun (x19 : T) =>
                        if (Const.eq («Prover.uses» x19 (leaf 0)) (leaf 0)).label ≠ 0 then
                          «Prelude.none»
                        else
                          «Prelude.some»
                            (Const.node
                              (leaf 0)
                              («Theory.l3»
                                x7
                                («Translation.condT»
                                  x3
                                  x4
                                  («Language.subst» x19 («Derivation.instVar» x17))
                                  x6)
                                («Tactics.maskRwD»
                                  x3
                                  x13
                                  x0
                                  («Language.p2» x16)
                                  x4
                                  x6
                                  x14
                                  x17
                                  x15
                                  x5)))))));
    x9

def «Tactics.maskSub» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := «Tactics.findSomeT»
      (fun (x4 : T) =>
        «Base.bindO»
          («Tactics.condParts» x4)
          (fun (x5 : T) =>
            «Tactics.findSomeT»
              («Tactics.maskAt»
                x0
                x1
                x2
                («Prelude.at» (Const.children x5) (leaf 0))
                («Prelude.at» (Const.children x5) (leaf 1))
                («Prelude.at» (Const.children x5) (leaf 2))
                («Prelude.at» (Const.children x5) (leaf 3))
                x4)
              («Prelude.reverse» («Base.range» («Prelude.length» x2)))))
      («Tactics.openSubterms» x3);
    x4

def «Tactics.byMaskSubs» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List (T × (T → T → List T → T)))
    (x5 : T) =>
    let x6 : (List (T × (T → T → List T → T)) →
      List T → List T → T → T → T) →
      List T →
        List T →
          T →
            T →
              T := Const.iter
      (α := List (T × (T → T → List T → T)) →
        (List (T × (T → T → List T → T)) → List T → List T → T → T → T) →
          List T → List T → T → T → T)
      (fun (x6 : List (T × (T → T → List T → T)) →
           (List (T × (T → T → List T → T)) → List T → List T → T → T → T) →
             List T → List T → T → T → T)
         (x7 : List (T × (T → T → List T → T)))
         (x8 : List (T × (T → T → List T → T)) →
           List T → List T → T → T → T) =>
        «Tactics.byNF»
          x0
          x1
          (leaf 0)
          («Tactics.appendNR» x7 x4)
          (leaf 1)
          (fun (x9 : List T) (x10 : List T) (x11 : T) (x12 : T) =>
            let x13 : T := «Tactics.orO»
              («Tactics.maskSub» x2 x3 x10 x11)
              («Tactics.maskSub» x2 x3 x10 x12);
            if («Prelude.isSome» x13).label ≠ 0 then
              let x14 : T := «Prelude.at»
                (Const.children («Prelude.get» x13))
                (leaf 0);
              let x15 : T := «Prelude.at»
                (Const.children («Prelude.get» x13))
                (leaf 1);
              «Base.mapO»
                (fun (x16 : T) =>
                  «Prover.dNode»
                    (leaf 22)
                    («Prelude.single» («Language.mEq» x14 x15))
                    («Theory.l2»
                      («Prelude.at» (Const.children («Prelude.get» x13)) (leaf 2))
                      x16))
                (x6
                  ((«Tactics.hypRule» («Prelude.length» x10)) :: x7)
                  x8
                  x9
                  («Prelude.append» x10 («Prelude.single» («Language.mEq» x14 x15)))
                  x11
                  x12)
            else
              x8 x7 x9 x10 x11 x12))
      (fun (x6 : List (T × (T → T → List T → T)))
         (x7 : List (T × (T → T → List T → T)) →
           List T → List T → T → T → T) =>
        x7 x6)
      x5
      ([] : List (T × (T → T → List T → T)));
    x6

def «Tactics.byGeneralize» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      let x7 : T := «Tactics.abstractTerm» x0 x1 x5;
      let x8 : T := «Tactics.abstractTerm» x0 x1 x6;
      «Base.mapO»
        (fun (x9 : T) =>
          «Tactics.applyAbs»
            x1
            («Prelude.length» x4)
            x7
            x8
            («Prover.dNode» (leaf 26) ([] : List T) («Prelude.single» x9)))
        (x2
          (x0 :: x3)
          («Base.mapT» «Derivation.weaken1» x4)
          («Language.mApp» («Derivation.weaken1» x7) («Language.mVar» (leaf 0)))
          («Language.mApp»
            («Derivation.weaken1» x8)
            («Language.mVar» (leaf 0)))));
    x3

end GebMirror.Metalogic

end
