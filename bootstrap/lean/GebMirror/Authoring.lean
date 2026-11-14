module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Logic/LF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Logic/LF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Logic/LF.l2» x1 x2)); x3

def «Logic/LF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Logic/LF.l3» x1 x2 x3)); x4

def «Logic/LF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Logic/LF.l4» x1 x2 x3 x4)); x5

def «Logic/LF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Logic/LF.l5» x1 x2 x3 x4 x5)); x6

def «Logic/DF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Logic/DF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Logic/DF.l2» x1 x2)); x3

def «Logic/DF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Logic/DF.l3» x1 x2 x3)); x4

def «Logic/DF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Logic/DF.l4» x1 x2 x3 x4)); x5

def «Logic/DF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Logic/DF.l5» x1 x2 x3 x4 x5)); x6

def «Logic/LD.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Logic/LD.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Logic/LD.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Logic/LD.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Logic/LD.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Logic/LD.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Logic/LD.tail» x1 x0; x2

def «Logic/LD.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Logic/LD.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Logic/Decls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Logic/Decls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Logic/Decls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Logic/Decls.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Logic/Decls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Logic/Decls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Logic/Decls.tail» x1 x0;
    x2

def «Logic/Decls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Logic/Decls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Logic.conjL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 1))
      ([] : List T)
      («Theory.l2» x2 x1);
    x3

def «Logic.connectives» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := «Language.objs»
              («Theory.l2» «Theory.omega» «Theory.omega»);
            «Logic/LF.l3»
              («Language.ldefn»
                (leaf 0)
                («Language.objs» ([] : List T))
                «Theory.omega»
                («Language.mEq» «Language.mStar» «Language.mStar»))
              («Language.ldefn»
                (leaf 0)
                x1
                «Theory.omega»
                («Language.mEq»
                  («Language.mPair» («Language.var» (leaf 1)) («Language.var» (leaf 0)))
                  («Language.mPair» («Tactics.ttL» x0) («Tactics.ttL» x0))))
              («Language.ldefn»
                (leaf 0)
                x1
                «Theory.omega»
                («Language.mEq»
                  («Logic.conjL» x0 («Language.var» (leaf 1)) («Language.var» (leaf 0)))
                  («Language.var» (leaf 1)))));
    x1

def «Logic.eqTrueI» :=
  fun (x0 : T) =>
    let x1 : T := «Prover.dNode»
      (leaf 25)
      ([] : List T)
      («Theory.l2»
        «Tactics.trueI»
        («Prover.dNode» (leaf 21) («Prelude.single» x0) ([] : List T)));
    x1

def «Logic.unfoldHyp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prover.dNode»
      (leaf 24)
      («Prelude.single» x0)
      («Theory.l2»
        («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
        («Prover.dNode» (leaf 21) («Prelude.single» x1) ([] : List T)));
    x2

def «Logic.rwHyp» :=
  fun (x0 : T) =>
    let x1 : T := «Prover.dNode»
      (leaf 17)
      («Theory.l2» x0 (leaf 0))
      ([] : List T);
    x1

def «Logic.conjE» :=
  fun (x0 : T) (x1 : T → T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Logic.conjL»
                     x0
                     («Language.var» (leaf 1))
                     («Language.var» (leaf 0));
                   let x5 : T := «Language.mEq»
                     («Language.mPair» («Language.var» (leaf 1)) («Language.var» (leaf 0)))
                     («Language.mPair» («Tactics.ttL» x0) («Tactics.ttL» x0));
                   let x6 : T := «Prover.dNode» x2 ([] : List T) ([] : List T);
                   «Derivation.declLang»
                     («Derivation.mkThm»
                       (leaf 0)
                       («Language.objs» («Theory.l2» «Theory.omega» «Theory.omega»))
                       («Derivation.terms» («Prelude.single» x4))
                       («Language.var» x3))
                     («Prover.dNode»
                       (leaf 22)
                       («Prelude.single» x5)
                       («Theory.l2»
                         («Logic.unfoldHyp» x4 (leaf 0))
                         («Prover.dNode»
                           (leaf 24)
                           («Prelude.single»
                             (x1
                               («Language.mPair»
                                 («Language.var» (leaf 1))
                                 («Language.var» (leaf 0)))))
                           («Theory.l2»
                             x6
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
                                       («Prelude.single» («Logic.rwHyp» (leaf 1))))
                                     x6))
                                 «Tactics.trueI»)))))));
    x4

def «Logic.connectiveRules» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : T := «Language.objs»
              («Theory.l2» «Theory.omega» «Theory.omega»);
            let x3 : T := «Tactics.ttL» x0;
            let x4 : T := «Logic.conjL»
              x0
              («Language.var» (leaf 1))
              («Language.var» (leaf 0));
            let x5 : T := «Prover.dNode» (leaf 0) ([] : List T) ([] : List T);
            «Logic/DF.l5»
              («Derivation.declLang»
                («Derivation.mkThm»
                  (leaf 0)
                  («Language.objs» ([] : List T))
                  («Derivation.terms» ([] : List T))
                  x3)
                «Tactics.trueI»)
              («Derivation.declLang»
                («Derivation.mkThm»
                  (leaf 0)
                  x2
                  («Derivation.terms»
                    («Theory.l2» («Language.var» (leaf 1)) («Language.var» (leaf 0))))
                  x4)
                («Prover.dNode»
                  (leaf 23)
                  ([] : List T)
                  («Theory.l2»
                    («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
                    («Prover.dNode»
                      (leaf 22)
                      («Prelude.single» («Language.mEq» («Language.var» (leaf 1)) x3))
                      («Theory.l2»
                        («Logic.eqTrueI» (leaf 0))
                        («Prover.dNode»
                          (leaf 22)
                          («Prelude.single» («Language.mEq» («Language.var» (leaf 0)) x3))
                          («Theory.l2»
                            («Logic.eqTrueI» (leaf 1))
                            («Prover.dNode»
                              (leaf 18)
                              ([] : List T)
                              («Theory.l2»
                                («Prover.dNode»
                                  (leaf 2)
                                  ([] : List T)
                                  («Theory.l2» («Logic.rwHyp» (leaf 2)) («Logic.rwHyp» (leaf 3))))
                                x5)))))))))
              («Logic.conjE» x0 «Language.mFst» (leaf 4) (leaf 1))
              («Logic.conjE» x0 «Language.mSnd» (leaf 5) (leaf 0))
              («Derivation.declLang»
                («Derivation.mkThm»
                  (leaf 0)
                  x2
                  («Derivation.terms»
                    («Theory.l2»
                      («Tactics.impL»
                        x0
                        («Language.var» (leaf 1))
                        («Language.var» (leaf 0)))
                      («Language.var» (leaf 1))))
                  («Language.var» (leaf 0)))
                («Prover.dNode»
                  (leaf 22)
                  («Prelude.single» («Language.mEq» x4 («Language.var» (leaf 1))))
                  («Theory.l2»
                    («Logic.unfoldHyp»
                      («Tactics.impL»
                        x0
                        («Language.var» (leaf 1))
                        («Language.var» (leaf 0)))
                      (leaf 0))
                    («Prover.dNode»
                      (leaf 22)
                      («Prelude.single» («Language.mEq» («Language.var» (leaf 1)) x3))
                      («Theory.l2»
                        («Logic.eqTrueI» (leaf 1))
                        («Prover.dNode»
                          (leaf 27)
                          («Theory.l3»
                            (Const.add x1 (leaf 3))
                            (Const.node (leaf 0) ([] : List T))
                            (Const.node
                              (leaf 0)
                              («Theory.l2» («Language.var» (leaf 0)) («Language.var» (leaf 1)))))
                          («Prelude.single»
                            («Prover.dNode»
                              (leaf 23)
                              ([] : List T)
                              («Theory.l2»
                                («Prover.dNode»
                                  (leaf 1)
                                  ([] : List T)
                                  («Theory.l2» («Logic.rwHyp» (leaf 2)) («Logic.rwHyp» (leaf 3))))
                                «Tactics.trueI»))))))))));
    x2

def «Logic.allL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 3))
      («Prelude.single» x1)
      («Prelude.single» x2);
    x3

def «Logic.ffL» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mDefn»
      (Const.add x0 (leaf 4))
      ([] : List T)
      ([] : List T);
    x1

def «Logic.negL» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mDefn»
      (Const.add x0 (leaf 5))
      ([] : List T)
      («Prelude.single» x1);
    x2

def «Logic.disjL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 6))
      ([] : List T)
      («Theory.l2» x2 x1);
    x3

def «Logic.exL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 7))
      («Prelude.single» x1)
      («Prelude.single» x2);
    x3

def «Logic.exuL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 8))
      («Prelude.single» x1)
      («Prelude.single» x2);
    x3

def «Logic.connectivesAll» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := «Language.objs»
              («Theory.l2» «Theory.omega» «Theory.omega»);
            let x2 : T := «Language.objs»
              («Prelude.single»
                («Theory.exp» («Theory.x» (leaf 0)) «Theory.omega»));
            let x3 : T → T → T := «Tactics.impL» x0;
            «Logic/LD.append»
              («Logic.connectives» x0)
              («Logic/LF.l6»
                («Language.ldefn»
                  (leaf 1)
                  x2
                  «Theory.omega»
                  («Language.mEq»
                    («Language.var» (leaf 0))
                    («Language.mLam» («Theory.x» (leaf 0)) («Tactics.ttL» x0))))
                («Language.ldefn»
                  (leaf 0)
                  («Language.objs» ([] : List T))
                  «Theory.omega»
                  («Logic.allL»
                    x0
                    «Theory.omega»
                    («Language.mLam» «Theory.omega» («Language.var» (leaf 0)))))
                («Language.ldefn»
                  (leaf 0)
                  («Language.objs» («Prelude.single» «Theory.omega»))
                  «Theory.omega»
                  (x3 («Language.var» (leaf 0)) («Logic.ffL» x0)))
                («Language.ldefn»
                  (leaf 0)
                  x1
                  «Theory.omega»
                  («Logic.allL»
                    x0
                    «Theory.omega»
                    («Language.mLam»
                      «Theory.omega»
                      (x3
                        («Logic.conjL»
                          x0
                          (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0)))
                          (x3 («Language.var» (leaf 1)) («Language.var» (leaf 0))))
                        («Language.var» (leaf 0))))))
                («Language.ldefn»
                  (leaf 1)
                  x2
                  «Theory.omega»
                  («Logic.allL»
                    x0
                    «Theory.omega»
                    («Language.mLam»
                      «Theory.omega»
                      (x3
                        («Logic.allL»
                          x0
                          («Theory.x» (leaf 0))
                          («Language.mLam»
                            («Theory.x» (leaf 0))
                            (x3
                              («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 0)))
                              («Language.var» (leaf 1)))))
                        («Language.var» (leaf 0))))))
                («Language.ldefn»
                  (leaf 1)
                  x2
                  «Theory.omega»
                  («Logic.conjL»
                    x0
                    («Logic.exL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 0)))
                    («Logic.allL»
                      x0
                      («Theory.x» (leaf 0))
                      («Language.mLam»
                        («Theory.x» (leaf 0))
                        («Logic.allL»
                          x0
                          («Theory.x» (leaf 0))
                          («Language.mLam»
                            («Theory.x» (leaf 0))
                            (x3
                              («Logic.conjL»
                                x0
                                («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 1)))
                                («Language.app»
                                  («Language.var» (leaf 2))
                                  («Language.var» (leaf 0))))
                              («Language.mEq»
                                («Language.var» (leaf 1))
                                («Language.var» (leaf 0))))))))))));
    x1

def «Logic.dDelta» :=
  «Prover.dNode» (leaf 8) ([] : List T) ([] : List T)

def «Logic.dBeta» :=
  «Prover.dNode» (leaf 3) ([] : List T) ([] : List T)

def «Logic.dConv» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prover.dNode»
      (leaf 23)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Logic.dCut» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prover.dNode»
      (leaf 22)
      («Prelude.single» x0)
      («Theory.l2» x1 x2);
    x3

def «Logic.dConvFrom» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prover.dNode»
      (leaf 24)
      («Prelude.single» x0)
      («Theory.l2» x1 x2);
    x3

def «Logic.dApply» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prover.dNode»
      (leaf 27)
      («Theory.l3» x0 (Const.node (leaf 0) x1) (Const.node (leaf 0) x2))
      x3;
    x4

def «Logic.dHyp» :=
  fun (x0 : T) =>
    let x1 : T := «Prover.dNode»
      (leaf 21)
      («Prelude.single» x0)
      ([] : List T);
    x1

def «Logic.impIntro» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Logic.dConv»
      «Logic.dDelta»
      («Prover.dNode»
        (leaf 25)
        ([] : List T)
        («Theory.l2»
          («Logic.dApply»
            (Const.add x0 (leaf 2))
            ([] : List T)
            («Theory.l2» x3 x2)
            («Prelude.single» («Logic.dHyp» x1)))
          («Logic.dApply»
            (Const.add x0 (leaf 1))
            ([] : List T)
            («Theory.l2» x3 x2)
            («Theory.l2» («Logic.dHyp» x1) x4))));
    x5

def «Logic.allI» :=
  fun (x0 : T) =>
    let x1 : T := «Logic.dConv»
      «Logic.dDelta»
      («Prover.dNode»
        (leaf 26)
        ([] : List T)
        («Prelude.single»
          («Logic.dConv»
            («Prover.dNode»
              (leaf 2)
              ([] : List T)
              («Theory.l2» «Logic.dBeta» «Logic.dBeta»))
            («Prover.dNode»
              (leaf 25)
              ([] : List T)
              («Theory.l2» «Tactics.trueI» x0)))));
    x1

def «Logic.connectiveRulesAll» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : T := «Language.objs»
              («Theory.l2» «Theory.omega» «Theory.omega»);
            let x3 : T → T → T := «Tactics.impL» x0;
            let x4 : T := «Theory.exp» («Theory.x» (leaf 0)) «Theory.omega»;
            let x5 : List T := ([] : List T);
            let x6 : T := «Logic.conjL»
              x0
              (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0)))
              (x3 («Language.var» (leaf 1)) («Language.var» (leaf 0)));
            let x7 : T := x3
              («Logic.conjL»
                x0
                (x3 («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0))))
              («Language.var» (leaf 0));
            let x8 : T := «Language.mLam»
              («Theory.x» (leaf 0))
              (x3
                («Language.app» («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                («Language.var» (leaf 1)));
            let x9 : T := «Logic.allL»
              x0
              («Theory.x» (leaf 0))
              («Language.mLam»
                («Theory.x» (leaf 0))
                (x3
                  («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 0)))
                  («Language.var» (leaf 1))));
            let x10 : T := «Language.mLam»
              «Theory.omega»
              (x3
                («Logic.allL»
                  x0
                  («Theory.x» (leaf 0))
                  («Language.mLam»
                    («Theory.x» (leaf 0))
                    (x3
                      («Language.app» («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                      («Language.var» (leaf 1)))))
                («Language.var» (leaf 0)));
            let x11 : T →
              T →
                T := (fun (x11 : T) (x12 : T) =>
              «Logic.dConv»
                «Logic.dDelta»
                («Logic.allI»
                  («Logic.impIntro»
                    x1
                    (leaf 2)
                    x6
                    («Language.var» (leaf 0))
                    («Logic.dApply»
                      (Const.add x1 (leaf 4))
                      x5
                      («Theory.l2» («Language.var» (leaf 0)) x11)
                      («Theory.l2»
                        («Logic.dApply»
                          (Const.add x1 x12)
                          x5
                          («Theory.l2»
                            (x3 («Language.var» (leaf 1)) («Language.var» (leaf 0)))
                            (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0))))
                          («Prelude.single» («Logic.dHyp» (leaf 2))))
                        («Logic.dHyp» (leaf 0)))))));
            «Logic/Decls.append»
              («Logic.connectiveRules» x0 x1)
              («Logic/Decls.append»
                («Logic/DF.l4»
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 1)
                      («Language.objs» («Theory.l2» («Theory.x» (leaf 0)) x4))
                      («Derivation.terms»
                        («Prelude.single»
                          («Logic.allL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 1)))))
                      («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0))))
                    («Logic.dCut»
                      («Language.mEq»
                        («Language.var» (leaf 1))
                        («Language.mLam» («Theory.x» (leaf 0)) («Tactics.ttL» x0)))
                      («Logic.unfoldHyp»
                        («Logic.allL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 1)))
                        (leaf 0))
                      («Logic.dConv»
                        («Prover.dNode»
                          (leaf 1)
                          ([] : List T)
                          («Theory.l2»
                            («Prover.dNode»
                              (leaf 2)
                              ([] : List T)
                              («Theory.l2»
                                («Logic.rwHyp» (leaf 1))
                                («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                            «Logic.dBeta»))
                        «Tactics.trueI»)))
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 0)
                      («Language.objs» («Prelude.single» «Theory.omega»))
                      («Derivation.terms» («Prelude.single» («Logic.ffL» x0)))
                      («Language.var» (leaf 0)))
                    («Logic.dConvFrom»
                      («Language.app»
                        («Language.mLam» «Theory.omega» («Language.var» (leaf 0)))
                        («Language.var» (leaf 0)))
                      «Logic.dBeta»
                      («Logic.dApply»
                        (Const.add x1 (leaf 5))
                        («Prelude.single» «Theory.omega»)
                        («Theory.l2»
                          («Language.var» (leaf 0))
                          («Language.mLam» «Theory.omega» («Language.var» (leaf 0))))
                        («Prelude.single» («Logic.unfoldHyp» («Logic.ffL» x0) (leaf 0))))))
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 0)
                      x2
                      («Derivation.terms» («Prelude.single» («Language.var» (leaf 1))))
                      («Logic.disjL»
                        x0
                        («Language.var» (leaf 1))
                        («Language.var» (leaf 0))))
                    (x11 («Language.var» (leaf 2)) (leaf 2)))
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 0)
                      x2
                      («Derivation.terms» («Prelude.single» («Language.var» (leaf 0))))
                      («Logic.disjL»
                        x0
                        («Language.var» (leaf 1))
                        («Language.var» (leaf 0))))
                    (x11 («Language.var» (leaf 1)) (leaf 3))))
                («Logic/DF.l3»
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 0)
                      («Language.objs»
                        («Theory.l3» «Theory.omega» «Theory.omega» «Theory.omega»))
                      («Derivation.terms»
                        («Theory.l3»
                          («Logic.disjL» x0 («Language.var» (leaf 2)) («Language.var» (leaf 1)))
                          (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0)))
                          (x3 («Language.var» (leaf 1)) («Language.var» (leaf 0)))))
                      («Language.var» (leaf 0)))
                    («Logic.dCut»
                      (x3 x6 («Language.var» (leaf 0)))
                      («Logic.dConvFrom»
                        («Language.app»
                          («Language.mLam» «Theory.omega» x7)
                          («Language.var» (leaf 0)))
                        «Logic.dBeta»
                        («Logic.dApply»
                          (Const.add x1 (leaf 5))
                          («Prelude.single» «Theory.omega»)
                          («Theory.l2»
                            («Language.var» (leaf 0))
                            («Language.mLam» «Theory.omega» x7))
                          («Prelude.single»
                            («Logic.unfoldHyp»
                              («Logic.disjL» x0 («Language.var» (leaf 2)) («Language.var» (leaf 1)))
                              (leaf 0)))))
                      («Logic.dApply»
                        (Const.add x1 (leaf 4))
                        x5
                        («Theory.l2» («Language.var» (leaf 0)) x6)
                        («Theory.l2»
                          («Logic.dHyp» (leaf 3))
                          («Logic.dApply»
                            (Const.add x1 (leaf 1))
                            x5
                            («Theory.l2»
                              (x3 («Language.var» (leaf 1)) («Language.var» (leaf 0)))
                              (x3 («Language.var» (leaf 2)) («Language.var» (leaf 0))))
                            («Theory.l2» («Logic.dHyp» (leaf 1)) («Logic.dHyp» (leaf 2))))))))
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 1)
                      («Language.objs» («Theory.l2» («Theory.x» (leaf 0)) x4))
                      («Derivation.terms»
                        («Prelude.single»
                          («Language.app» («Language.var» (leaf 1)) («Language.var» (leaf 0)))))
                      («Logic.exL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 1))))
                    («Logic.dConv»
                      «Logic.dDelta»
                      («Logic.allI»
                        («Logic.impIntro»
                          x1
                          (leaf 2)
                          («Logic.allL»
                            x0
                            («Theory.x» (leaf 0))
                            («Language.mLam»
                              («Theory.x» (leaf 0))
                              (x3
                                («Language.app» («Language.var» (leaf 3)) («Language.var» (leaf 0)))
                                («Language.var» (leaf 1)))))
                          («Language.var» (leaf 0))
                          («Logic.dApply»
                            (Const.add x1 (leaf 4))
                            x5
                            («Theory.l2»
                              («Language.var» (leaf 0))
                              («Language.app» («Language.var» (leaf 2)) («Language.var» (leaf 1))))
                            («Theory.l2»
                              («Logic.dConvFrom»
                                («Language.app» x8 («Language.var» (leaf 1)))
                                «Logic.dBeta»
                                («Logic.dApply»
                                  (Const.add x1 (leaf 5))
                                  («Prelude.single» («Theory.x» (leaf 0)))
                                  («Theory.l2» («Language.var» (leaf 1)) x8)
                                  («Prelude.single» («Logic.dHyp» (leaf 2)))))
                              («Logic.dHyp» (leaf 0))))))))
                  («Derivation.declLang»
                    («Derivation.mkThm»
                      (leaf 1)
                      («Language.objs» («Theory.l2» «Theory.omega» x4))
                      («Derivation.terms»
                        («Theory.l2»
                          («Logic.exL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 1)))
                          x9))
                      («Language.var» (leaf 0)))
                    («Logic.dCut»
                      (x3 x9 («Language.var» (leaf 0)))
                      («Logic.dConvFrom»
                        («Language.app» x10 («Language.var» (leaf 0)))
                        «Logic.dBeta»
                        («Logic.dApply»
                          (Const.add x1 (leaf 5))
                          («Prelude.single» «Theory.omega»)
                          («Theory.l2» («Language.var» (leaf 0)) x10)
                          («Prelude.single»
                            («Logic.unfoldHyp»
                              («Logic.exL» x0 («Theory.x» (leaf 0)) («Language.var» (leaf 1)))
                              (leaf 0)))))
                      («Logic.dApply»
                        (Const.add x1 (leaf 4))
                        x5
                        («Theory.l2» («Language.var» (leaf 0)) x9)
                        («Theory.l2» («Logic.dHyp» (leaf 2)) («Logic.dHyp» (leaf 1)))))))));
    x2

def «Formula.conj» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mDefn»
      (Const.add x0 (leaf 1))
      ([] : List T)
      («Theory.l2» x2 x1);
    x3

def «Formula.prove» :=
  fun (x0 : T) (x1 : List T → List T → T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T := (fun (x2 : List T) (x3 : List T) (x4 : T) =>
      let x5 : T := «Derivation.eqParts» x4;
      if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
        let x6 : List T := Const.children x5;
        let x7 : T := Const.lcase
          (α := T)
          (β := T)
          x6
          (leaf 0)
          (fun (x7 : T) (_ : List T) => x7);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x6
          ([] : List T)
          (fun (_ : T) (x9 : List T) => x9);
        x1 x2 x3 («Language.p1» x7) («Language.p2» x7)
      else
        let _ : List T := Const.children x5;
        «Base.mapO»
          (fun (x7 : T) =>
            «Prover.dNode»
              (leaf 22)
              («Prelude.single» («Language.mEq» x4 («Tactics.ttL» x0)))
              («Theory.l2»
                x7
                («Prover.dNode»
                  (leaf 23)
                  ([] : List T)
                  («Theory.l2»
                    («Prover.dNode»
                      (leaf 17)
                      («Theory.l2» («Prelude.length» x3) (leaf 0))
                      ([] : List T))
                    «Tactics.trueI»))))
          (x1 x2 x3 x4 («Tactics.ttL» x0)));
    x2

def «Formula.equate» :=
  fun (x0 : T) (x1 : List T → List T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T →
            T := (fun (x2 : List T) (x3 : List T) (x4 : T) (x5 : T) =>
      if (Const.equal x5 («Tactics.ttL» x0)).label ≠ 0 then
        «Base.mapO»
          (fun (x6 : T) =>
            «Prover.dNode»
              (leaf 25)
              ([] : List T)
              («Theory.l2» «Tactics.trueI» x6))
          (x1 x2 («Prelude.append» x3 («Prelude.single» («Tactics.ttL» x0))) x4)
      else
        «Base.mapO»
          (fun (x6 : T) =>
            «Prover.dNode»
              (leaf 22)
              («Prelude.single» («Tactics.ttL» x0))
              («Theory.l2» «Tactics.trueI» x6))
          (x1
            x2
            («Prelude.append» x3 («Prelude.single» («Tactics.ttL» x0)))
            («Language.mEq» x4 x5)));
    x2

def «Formula.equateExact» :=
  fun (x0 : T) (x1 : List T → List T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T →
            T := (fun (x2 : List T) (x3 : List T) (x4 : T) (x5 : T) =>
      let x6 : List
        T := «Prelude.append» x3 («Prelude.single» («Tactics.ttL» x0));
      let x7 : T := x1 x2 x6 («Language.mEq» x4 x5);
      if («Prelude.isSome» x7).label ≠ 0 then
        «Base.mapO»
          (fun (x8 : T) =>
            «Prover.dNode»
              (leaf 22)
              («Prelude.single» («Tactics.ttL» x0))
              («Theory.l2» «Tactics.trueI» x8))
          x7
      else
        if (Const.equal x5 («Tactics.ttL» x0)).label ≠ 0 then
          «Base.mapO»
            (fun (x8 : T) =>
              «Prover.dNode»
                (leaf 25)
                ([] : List T)
                («Theory.l2» «Tactics.trueI» x8))
            (x1 x2 x6 x4)
        else
          «Prelude.none»);
    x2

def «Formula.truth» :=
  fun (x0 : T) =>
    let x1 : List T →
      List T →
        T →
          T := (fun (_ : List T) (_ : List T) (x3 : T) =>
      if (Const.equal x3 («Tactics.ttL» x0)).label ≠ 0 then
        «Prelude.some» «Tactics.trueI»
      else
        «Prelude.none»);
    x1

def «Formula.hypothesis» :=
  fun (x0 : T) =>
    let x1 : List T →
      List T →
        T →
          T := (fun (_ : List T) (x2 : List T) (x3 : T) =>
      if («Prelude.and»
        (Const.lt x0 («Prelude.length» x2))
        (Const.equal («Prelude.at» x2 x0) x3)).label ≠ 0 then
        «Prelude.some»
          («Prover.dNode» (leaf 21) («Prelude.single» x0) ([] : List T))
      else
        «Prelude.none»);
    x1

def «Formula.assume» :=
  fun (x0 : T) (x1 : List T → List T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T := (fun (x2 : List T) (x3 : List T) (x4 : T) =>
      if («Prelude.and»
        («Language.mIs» (leaf 11) (leaf 2) x4)
        (Const.eq
          («Language.mD» x4 (leaf 0))
          (Const.add x0 (leaf 2)))).label ≠ 0 then
        let x5 : T := «Language.mArg» x4 (leaf 1);
        let x6 : T := «Language.mArg» x4 (leaf 0);
        «Base.mapO»
          (fun (x7 : T) =>
            «Prover.dNode»
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
                        (leaf 2)
                        (Const.node (leaf 0) ([] : List T))
                        (Const.node (leaf 0) («Theory.l2» x6 x5)))
                      («Prelude.single»
                        («Prover.dNode»
                          (leaf 21)
                          («Prelude.single» («Prelude.length» x3))
                          ([] : List T))))
                    («Prover.dNode»
                      (leaf 27)
                      («Theory.l3»
                        (leaf 1)
                        (Const.node (leaf 0) ([] : List T))
                        (Const.node (leaf 0) («Theory.l2» x6 x5)))
                      («Theory.l2»
                        («Prover.dNode»
                          (leaf 21)
                          («Prelude.single» («Prelude.length» x3))
                          ([] : List T))
                        x7))))))
          (x1 x2 («Prelude.append» x3 («Prelude.single» x5)) x6)
      else
        «Prelude.none»);
    x2

def «Formula.rule» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prover.dNode»
      (leaf 27)
      («Theory.l3» x0 (Const.node (leaf 0) x1) (Const.node (leaf 0) x2))
      x3;
    x4

def «Formula.hyp» :=
  fun (x0 : T) =>
    let x1 : T := «Prover.dNode»
      (leaf 21)
      («Prelude.single» x0)
      ([] : List T);
    x1

def «Formula.cut» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prover.dNode»
      (leaf 22)
      («Prelude.single» x0)
      («Theory.l2» x1 x2);
    x3

def «Formula.beta» :=
  «Prover.dNode» (leaf 3) ([] : List T) ([] : List T)

def «Formula.conv» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prover.dNode»
      (leaf 23)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Formula.from» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prover.dNode»
      (leaf 24)
      («Prelude.single» x0)
      («Theory.l2» x1 x2);
    x3

def «Formula.connective» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Prelude.and»
      («Language.mIs» (leaf 11) x2 x3)
      (Const.eq («Language.mD» x3 (leaf 0)) (Const.add x0 x1));
    x4

def «Formula.conjunction» :=
  fun (x0 : T)
    (x1 : List T → List T → T → T)
    (x2 : List T → List T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T := (fun (x3 : List T) (x4 : List T) (x5 : T) =>
      if («Formula.connective» x0 (leaf 1) (leaf 2) x5).label ≠ 0 then
        «Base.bindO»
          (x1 x3 x4 («Language.mArg» x5 (leaf 1)))
          (fun (x6 : T) =>
            «Base.mapO»
              (fun (x7 : T) =>
                «Formula.rule»
                  (leaf 1)
                  ([] : List T)
                  («Language.mArgs» x5)
                  («Theory.l2» x6 x7))
              (x2 x3 x4 («Language.mArg» x5 (leaf 0))))
      else
        «Prelude.none»);
    x3

def «Formula.conjuncts» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T := (fun (x3 : List T) (x4 : List T) (x5 : T) =>
      let x6 : T := «Prelude.at» x4 x1;
      if («Prelude.and»
        (Const.lt x1 («Prelude.length» x4))
        («Formula.connective» x0 (leaf 1) (leaf 2) x6)).label ≠ 0 then
        let x7 : T := «Language.mArg» x6 (leaf 1);
        let x8 : T := «Language.mArg» x6 (leaf 0);
        «Base.mapO»
          (fun (x9 : T) =>
            «Formula.cut»
              x7
              («Formula.rule»
                (leaf 2)
                ([] : List T)
                («Language.mArgs» x6)
                («Prelude.single» («Formula.hyp» x1)))
              («Formula.cut»
                x8
                («Formula.rule»
                  (leaf 3)
                  ([] : List T)
                  («Language.mArgs» x6)
                  («Prelude.single» («Formula.hyp» x1)))
                x9))
          (x2 x3 («Prelude.append» x4 («Theory.l2» x7 x8)) x5)
      else
        «Prelude.none»);
    x3

def «Formula.implication» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T)
    (x3 : List T → List T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T := (fun (x4 : List T) (x5 : List T) (x6 : T) =>
      let x7 : T := «Prelude.at» x5 x1;
      if («Prelude.and»
        (Const.lt x1 («Prelude.length» x5))
        («Formula.connective» x0 (leaf 2) (leaf 2) x7)).label ≠ 0 then
        «Base.bindO»
          (x2 x4 x5 («Language.mArg» x7 (leaf 1)))
          (fun (x8 : T) =>
            «Base.mapO»
              (fun (x9 : T) =>
                «Formula.cut»
                  («Language.mArg» x7 (leaf 0))
                  («Formula.rule»
                    (leaf 4)
                    ([] : List T)
                    («Language.mArgs» x7)
                    («Theory.l2» («Formula.hyp» x1) x8))
                  x9)
              (x3
                x4
                («Prelude.append» x5 («Prelude.single» («Language.mArg» x7 (leaf 0))))
                x6))
      else
        «Prelude.none»);
    x4

def «Formula.disjunct» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T := (fun (x3 : List T) (x4 : List T) (x5 : T) =>
      if («Formula.connective» x0 (leaf 6) (leaf 2) x5).label ≠ 0 then
        «Base.mapO»
          (fun (x6 : T) =>
            «Formula.rule»
              (if (x1).label ≠ 0 then leaf 8 else leaf 7)
              ([] : List T)
              («Language.mArgs» x5)
              («Prelude.single» x6))
          (x2
            x3
            x4
            («Language.mArg» x5 (if (x1).label ≠ 0 then leaf 0 else leaf 1)))
      else
        «Prelude.none»);
    x3

def «Formula.alternatives» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T)
    (x3 : List T → List T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T := (fun (x4 : List T) (x5 : List T) (x6 : T) =>
      let x7 : T := «Prelude.at» x5 x1;
      if («Prelude.and»
        (Const.lt x1 («Prelude.length» x5))
        («Formula.connective» x0 (leaf 6) (leaf 2) x7)).label ≠ 0 then
        «Base.bindO»
          («Formula.assume»
            x0
            x2
            x4
            x5
            («Tactics.impL» x0 («Language.mArg» x7 (leaf 1)) x6))
          (fun (x8 : T) =>
            «Base.mapO»
              (fun (x9 : T) =>
                «Formula.rule»
                  (leaf 9)
                  ([] : List T)
                  (x6 :: («Language.mArgs» x7))
                  («Theory.l3» («Formula.hyp» x1) x8 x9))
              («Formula.assume»
                x0
                x3
                x4
                x5
                («Tactics.impL» x0 («Language.mArg» x7 (leaf 0)) x6)))
      else
        «Prelude.none»);
    x4

def «Formula.quantified» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Formula.connective» x0 x1 (leaf 1) x2)
      (Const.eq (Const.arity («Language.mD» x2 (leaf 1))) (leaf 1));
    x3

def «Formula.instanceOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Language.mIs» (leaf 5) (leaf 1) x0).label ≠ 0 then
      «Language.subst»
        («Language.mArg» x0 (leaf 0))
        («Derivation.instVar» x1)
    else
      «Language.app» x0 x1);
    x2

def «Formula.instanceRule» :=
  fun (x0 : T) =>
    let x1 : T := (if («Language.mIs» (leaf 5) (leaf 1) x0).label ≠ 0 then
      «Formula.beta»
    else
      «Prover.dNode» (leaf 0) ([] : List T) ([] : List T));
    x1

def «Formula.allIntro» :=
  fun (x0 : T) (x1 : List T → List T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T := (fun (x2 : List T) (x3 : List T) (x4 : T) =>
      if («Formula.quantified» x0 (leaf 3) x4).label ≠ 0 then
        «Base.mapO»
          (fun (x5 : T) =>
            «Formula.conv»
              («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
              («Prover.dNode»
                (leaf 26)
                ([] : List T)
                («Prelude.single»
                  («Formula.conv»
                    («Prover.dNode»
                      (leaf 2)
                      ([] : List T)
                      («Theory.l2»
                        («Formula.instanceRule» («Language.mArg» x4 (leaf 0)))
                        «Formula.beta»))
                    («Prover.dNode»
                      (leaf 25)
                      ([] : List T)
                      («Theory.l2» «Tactics.trueI» x5))))))
          (x1
            ((Const.child («Language.mD» x4 (leaf 1)) (leaf 0)) :: x2)
            («Prelude.append»
              («Base.mapT» «Derivation.weaken1» x3)
              («Prelude.single» («Tactics.ttL» x0)))
            («Formula.instanceOf»
              («Derivation.weaken1» («Language.mArg» x4 (leaf 0)))
              («Language.var» (leaf 0))))
      else
        «Prelude.none»);
    x2

def «Formula.allElim» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T := (fun (x4 : List T) (x5 : List T) (x6 : T) =>
      let x7 : T := «Prelude.at» x5 x1;
      if («Prelude.and»
        (Const.lt x1 («Prelude.length» x5))
        («Formula.quantified» x0 (leaf 3) x7)).label ≠ 0 then
        let x8 : T := «Language.mArg» x7 (leaf 0);
        let x9 : T := «Formula.instanceOf» x8 x2;
        «Base.mapO»
          (fun (x10 : T) =>
            «Formula.cut»
              x9
              («Formula.from»
                («Language.app» x8 x2)
                («Formula.instanceRule» x8)
                («Formula.rule»
                  (leaf 5)
                  (Const.children («Language.mD» x7 (leaf 1)))
                  («Theory.l2» x2 x8)
                  («Prelude.single» («Formula.hyp» x1))))
              x10)
          (x3 x4 («Prelude.append» x5 («Prelude.single» x9)) x6)
      else
        «Prelude.none»);
    x4

def «Formula.existsIntro» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T := (fun (x3 : List T) (x4 : List T) (x5 : T) =>
      if («Formula.quantified» x0 (leaf 7) x5).label ≠ 0 then
        let x6 : T := «Language.mArg» x5 (leaf 0);
        «Base.mapO»
          (fun (x7 : T) =>
            «Formula.rule»
              (leaf 10)
              (Const.children («Language.mD» x5 (leaf 1)))
              («Theory.l2» x1 x6)
              («Prelude.single» («Formula.conv» («Formula.instanceRule» x6) x7)))
          (x2 x3 x4 («Formula.instanceOf» x6 x1))
      else
        «Prelude.none»);
    x3

def «Formula.existsElim» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T := (fun (x3 : List T) (x4 : List T) (x5 : T) =>
      let x6 : T := «Prelude.at» x4 x1;
      if («Prelude.and»
        (Const.lt x1 («Prelude.length» x4))
        («Formula.quantified» x0 (leaf 7) x6)).label ≠ 0 then
        let x7 : T := Const.child («Language.mD» x6 (leaf 1)) (leaf 0);
        let x8 : T := «Language.mArg» x6 (leaf 0);
        let x9 : T := «Language.app»
          («Derivation.weaken1» x8)
          («Language.var» (leaf 0));
        let x10 : T := «Formula.instanceOf»
          («Derivation.weaken1» x8)
          («Language.var» (leaf 0));
        let x11 : List T →
          List T →
            T →
              T := (fun (x11 : List T) (x12 : List T) (x13 : T) =>
          «Base.mapO»
            (fun (x14 : T) =>
              «Formula.cut»
                x10
                («Formula.from»
                  x9
                  («Formula.instanceRule» x8)
                  («Formula.hyp» (Const.sub («Prelude.length» x12) (leaf 1))))
                x14)
            (x2 x11 («Prelude.append» x12 («Prelude.single» x10)) x13));
        «Base.mapO»
          (fun (x12 : T) =>
            «Formula.rule»
              (leaf 11)
              («Prelude.single» x7)
              («Theory.l2» x5 x8)
              («Theory.l2» («Formula.hyp» x1) x12))
          («Formula.allIntro»
            x0
            («Formula.assume» x0 x11)
            x3
            x4
            («Logic.allL»
              x0
              x7
              («Language.mLam»
                x7
                («Tactics.impL» x0 x9 («Derivation.weaken1» x5)))))
      else
        «Prelude.none»);
    x3

def «Formula.falseElim» :=
  fun (x0 : T) (x1 : List T → List T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T := (fun (x2 : List T) (x3 : List T) (x4 : T) =>
      «Base.mapO»
        (fun (x5 : T) =>
          «Formula.rule»
            (leaf 6)
            ([] : List T)
            («Prelude.single» x4)
            («Prelude.single» x5))
        (x1 x2 x3 («Logic.ffL» x0)));
    x2

def «Formula.unfoldFormula» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T → List T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T := (fun (x4 : List T) (x5 : List T) (x6 : T) =>
      «Base.bindO»
        («Derivation.rootStep» x0 x1 x2 x4 x5 (leaf 8) ([] : List T) x6)
        (fun (x7 : T) =>
          «Base.mapO»
            («Formula.conv» («Prover.dNode» (leaf 8) ([] : List T) ([] : List T)))
            (x3 x4 x5 x7)));
    x4

def «Formula.unfoldHypothesis» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T := (fun (x5 : List T) (x6 : List T) (x7 : T) =>
      if (Const.lt x3 («Prelude.length» x6)).label ≠ 0 then
        «Base.bindO»
          («Derivation.rootStep»
            x0
            x1
            x2
            x5
            x6
            (leaf 8)
            ([] : List T)
            («Prelude.at» x6 x3))
          (fun (x8 : T) =>
            «Base.mapO»
              (fun (x9 : T) =>
                «Formula.cut»
                  x8
                  («Formula.from»
                    («Prelude.at» x6 x3)
                    («Prover.dNode» (leaf 8) ([] : List T) ([] : List T))
                    («Formula.hyp» x3))
                  x9)
              (x4 x5 («Prelude.append» x6 («Prelude.single» x8)) x7))
      else
        «Prelude.none»);
    x5

def «Formula/Deducers.single» :=
  fun (x0 : List T → List T → T → T) =>
    let x1 : List
      (List T →
        List T → T → T) := (x0 :: ([] : List (List T → List T → T → T)));
    x1

def «Formula/Deducers.length» :=
  fun (x0 : List (List T → List T → T → T)) =>
    let x1 : T := Const.foldr
      (α := List T → List T → T → T)
      (β := T)
      (fun (_ : List T → List T → T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Formula/Deducers.append» :=
  fun (x0 : List (List T → List T → T → T))
    (x1 : List (List T → List T → T → T)) =>
    let x2 : List
      (List T →
        List T →
          T →
            T) := Const.foldr
      (α := List T → List T → T → T)
      (β := List (List T → List T → T → T))
      (fun (x2 : List T → List T → T → T)
         (x3 : List (List T → List T → T → T)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Formula/Deducers.reverse» :=
  fun (x0 : List (List T → List T → T → T)) =>
    let x1 : List
      (List T →
        List T →
          T →
            T) := Const.foldr
      (α := List T → List T → T → T)
      (β := List (List T → List T → T → T) → List (List T → List T → T → T))
      (fun (x1 : List T → List T → T → T)
         (x2 : List (List T → List T → T → T) → List (List T → List T → T → T))
         (x3 : List (List T → List T → T → T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List T → List T → T → T)) => x1)
      x0
      ([] : List (List T → List T → T → T));
    x1

def «Formula/Deducers.tail» :=
  fun (x0 : List (List T → List T → T → T)) =>
    let x1 : List
      (List T →
        List T →
          T →
            T) := Const.lcase
      (α := List T → List T → T → T)
      (β := List (List T → List T → T → T))
      x0
      ([] : List (List T → List T → T → T))
      (fun (_ : List T → List T → T → T)
         (x2 : List (List T → List T → T → T)) =>
        x2);
    x1

def «Formula/Deducers.drop» :=
  fun (x0 : T) (x1 : List (List T → List T → T → T)) =>
    let x2 : List
      (List T →
        List T →
          T →
            T) := Const.iter
      (α := List (List T → List T → T → T))
      «Formula/Deducers.tail»
      x1
      x0;
    x2

def «Formula/Deducers.atOr» :=
  fun (x0 : List T → List T → T → T)
    (x1 : List (List T → List T → T → T))
    (x2 : T) =>
    let x3 : List T →
      List T →
        T →
          T := Const.lcase
      (α := List T → List T → T → T)
      (β := List T → List T → T → T)
      («Formula/Deducers.drop» x2 x1)
      x0
      (fun (x3 : List T → List T → T → T)
         (_ : List (List T → List T → T → T)) =>
        x3);
    x3

def «Formula.noProof» :=
  fun (_ : List T) (_ : List T) (_ : T) => «Prelude.none»

def «Formula.applyTheorem» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List (List T → List T → T → T)) =>
    let x5 : List T →
      List T →
        T →
          T := (fun (x5 : List T) (x6 : List T) (x7 : T) =>
      let x8 : T := «Derivation.thmAt» x0 x1;
      if (Const.eq (Const.label x8) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x8; «Prelude.none»
      else
        let x9 : List T := Const.children x8;
        let x10 : T := Const.lcase
          (α := T)
          (β := T)
          x9
          (leaf 0)
          (fun (x10 : T) (_ : List T) => x10);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x9
          ([] : List T)
          (fun (_ : T) (x12 : List T) => x12);
        let x12 : T := x10;
        let x13 : List T := Const.children x12;
        let x14 : T := Const.lcase
          (α := T)
          (β := T)
          x13
          (leaf 0)
          (fun (x14 : T) (_ : List T) => x14);
        let x15 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x13
          ([] : List T)
          (fun (_ : T) (x16 : List T) => x16);
        let x16 : T := Const.lcase
          (α := T)
          (β := T)
          x15
          (leaf 0)
          (fun (x16 : T) (_ : List T) => x16);
        let x17 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x15
          ([] : List T)
          (fun (_ : T) (x18 : List T) => x18);
        let x18 : T := Const.lcase
          (α := T)
          (β := T)
          x17
          (leaf 0)
          (fun (x18 : T) (_ : List T) => x18);
        let x19 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x17
          ([] : List T)
          (fun (_ : T) (x20 : List T) => x20);
        let x20 : T := Const.lcase
          (α := T)
          (β := T)
          x19
          (leaf 0)
          (fun (x20 : T) (_ : List T) => x20);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x19
          ([] : List T)
          (fun (_ : T) (x22 : List T) => x22);
        let x22 : T := x18;
        let x23 : List T := Const.children x22;
        let x24 : List T := x23;
        if («Prelude.and»
          (Const.eq x14 («Prelude.length» x2))
          («Prelude.and»
            (Const.eq
              («Prelude.length»
                (let x25 : T := x16;
                 let x26 : List T := Const.children x25; let x27 : List T := x26; x27))
              («Prelude.length» x3))
            («Prelude.and»
              (Const.equal x7 («Derivation.instTerm» x2 x3 x20))
              (Const.eq
                («Prelude.length» x24)
                («Formula/Deducers.length» x4))))).label ≠ 0 then
          «Base.mapO»
            (fun (x25 : T) => «Formula.rule» x1 x2 x3 (Const.children x25))
            («Base.allSomeT»
              («Base.mapT»
                (fun (x25 : T) =>
                  «Formula/Deducers.atOr»
                    «Formula.noProof»
                    x4
                    x25
                    x5
                    x6
                    («Derivation.instTerm» x2 x3 («Prelude.at» x24 x25)))
                («Base.range» («Prelude.length» x24))))
        else
          «Prelude.none»);
    x5

def «Authoring/LD.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/LD.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/LD.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/LD.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/LD.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/LD.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/LD.tail» x1 x0;
    x2

def «Authoring/LD.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/LD.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/OS.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/OS.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/OS.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/OS.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/OS.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/OS.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/OS.tail» x1 x0;
    x2

def «Authoring/OS.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/OS.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/PF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Authoring/PF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Authoring/PF.l2» x1 x2)); x3

def «Authoring/PF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Authoring/PF.l3» x1 x2 x3)); x4

def «Authoring/PF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Authoring/PF.l4» x1 x2 x3 x4)); x5

def «Authoring/PF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Authoring/PF.l5» x1 x2 x3 x4 x5)); x6

def «Authoring/PrimL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/PrimL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/PrimL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/PrimL.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/PrimL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/PrimL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/PrimL.tail» x1 x0;
    x2

def «Authoring/PrimL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/PrimL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/DL.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring/Decls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Decls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Decls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Decls.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Decls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Decls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Decls.tail» x1 x0;
    x2

def «Authoring/Decls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Decls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/Rules.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Rules.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Rules.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Rules.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Rules.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Rules.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Rules.tail» x1 x0;
    x2

def «Authoring/Rules.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Rules.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.word» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isAtom» x0)
      (Const.equal («Reader.nameOf» x0) x1);
    x2

def «Authoring.form» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x0)) x2)
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x3

def «Authoring.headed» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.lt (leaf 0) («Prelude.length» (Const.children x0)))
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x2

def «Authoring.number» :=
  fun (x0 : T) =>
    let x1 : T := (if («Reader.isAtom» x0).label ≠ 0 then
      «Reader.numeral» (Const.children x0)
    else
      «Prelude.none»);
    x1

def «Authoring.has» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Prelude.isSome» («Reader.indexOf» x0 x1); x2

def «Authoring.declared» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Reader.isAtom» x0)
      («Prelude.and»
        («Base.not» («Base.isEmpty» (Const.children x0)))
        («Prelude.and»
          («Base.not» («Prelude.isSome» («Authoring.number» x0)))
          («Base.not»
            («Authoring.has» («Reader.nameOf» x0) «Reader.reservedNames»))));
    x1

def «Authoring.internalNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 105, leaf 110, leaf 108],
      mk 0 [leaf 105, leaf 110, leaf 114],
      mk 0 [leaf 99, leaf 97, leaf 115, leaf 101],
      mk 0 [leaf 108,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 45,
        leaf 114,
        leaf 101,
        leaf 99],
      mk 0 [leaf 114,
        leaf 111,
        leaf 115,
        leaf 101,
        leaf 45,
        leaf 114,
        leaf 101,
        leaf 99],
      mk 0 [leaf 108, leaf 105, leaf 98],
      mk 0 [leaf 107, leaf 101, leaf 114, leaf 110, leaf 101, leaf 108]])

def «Authoring.connectiveNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 116, leaf 114, leaf 117, leaf 101],
      mk 0 [leaf 105,
        leaf 109,
        leaf 112,
        leaf 108,
        leaf 105,
        leaf 101,
        leaf 115]])

def «Authoring.naturalNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 122, leaf 101, leaf 114, leaf 111],
      mk 0 [leaf 115, leaf 117, leaf 99, leaf 99],
      mk 0 [leaf 110,
        leaf 97,
        leaf 116,
        leaf 45,
        leaf 114,
        leaf 101,
        leaf 99]])

def «Authoring.formulaNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 102, leaf 97, leaf 108, leaf 115, leaf 101],
      mk 0 [leaf 97, leaf 110, leaf 100],
      mk 0 [leaf 111, leaf 114],
      mk 0 [leaf 110, leaf 111, leaf 116],
      mk 0 [leaf 97, leaf 108, leaf 108],
      mk 0 [leaf 101, leaf 120, leaf 105, leaf 115, leaf 116, leaf 115],
      mk 0 [leaf 101,
        leaf 120,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 115,
        leaf 45,
        leaf 117,
        leaf 110,
        leaf 105,
        leaf 113,
        leaf 117,
        leaf 101],
      mk 0 [leaf 97,
        leaf 115,
        leaf 115,
        leaf 117,
        leaf 109,
        leaf 105,
        leaf 110,
        leaf 103]])

def «Authoring.bindable» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Authoring.declared» x1)
      («Prelude.and»
        («Base.not»
          («Authoring.has» («Reader.nameOf» x1) «Authoring.internalNames»))
        («Prelude.and»
          («Base.not»
            («Prelude.and»
              (Const.lt (leaf 2) x0)
              («Authoring.has» («Reader.nameOf» x1) «Authoring.connectiveNames»)))
          («Prelude.and»
            («Base.not»
              («Prelude.and»
                (Const.lt (leaf 3) x0)
                («Authoring.has» («Reader.nameOf» x1) «Authoring.naturalNames»)))
            («Base.not»
              («Prelude.and»
                (Const.lt (leaf 4) x0)
                («Authoring.has» («Reader.nameOf» x1) «Authoring.formulaNames»))))));
    x2

def «Authoring.distinctFrom» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := List T → T)
      (fun (x2 : T) (x3 : List T → T) (x4 : List T) =>
        «Prelude.and» («Base.not» («Authoring.has» x2 x4)) (x3 (x2 :: x4)))
      (fun (_ : List T) => leaf 1)
      x1
      x0;
    x2

def «Authoring.namesOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x2)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x2)) x1)
        («Base.allT» («Authoring.bindable» x0) (Const.children x2)));
    x3

def «Authoring.kZero» := leaf 6

def «Authoring.kSucc» := leaf 7

def «Authoring.primsFor» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : List
              T := «Authoring/PF.l6»
              «Derivation.nilPrim»
              «Derivation.consPrim»
              «Derivation.lnodePrim»
              «Derivation.inlPrim»
              «Derivation.inrPrim»
              «Derivation.casePrim»;
            if (Const.lt (leaf 3) x0).label ≠ 0 then
              «Authoring/PrimL.append»
                x1
                («Authoring/PF.l2»
                  («Language.primitive»
                    (leaf 0)
                    «Theory.zeroN»
                    «Theory.one»
                    «Theory.nat»)
                  («Language.primitive»
                    (leaf 0)
                    «Theory.succ»
                    «Theory.nat»
                    «Theory.nat»))
            else
              x1);
    x1

def «Authoring.globalsOf» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Language.globals»
      («Language.prims» («Authoring.primsFor» x0))
      («Language.defs»
        («Authoring/DL.map»
          «Language.defLang»
          («Authoring/LD.append» «Translation.lib» x1)))
      («Authoring/OS.length» «Theory.sig»);
    x2

def «Authoring.connectivesAt» :=
  fun (x0 : List T) =>
    let x1 : T := Const.add
      («Authoring/LD.length» «Translation.lib»)
      («Prelude.length» x0);
    x1

def «Authoring.connectivesOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (if (Const.lt (leaf 3) x0).label ≠ 0 then
      «Logic.connectivesAll» x1
    else
      if (Const.lt (leaf 2) x0).label ≠ 0 then
        «Logic.connectives» x1
      else
        ([] : List T));
    x2

def «Authoring.rulesFor» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List
      T := (if (Const.lt (leaf 3) x0).label ≠ 0 then
      «Logic.connectiveRulesAll» x1 x2
    else
      if (Const.lt (leaf 2) x0).label ≠ 0 then
        «Logic.connectiveRules» x1 x2
      else
        ([] : List T));
    x3

def «Authoring.globalsFor» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Authoring.globalsOf»
      x0
      («Authoring/LD.append»
        x1
        («Authoring.connectivesOf»
          x0
          (Const.add
            («Authoring/LD.length» «Translation.lib»)
            («Authoring/LD.length» x1))));
    x2

def «Authoring.ruleCount» :=
  «Authoring/Decls.length» («Logic.connectiveRules» (leaf 0) (leaf 0))

def «Authoring.ruleCountAll» :=
  «Authoring/Decls.length»
    («Logic.connectiveRulesAll» (leaf 0) (leaf 0))

def «Authoring.entryBase» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.lt (leaf 3) x0).label ≠ 0 then
      «Authoring.ruleCountAll»
    else
      if (Const.lt (leaf 2) x0).label ≠ 0 then
        «Authoring.ruleCount»
      else
        leaf 0);
    x1

def «Authoring.declaredAt» :=
  fun (x0 : List T) =>
    let x1 : T := Const.add
      («Authoring.connectivesAt» x0)
      («Authoring/LD.length» («Logic.connectivesAll» (leaf 0)));
    x1

def «Authoring.rulesOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : List
              T := ((«Prover.nrBelow» x1 («Derivation.terms» ([] : List T))) ::
              (if (Const.lt (leaf 3) x0).label ≠ 0 then
                ((«Prover.nrRule»
                  (leaf 9)
                  («Derivation.terms» («Prelude.single» «Authoring.kZero»))) ::
                  («Authoring/Rules.single»
                    («Prover.nrRule»
                      (leaf 10)
                      («Derivation.terms» («Prelude.single» «Authoring.kSucc»)))))
              else
                ([] : List T)));
            ((«Prover.nrRule» (leaf 3) («Derivation.terms» ([] : List T))) ::
              ((«Prover.nrRule» (leaf 4) («Derivation.terms» ([] : List T))) ::
                ((«Prover.nrRule» (leaf 5) («Derivation.terms» ([] : List T))) ::
                  (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                    x2
                  else
                    ((«Prover.nrRule»
                      (leaf 11)
                      («Derivation.terms» («Prelude.single» (leaf 0)))) ::
                      ((«Prover.nrRule»
                        (leaf 12)
                        («Derivation.terms» («Prelude.single» (leaf 1)))) ::
                        ((«Prover.nrRule»
                          (leaf 13)
                          («Derivation.terms» («Theory.l3» (leaf 2) (leaf 0) (leaf 1)))) ::
                          ((«Prover.nrRule»
                            (leaf 14)
                            («Derivation.terms» («Theory.l2» (leaf 5) (leaf 3)))) ::
                            ((«Prover.nrRule»
                              (leaf 15)
                              («Derivation.terms» («Theory.l2» (leaf 5) (leaf 4)))) ::
                              («Prover.nrUnit» :: x2)))))))))));
    x2

def «Authoring.declaredRef» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 3) («Theory.l2» x0 x1); x2

def «Authoring.isDeclaredRef» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2));
    x1

def «Authoring.natRef» :=
  Const.node (leaf 3) («Prelude.single» (leaf 0))

def «Authoring.isNatRef» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 1));
    x1

def «Authoring.withNames» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        if («Reader.isAtom» x2).label ≠ 0 then
          let x4 : T := «Reader.lookupAbbrev» («Reader.nameOf» x2) x0;
          if («Prelude.isSome» x4).label ≠ 0 then «Prelude.get» x4 else x2
        else
          Const.node (Const.label x2) x3)
      x1;
    x2

def «Authoring.kernelType» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Reader.resolve»
                     ([] : List T)
                     x0
                     (Const.node
                       (leaf 2)
                       («Theory.l2»
                         (Const.node (leaf 1) (Const.children «Reader.kwNil»))
                         x1))
                     ([] : List T);
                   if («Prelude.isSome» x2).label ≠ 0 then
                     «Prelude.some» (Const.child («Prelude.get» x2) (leaf 0))
                   else
                     «Prelude.none»);
    x2

def «Authoring.itype» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := «Prelude.length» x3;
        let x5 : T := Const.child x2 (leaf 0);
        let x6 : (T → T → T) →
          T := (fun (x6 : T → T → T) =>
          if (Const.eq x4 (leaf 3)).label ≠ 0 then
            «Base.bindO»
              («Prelude.at» x3 (leaf 1))
              (fun (x7 : T) => «Base.mapO» (x6 x7) («Prelude.at» x3 (leaf 2)))
          else
            «Prelude.none»);
        let x7 : (T → T) →
          T := (fun (x7 : T → T) =>
          if (Const.eq x4 (leaf 2)).label ≠ 0 then
            «Base.mapO» x7 («Prelude.at» x3 (leaf 1))
          else
            «Prelude.none»);
        if («Reader.isAtom» x2).label ≠ 0 then
          let x8 : T := «Reader.nameOf» x2;
          if (Const.equal x8 «Reader.kwT»).label ≠ 0 then
            «Prelude.some» «Translation.treeTy»
          else
            if (Const.equal x8 «Reader.kwUnit»).label ≠ 0 then
              «Prelude.some» «Theory.one»
            else
              if (Const.equal
                x8
                (mk 0 [leaf 66, leaf 105, leaf 116])).label ≠ 0 then
                «Prelude.some» («Theory.coprod» «Theory.one» «Theory.one»)
              else
                if (Const.equal
                  x8
                  (mk 0 [leaf 66, leaf 105, leaf 116, leaf 115])).label ≠ 0 then
                  «Prelude.some» «Translation.bitsTy»
                else
                  if (Const.equal
                    x8
                    (mk 0 [leaf 79,
                      leaf 109,
                      leaf 101,
                      leaf 103,
                      leaf 97])).label ≠ 0 then
                    «Prelude.some» «Theory.omega»
                  else
                    «Base.mapO» «Theory.x» («Reader.indexOf» x8 x0)
        else
          if («Base.not» («Reader.isList» x2)).label ≠ 0 then
            if («Authoring.isNatRef» x2).label ≠ 0 then
              «Prelude.some» «Theory.nat»
            else
              «Prelude.none»
          else
            if («Authoring.word» x5 «Reader.kwProd»).label ≠ 0 then
              x6 «Theory.prod»
            else
              if («Authoring.word»
                x5
                (mk 0 [leaf 83, leaf 117, leaf 109])).label ≠ 0 then
                x6 «Theory.coprod»
              else
                if («Authoring.word» x5 «Reader.kwArrow»).label ≠ 0 then
                  x6 «Theory.exp»
                else
                  if («Authoring.word» x5 «Reader.kwList»).label ≠ 0 then
                    x7 «Theory.list»
                  else
                    if («Authoring.word»
                      x5
                      (mk 0 [leaf 82, leaf 111, leaf 115, leaf 101])).label ≠ 0 then
                      x7 «Theory.lrose»
                    else
                      «Prelude.none»)
      x1;
    x2

def «Authoring.listElem» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      if («Prelude.and»
        (Const.eq (Const.label («Prelude.get» x0)) (leaf 4))
        (Const.eq (Const.arity («Prelude.get» x0)) (leaf 1))).label ≠ 0 then
        «Prelude.some» (Const.child («Prelude.get» x0) (leaf 0))
      else
        «Prelude.none»
    else
      «Prelude.none»);
    x1

def «Authoring.ikernel» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := (let x5 : List
                     T := Const.foldr
                     (α := T)
                     (β := List T)
                     (fun (x5 : T) (x6 : List T) =>
                       if («Prelude.isSome» («Prelude.at» x4 x5)).label ≠ 0 then
                         (x5 :: x6)
                       else
                         x6)
                     ([] : List T)
                     («Base.range» («Prelude.length» x3));
                   «Base.bindO»
                     («Reader.resolve»
                       ([] : List T)
                       x1
                       x2
                       («Base.mapT» («Prelude.at» x3) x5))
                     (fun (x6 : T) =>
                       let x7 : T := «Translation.term»
                         x0
                         («Base.mapT» (fun (x7 : T) => «Prelude.get» («Prelude.at» x4 x7)) x5)
                         x6;
                       if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x7; «Prelude.none»
                       else
                         let x8 : List T := Const.children x7;
                         let x9 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x8
                           (leaf 0)
                           (fun (x9 : T) (_ : List T) => x9);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x8
                           ([] : List T)
                           (fun (_ : T) (x11 : List T) => x11);
                         «Prelude.some»
                           (if (Const.eq
                             («Prelude.length» x5)
                             («Prelude.length» x3)).label ≠ 0 then
                             «Language.p2» x9
                           else
                             «Language.rename»
                               («Language.p2» x9)
                               (fun (x11 : T) => «Prelude.at» x5 x11))));
    x5

def «Authoring.libEntry» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 0) («Theory.l2» x0 x1); x2

def «Authoring.libTable» :=
  «Prelude.append»
    («Theory.l6»
      («Authoring.libEntry»
        (mk 0 [leaf 98, leaf 110, leaf 105, leaf 108])
        (leaf 0))
      («Authoring.libEntry» (mk 0 [leaf 98, leaf 48]) (leaf 1))
      («Authoring.libEntry» (mk 0 [leaf 98, leaf 49]) (leaf 2))
      («Authoring.libEntry» (mk 0 [leaf 108, leaf 97, leaf 98]) (leaf 3))
      («Authoring.libEntry»
        (mk 0 [leaf 117, leaf 110, leaf 110, leaf 111, leaf 100, leaf 101])
        (leaf 4))
      («Authoring.libEntry»
        (mk 0 [leaf 99,
          leaf 104,
          leaf 105,
          leaf 108,
          leaf 100,
          leaf 114,
          leaf 101,
          leaf 110])
        (leaf 5)))
    («Prelude.append»
      («Theory.l6»
        («Authoring.libEntry»
          (mk 0 [leaf 99, leaf 111, leaf 110, leaf 100])
          (leaf 6))
        («Authoring.libEntry»
          (mk 0 [leaf 116, leaf 97, leaf 105, leaf 108])
          (leaf 7))
        («Authoring.libEntry»
          (mk 0 [leaf 104, leaf 101, leaf 97, leaf 100, leaf 68])
          (leaf 8))
        («Authoring.libEntry»
          (mk 0 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101])
          (leaf 9))
        («Authoring.libEntry»
          (mk 0 [leaf 105, leaf 115, leaf 78, leaf 105, leaf 108])
          (leaf 10))
        («Authoring.libEntry»
          (mk 0 [leaf 115, leaf 117, leaf 99, leaf 99])
          (leaf 11)))
      («Prelude.append»
        («Theory.l6»
          («Authoring.libEntry»
            (mk 0 [leaf 108, leaf 101, leaf 110, leaf 103, leaf 116, leaf 104])
            (leaf 12))
          («Authoring.libEntry»
            (mk 0 [leaf 112, leaf 114, leaf 101, leaf 100])
            (leaf 13))
          («Authoring.libEntry» (mk 0 [leaf 100, leaf 98, leaf 108]) (leaf 14))
          («Authoring.libEntry» (mk 0 [leaf 97, leaf 100, leaf 100]) (leaf 15))
          («Authoring.libEntry» (mk 0 [leaf 99, leaf 109, leaf 112]) (leaf 16))
          («Authoring.libEntry» (mk 0 [leaf 108, leaf 116, leaf 66]) (leaf 17)))
        («Prelude.append»
          («Theory.l6»
            («Authoring.libEntry» (mk 0 [leaf 101, leaf 113, leaf 66]) (leaf 18))
            («Authoring.libEntry»
              (mk 0 [leaf 115, leaf 117, leaf 98, leaf 69])
              (leaf 19))
            («Authoring.libEntry» (mk 0 [leaf 115, leaf 117, leaf 98]) (leaf 20))
            («Authoring.libEntry» (mk 0 [leaf 109, leaf 117, leaf 108]) (leaf 21))
            («Authoring.libEntry»
              (mk 0 [leaf 100, leaf 105, leaf 118, leaf 77, leaf 111, leaf 100])
              (leaf 22))
            («Authoring.libEntry»
              (mk 0 [leaf 108, leaf 111, leaf 103, leaf 50])
              (leaf 23)))
          («Theory.l5»
            («Authoring.libEntry»
              (mk 0 [leaf 105, leaf 116, leaf 101, leaf 114])
              (leaf 24))
            («Authoring.libEntry»
              (mk 0 [leaf 109, leaf 97, leaf 112, leaf 65, leaf 112, leaf 112])
              (leaf 25))
            («Authoring.libEntry» (mk 0 [leaf 97, leaf 110, leaf 100]) (leaf 26))
            («Authoring.libEntry»
              (mk 0 [leaf 97, leaf 108, leaf 108, leaf 90, leaf 105, leaf 112])
              (leaf 27))
            («Authoring.libEntry»
              (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
              (leaf 28))))))

def «Authoring.ilib» :=
  fun (x0 : List T) (x1 : List T) (x2 : T → T) =>
    let x3 : T := «Base.bindO»
      (if («Reader.isAtom» («Prelude.at» x1 (leaf 1))).label ≠ 0 then
        «Reader.lookupAbbrev»
          («Reader.nameOf» («Prelude.at» x1 (leaf 1)))
          «Authoring.libTable»
      else
        «Prelude.none»)
      (fun (x3 : T) =>
        let x4 : T := «Language/OLDefn.nthOf» «Translation.lib» x3;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x4; «Prelude.none»
        else
          let x5 : List T := Const.children x4;
          let x6 : T := Const.lcase
            (α := T)
            (β := T)
            x5
            (leaf 0)
            (fun (x6 : T) (_ : List T) => x6);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x5
            ([] : List T)
            (fun (_ : T) (x8 : List T) => x8);
          let x8 : T := x6;
          let x9 : List T := Const.children x8;
          let x10 : T := Const.lcase
            (α := T)
            (β := T)
            x9
            (leaf 0)
            (fun (x10 : T) (_ : List T) => x10);
          let x11 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x9
            ([] : List T)
            (fun (_ : T) (x12 : List T) => x12);
          let x12 : T := Const.lcase
            (α := T)
            (β := T)
            x11
            (leaf 0)
            (fun (x12 : T) (_ : List T) => x12);
          let x13 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x11
            ([] : List T)
            (fun (_ : T) (x14 : List T) => x14);
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x13
            (leaf 0)
            (fun (x14 : T) (_ : List T) => x14);
          let x15 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x13
            ([] : List T)
            (fun (_ : T) (x16 : List T) => x16);
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x15
            (leaf 0)
            (fun (x16 : T) (_ : List T) => x16);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x15
            ([] : List T)
            (fun (_ : T) (x18 : List T) => x18);
          let x18 : T := x12;
          let x19 : List T := Const.children x18;
          let x20 : List T := x19;
          if (Const.eq
            («Prelude.length» x1)
            (Const.add
              (leaf 2)
              (Const.add x10 («Prelude.length» x20)))).label ≠ 0 then
            «Base.bindO»
              («Base.allSomeT»
                («Base.mapT»
                  (fun (x21 : T) =>
                    «Authoring.itype» x0 («Prelude.at» x1 (Const.add (leaf 2) x21)))
                  («Base.range» x10)))
              (fun (x21 : T) =>
                «Base.mapO»
                  (fun (x22 : T) =>
                    «Translation.call» x3 (Const.children x21) (Const.children x22))
                  («Base.allSomeT»
                    («Base.mapT»
                      (fun (x22 : T) => x2 (Const.add (Const.add (leaf 2) x10) x22))
                      («Base.range» («Prelude.length» x20)))))
          else
            «Prelude.none»);
    x3

def «Authoring/IRs.single» :=
  fun (x0 : List T → List T → T) =>
    let x1 : List
      (List T → List T → T) := (x0 :: ([] : List (List T → List T → T)));
    x1

def «Authoring/IRs.length» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : T := Const.foldr
      (α := List T → List T → T)
      (β := T)
      (fun (_ : List T → List T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/IRs.append» :=
  fun (x0 : List (List T → List T → T))
    (x1 : List (List T → List T → T)) =>
    let x2 : List
      (List T →
        List T →
          T) := Const.foldr
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      (fun (x2 : List T → List T → T) (x3 : List (List T → List T → T)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/IRs.reverse» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : List
      (List T →
        List T →
          T) := Const.foldr
      (α := List T → List T → T)
      (β := List (List T → List T → T) → List (List T → List T → T))
      (fun (x1 : List T → List T → T)
         (x2 : List (List T → List T → T) → List (List T → List T → T))
         (x3 : List (List T → List T → T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List T → List T → T)) => x1)
      x0
      ([] : List (List T → List T → T));
    x1

def «Authoring/IRs.tail» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : List
      (List T →
        List T →
          T) := Const.lcase
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      x0
      ([] : List (List T → List T → T))
      (fun (_ : List T → List T → T) (x2 : List (List T → List T → T)) =>
        x2);
    x1

def «Authoring/IRs.drop» :=
  fun (x0 : T) (x1 : List (List T → List T → T)) =>
    let x2 : List
      (List T →
        List T →
          T) := Const.iter
      (α := List (List T → List T → T))
      «Authoring/IRs.tail»
      x1
      x0;
    x2

def «Authoring/IRs.atOr» :=
  fun (x0 : List T → List T → T)
    (x1 : List (List T → List T → T))
    (x2 : T) =>
    let x3 : List T →
      List T →
        T := Const.lcase
      (α := List T → List T → T)
      (β := List T → List T → T)
      («Authoring/IRs.drop» x2 x1)
      x0
      (fun (x3 : List T → List T → T) (_ : List (List T → List T → T)) =>
        x3);
    x3

def «Authoring.failIR» :=
  fun (_ : List T) (_ : List T) => «Prelude.none»

def «Authoring.map2» :=
  fun (x0 : T → T → T) (x1 : T) (x2 : T) =>
    let x3 : T := «Base.bindO»
      x1
      (fun (x3 : T) => «Base.mapO» (x0 x3) x2);
    x3

def «Authoring.binderName» :=
  fun (x0 : T) =>
    let x1 : T := «Reader.nameOf» (Const.child x0 (leaf 0)); x1

def «Authoring.ibinder» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x2)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x2)) (leaf 2))
        («Prelude.and»
          («Authoring.bindable» x0 (Const.child x2 (leaf 0)))
          («Prelude.isSome» («Authoring.itype» x1 (Const.child x2 (leaf 1))))));
    x3

def «Authoring.ilam» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T → List T → T)
    (x5 : List T)
    (x6 : List T) =>
    let x7 : T := (if («Prelude.and»
      («Base.not» («Base.isEmpty» x3))
      («Base.allT» («Authoring.ibinder» x0 x2) x3)).label ≠ 0 then
      «Base.mapO»
        (fun (x7 : T) =>
          Const.foldr
            (α := T)
            (β := T)
            (fun (x8 : T) (x9 : T) =>
              «Language.mLam»
                («Base.getD»
                  («Authoring.itype» x2 (Const.child x8 (leaf 1)))
                  «Theory.one»)
                x9)
            x7
            x3)
        (x4
          («Prelude.append»
            («Prelude.reverse» («Base.mapT» «Authoring.binderName» x3))
            x5)
          («Prelude.append»
            («Prelude.reverse»
              («Base.mapT»
                (fun (x7 : T) => «Authoring.kernelType» x1 (Const.child x7 (leaf 1)))
                x3))
            x6))
    else
      «Prelude.none»);
    x7

def «Authoring.iatom» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «Reader.indexOf» x2 x3;
                   if («Prelude.isSome» x4).label ≠ 0 then
                     «Prelude.some» («Language.var» («Prelude.get» x4))
                   else
                     if (Const.equal x2 «Reader.kwUnitValue»).label ≠ 0 then
                       «Prelude.some» «Language.mStar»
                     else
                       if («Prelude.and»
                         (Const.lt (leaf 2) x0)
                         (Const.equal
                           x2
                           (mk 0 [leaf 116, leaf 114, leaf 117, leaf 101]))).label ≠ 0 then
                         «Prelude.some» («Tactics.ttL» («Authoring.connectivesAt» x1))
                       else
                         if («Prelude.and»
                           (Const.lt (leaf 3) x0)
                           (Const.equal
                             x2
                             (mk 0 [leaf 122, leaf 101, leaf 114, leaf 111]))).label ≠ 0 then
                           «Prelude.some»
                             («Language.mArr» «Authoring.kZero» ([] : List T) «Language.mStar»)
                         else
                           if («Prelude.and»
                             (Const.lt (leaf 4) x0)
                             (Const.equal
                               x2
                               (mk 0 [leaf 102,
                                 leaf 97,
                                 leaf 108,
                                 leaf 115,
                                 leaf 101]))).label ≠ 0 then
                             «Prelude.some» («Logic.ffL» («Authoring.connectivesAt» x1))
                           else
                             «Base.mapO»
                               (fun (x5 : T) =>
                                 «Translation.call»
                                   (Const.add («Authoring/LD.length» «Translation.lib») x5)
                                   ([] : List T)
                                   ([] : List T))
                               («Reader.indexOf» x2 x1));
    x4

def «Authoring.iprim» :=
  fun (x0 : List T) (x1 : List T) (x2 : T → T) =>
    let x3 : T := (let x3 : T := «Prelude.length» x1;
                   let x4 : T := «Prelude.at» x1 (leaf 0);
                   let x5 : T →
                     T := (fun (x5 : T) => «Authoring.itype» x0 («Prelude.at» x1 x5));
                   if («Authoring.word» x4 «Reader.kwNil»).label ≠ 0 then
                     if (Const.eq x3 (leaf 2)).label ≠ 0 then
                       «Base.mapO»
                         (fun (x6 : T) =>
                           «Language.mArr» (leaf 0) («Prelude.single» x6) «Language.mStar»)
                         (x5 (leaf 1))
                     else
                       «Prelude.none»
                   else
                     if («Authoring.word» x4 «Reader.kwCons»).label ≠ 0 then
                       if (Const.eq x3 (leaf 4)).label ≠ 0 then
                         «Base.bindO»
                           (x5 (leaf 1))
                           (fun (x6 : T) =>
                             «Authoring.map2»
                               (fun (x7 : T) (x8 : T) =>
                                 «Language.mArr»
                                   (leaf 1)
                                   («Prelude.single» x6)
                                   («Language.mPair» x7 x8))
                               (x2 (leaf 2))
                               (x2 (leaf 3)))
                       else
                         «Prelude.none»
                     else
                       if («Authoring.word»
                         x4
                         (mk 0 [leaf 110, leaf 111, leaf 100, leaf 101])).label ≠ 0 then
                         if (Const.eq x3 (leaf 3)).label ≠ 0 then
                           «Authoring.map2»
                             (fun (x6 : T) (x7 : T) =>
                               «Language.mArr» (leaf 2) («Prelude.single» x6) x7)
                             (x5 (leaf 1))
                             (x2 (leaf 2))
                         else
                           «Prelude.none»
                       else
                         if («Prelude.or»
                           («Authoring.word» x4 (mk 0 [leaf 105, leaf 110, leaf 108]))
                           («Authoring.word»
                             x4
                             (mk 0 [leaf 105, leaf 110, leaf 114]))).label ≠ 0 then
                           if (Const.eq x3 (leaf 4)).label ≠ 0 then
                             «Base.bindO»
                               (x5 (leaf 1))
                               (fun (x6 : T) =>
                                 «Authoring.map2»
                                   (fun (x7 : T) (x8 : T) =>
                                     «Language.mArr»
                                       (if («Authoring.word»
                                         x4
                                         (mk 0 [leaf 105, leaf 110, leaf 108])).label ≠ 0 then
                                         leaf 3
                                       else
                                         leaf 4)
                                       («Theory.l2» x6 x7)
                                       x8)
                                   (x5 (leaf 2))
                                   (x2 (leaf 3)))
                           else
                             «Prelude.none»
                         else
                           if (Const.eq x3 (leaf 5)).label ≠ 0 then
                             «Base.bindO»
                               (x5 (leaf 1))
                               (fun (x6 : T) =>
                                 «Base.bindO»
                                   (x5 (leaf 2))
                                   (fun (x7 : T) =>
                                     «Authoring.map2»
                                       (fun (x8 : T) (x9 : T) =>
                                         «Language.mArr» (leaf 5) («Theory.l3» x6 x7 x8) x9)
                                       (x5 (leaf 3))
                                       (x2 (leaf 4))))
                           else
                             «Prelude.none»);
    x3

def «Authoring.primHead» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.or»
      («Authoring.word» x0 «Reader.kwNil»)
      («Prelude.or»
        («Authoring.word» x0 «Reader.kwCons»)
        («Prelude.or»
          («Authoring.word» x0 (mk 0 [leaf 110, leaf 111, leaf 100, leaf 101]))
          («Prelude.or»
            («Authoring.word» x0 (mk 0 [leaf 105, leaf 110, leaf 108]))
            («Prelude.or»
              («Authoring.word» x0 (mk 0 [leaf 105, leaf 110, leaf 114]))
              («Authoring.word»
                x0
                (mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]))))));
    x1

def «Authoring.inatural» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T → List T → List T → T)
    (x6 : List T)
    (x7 : List T)
    (x8 : T → T) =>
    let x9 : T := (let x9 : T := «Prelude.length» x3;
                   let x10 : T → T := (fun (x10 : T) => x5 x10 x6 x7);
                   if («Prelude.and»
                     (Const.lt (leaf 3) x0)
                     («Authoring.word»
                       x2
                       (mk 0 [leaf 115, leaf 117, leaf 99, leaf 99]))).label ≠ 0 then
                     if (Const.eq x9 (leaf 2)).label ≠ 0 then
                       «Base.mapO»
                         (fun (x11 : T) => «Language.mArr» «Authoring.kSucc» ([] : List T) x11)
                         (x10 (leaf 1))
                     else
                       «Prelude.none»
                   else
                     if («Prelude.and»
                       (Const.lt (leaf 3) x0)
                       («Authoring.word»
                         x2
                         (mk 0 [leaf 110,
                           leaf 97,
                           leaf 116,
                           leaf 45,
                           leaf 114,
                           leaf 101,
                           leaf 99]))).label ≠ 0 then
                       if («Prelude.and»
                         (Const.eq x9 (leaf 5))
                         («Authoring.namesOk»
                           x0
                           (leaf 1)
                           («Prelude.at» x3 (leaf 2)))).label ≠ 0 then
                         «Base.bindO»
                           (x10 (leaf 1))
                           (fun (x11 : T) =>
                             «Base.bindO»
                               (x5
                                 (leaf 3)
                                 ((«Prelude.at» x4 (leaf 0)) :: x6)
                                 («Prelude.none» :: x7))
                               (fun (x12 : T) =>
                                 «Base.mapO» («Language.mNatRec» x11 x12) (x10 (leaf 4))))
                       else
                         «Prelude.none»
                     else
                       if («Authoring.isDeclaredRef» x2).label ≠ 0 then
                         if (Const.eq
                           (Const.child x2 (leaf 1))
                           (Const.sub x9 (leaf 1))).label ≠ 0 then
                           «Base.mapO»
                             (fun (x11 : T) =>
                               «Translation.call»
                                 (Const.add («Authoring.declaredAt» x1) (Const.child x2 (leaf 0)))
                                 ([] : List T)
                                 (Const.children x11))
                             («Base.allSomeT»
                               («Base.mapT» x10 («Prelude.drop» (leaf 1) («Base.range» x9))))
                         else
                           «Prelude.none»
                       else
                         x8 (leaf 0));
    x9

def «Authoring.ilogic» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T → T) =>
    let x4 : T := (let x4 : T := «Prelude.at» x2 (leaf 0);
                   let x5 : T := «Prelude.length» x2;
                   if («Authoring.word»
                     x4
                     (mk 0 [leaf 110, leaf 111, leaf 116])).label ≠ 0 then
                     if (Const.eq x5 (leaf 2)).label ≠ 0 then
                       «Base.mapO» («Logic.negL» x0) (x3 (leaf 1))
                     else
                       «Prelude.none»
                   else
                     if («Prelude.or»
                       («Authoring.word» x4 (mk 0 [leaf 97, leaf 110, leaf 100]))
                       («Authoring.word» x4 (mk 0 [leaf 111, leaf 114]))).label ≠ 0 then
                       if (Const.eq x5 (leaf 3)).label ≠ 0 then
                         «Authoring.map2»
                           (if («Authoring.word»
                             x4
                             (mk 0 [leaf 97, leaf 110, leaf 100])).label ≠ 0 then
                             «Formula.conj» x0
                           else
                             «Logic.disjL» x0)
                           (x3 (leaf 1))
                           (x3 (leaf 2))
                       else
                         «Prelude.none»
                     else
                       if («Prelude.and»
                         (Const.eq x5 (leaf 3))
                         («Prelude.or»
                           («Authoring.word» x4 (mk 0 [leaf 97, leaf 108, leaf 108]))
                           («Prelude.or»
                             («Authoring.word»
                               x4
                               (mk 0 [leaf 101, leaf 120, leaf 105, leaf 115, leaf 116, leaf 115]))
                             («Authoring.word»
                               x4
                               (mk 0 [leaf 101,
                                 leaf 120,
                                 leaf 105,
                                 leaf 115,
                                 leaf 116,
                                 leaf 115,
                                 leaf 45,
                                 leaf 117,
                                 leaf 110,
                                 leaf 105,
                                 leaf 113,
                                 leaf 117,
                                 leaf 101]))))).label ≠ 0 then
                         «Base.bindO»
                           («Authoring.itype» x1 («Prelude.at» x2 (leaf 1)))
                           (fun (x6 : T) =>
                             «Base.mapO»
                               (if («Authoring.word»
                                 x4
                                 (mk 0 [leaf 97, leaf 108, leaf 108])).label ≠ 0 then
                                 «Logic.allL» x0 x6
                               else
                                 if («Authoring.word»
                                   x4
                                   (mk 0 [leaf 101,
                                     leaf 120,
                                     leaf 105,
                                     leaf 115,
                                     leaf 116,
                                     leaf 115])).label ≠ 0 then
                                   «Logic.exL» x0 x6
                                 else
                                   «Logic.exuL» x0 x6)
                               (x3 (leaf 2)))
                       else
                         «Prelude.none»);
    x4

def «Authoring.itermStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List (List T → List T → T)) =>
    let x6 : List T →
      List T →
        T := (let x6 : List T := Const.children x4;
              let x7 : T := «Prelude.length» x6;
              let x8 : T := «Prelude.at» x6 (leaf 0);
              fun (x9 : List T) (x10 : List T) =>
                let x11 : T →
                  List T →
                    List T →
                      T := (fun (x11 : T) =>
                  «Authoring/IRs.atOr» «Authoring.failIR» x5 x11);
                let x12 : T → T := (fun (x12 : T) => x11 x12 x9 x10);
                let x13 : List
                  T := «Base.mapT»
                  «Reader.nameOf»
                  (Const.children («Prelude.at» x6 (leaf 2)));
                if («Reader.isAtom» x4).label ≠ 0 then
                  «Authoring.iatom» x0 x2 («Reader.nameOf» x4) x9
                else
                  if («Base.not» («Reader.isList» x4)).label ≠ 0 then
                    if («Prelude.and»
                      («Authoring.isDeclaredRef» x4)
                      (Const.eq (Const.child x4 (leaf 1)) (leaf 0))).label ≠ 0 then
                      «Prelude.some»
                        («Translation.call»
                          (Const.add («Authoring.declaredAt» x2) (Const.child x4 (leaf 0)))
                          ([] : List T)
                          ([] : List T))
                    else
                      «Prelude.none»
                  else
                    if («Authoring.word» x8 «Reader.kwPair»).label ≠ 0 then
                      if (Const.eq x7 (leaf 3)).label ≠ 0 then
                        «Authoring.map2» «Language.mPair» (x12 (leaf 1)) (x12 (leaf 2))
                      else
                        «Prelude.none»
                    else
                      if («Authoring.word» x8 «Reader.kwFst»).label ≠ 0 then
                        if (Const.eq x7 (leaf 2)).label ≠ 0 then
                          «Base.mapO» «Language.mFst» (x12 (leaf 1))
                        else
                          «Prelude.none»
                      else
                        if («Authoring.word» x8 «Reader.kwSnd»).label ≠ 0 then
                          if (Const.eq x7 (leaf 2)).label ≠ 0 then
                            «Base.mapO» «Language.mSnd» (x12 (leaf 1))
                          else
                            «Prelude.none»
                        else
                          if («Authoring.word»
                            x8
                            (mk 0 [leaf 101,
                              leaf 113,
                              leaf 117,
                              leaf 97,
                              leaf 108])).label ≠ 0 then
                            if (Const.eq x7 (leaf 3)).label ≠ 0 then
                              «Authoring.map2» «Language.mEq» (x12 (leaf 1)) (x12 (leaf 2))
                            else
                              «Prelude.none»
                          else
                            if («Authoring.word» x8 «Reader.kwLam»).label ≠ 0 then
                              if («Prelude.and»
                                (Const.eq x7 (leaf 3))
                                («Reader.isList» («Prelude.at» x6 (leaf 1)))).label ≠ 0 then
                                «Authoring.ilam»
                                  x0
                                  x2
                                  x3
                                  (Const.children («Prelude.at» x6 (leaf 1)))
                                  (x11 (leaf 2))
                                  x9
                                  x10
                              else
                                «Prelude.none»
                            else
                              if («Prelude.and»
                                (Const.lt (leaf 2) x0)
                                («Authoring.word»
                                  x8
                                  (mk 0 [leaf 105,
                                    leaf 109,
                                    leaf 112,
                                    leaf 108,
                                    leaf 105,
                                    leaf 101,
                                    leaf 115]))).label ≠ 0 then
                                if (Const.eq x7 (leaf 3)).label ≠ 0 then
                                  «Authoring.map2»
                                    (fun (x14 : T) (x15 : T) =>
                                      «Tactics.impL» («Authoring.connectivesAt» x2) x14 x15)
                                    (x12 (leaf 1))
                                    (x12 (leaf 2))
                                else
                                  «Prelude.none»
                              else
                                if («Authoring.primHead» x8).label ≠ 0 then
                                  «Authoring.iprim» x3 x6 x12
                                else
                                  if («Authoring.word»
                                    x8
                                    (mk 0 [leaf 108,
                                      leaf 105,
                                      leaf 115,
                                      leaf 116,
                                      leaf 45,
                                      leaf 114,
                                      leaf 101,
                                      leaf 99])).label ≠ 0 then
                                    if («Prelude.and»
                                      (Const.eq x7 (leaf 5))
                                      («Authoring.namesOk»
                                        x0
                                        (leaf 2)
                                        («Prelude.at» x6 (leaf 2)))).label ≠ 0 then
                                      «Base.bindO»
                                        (x12 (leaf 1))
                                        (fun (x14 : T) =>
                                          «Base.bindO»
                                            (x11
                                              (leaf 3)
                                              ((«Prelude.at» x13 (leaf 1)) ::
                                                ((«Prelude.at» x13 (leaf 0)) :: x9))
                                              («Prelude.none» :: («Prelude.none» :: x10)))
                                            (fun (x15 : T) =>
                                              «Base.mapO»
                                                («Language.mListRec» x14 x15)
                                                (x12 (leaf 4))))
                                    else
                                      «Prelude.none»
                                  else
                                    if («Authoring.word»
                                      x8
                                      (mk 0 [leaf 114,
                                        leaf 111,
                                        leaf 115,
                                        leaf 101,
                                        leaf 45,
                                        leaf 114,
                                        leaf 101,
                                        leaf 99])).label ≠ 0 then
                                      if («Prelude.and»
                                        (Const.eq x7 (leaf 5))
                                        («Authoring.namesOk»
                                          x0
                                          (leaf 1)
                                          («Prelude.at» x6 (leaf 2)))).label ≠ 0 then
                                        «Base.bindO»
                                          («Authoring.itype» x3 («Prelude.at» x6 (leaf 1)))
                                          (fun (x14 : T) =>
                                            «Base.bindO»
                                              (x11
                                                (leaf 3)
                                                ((«Prelude.at» x13 (leaf 0)) :: x9)
                                                («Prelude.none» :: x10))
                                              (fun (x15 : T) =>
                                                «Base.mapO»
                                                  («Language.mRoseRec» x14 x15)
                                                  (x12 (leaf 4))))
                                      else
                                        «Prelude.none»
                                    else
                                      if («Authoring.word»
                                        x8
                                        (mk 0 [leaf 108, leaf 105, leaf 98])).label ≠ 0 then
                                        «Authoring.ilib» x3 x6 x12
                                      else
                                        if («Authoring.word»
                                          x8
                                          (mk 0 [leaf 107,
                                            leaf 101,
                                            leaf 114,
                                            leaf 110,
                                            leaf 101,
                                            leaf 108])).label ≠ 0 then
                                          if (Const.eq x7 (leaf 2)).label ≠ 0 then
                                            «Authoring.ikernel»
                                              x1
                                              x2
                                              («Prelude.at» x6 (leaf 1))
                                              x9
                                              x10
                                          else
                                            «Prelude.none»
                                        else
                                          «Authoring.inatural»
                                            x0
                                            x2
                                            x8
                                            x6
                                            x13
                                            x11
                                            x9
                                            x10
                                            (fun (_ : T) =>
                                              if («Prelude.and»
                                                (Const.lt (leaf 4) x0)
                                                («Authoring.has»
                                                  («Reader.nameOf» x8)
                                                  «Authoring.formulaNames»)).label ≠ 0 then
                                                «Authoring.ilogic»
                                                  («Authoring.connectivesAt» x2)
                                                  x3
                                                  x6
                                                  x12
                                              else
                                                if (Const.lt (leaf 1) x7).label ≠ 0 then
                                                  «Base.bindO»
                                                    (x12 (leaf 0))
                                                    (fun (x15 : T) =>
                                                      «Base.mapO»
                                                        (fun (x16 : T) =>
                                                          «Tactics.apps» x15 (Const.children x16))
                                                        («Base.allSomeT»
                                                          («Base.mapT»
                                                            x12
                                                            («Prelude.drop»
                                                              (leaf 1)
                                                              («Base.range» x7)))))
                                                else
                                                  «Prelude.none»));
    x6

def «Authoring.iterm» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) (x4 : T) =>
    let x5 : List T →
      List T →
        T := Const.para
      (α := List T → List T → T)
      («Authoring.itermStep» x0 x1 x2 x3)
      x4;
    x5

def «Authoring.readEqn» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T → T) (x4 : T) =>
    let x5 : T := (if («Authoring.form»
      x4
      (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
      (leaf 3)).label ≠ 0 then
      «Base.bindO»
        (x3 (Const.child x4 (leaf 1)))
        (fun (x5 : T) =>
          «Base.bindO»
            (x3 (Const.child x4 (leaf 2)))
            (fun (x6 : T) =>
              let x7 : T := «Derivation.typeIn» x0 x1 x2 x5;
              if («Prelude.and»
                («Prelude.isSome» x7)
                (Const.equal x7 («Derivation.typeIn» x0 x1 x2 x6))).label ≠ 0 then
                «Prelude.some» («Language.mEq» x5 x6)
              else
                «Prelude.none»))
    else
      «Prelude.none»);
    x5

def «Authoring.statement» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Authoring.readFormula» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : T → T)
    (x6 : T) =>
    let x7 : T := (if («Prelude.and»
      (Const.lt (leaf 4) x0)
      x1).label ≠ 0 then
      «Base.bindO»
        (x5 x6)
        (fun (x7 : T) =>
          if (Const.equal
            («Derivation.typeIn» x2 x3 x4 x7)
            («Prelude.some» «Theory.omega»)).label ≠ 0 then
            «Prelude.some» x7
          else
            «Prelude.none»)
    else
      «Authoring.readEqn» x2 x3 x4 x5 x6);
    x7

def «Authoring/OSt.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OSt.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OSt.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OSt.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OSt.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OSt.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OSt.just» x2);
    x2

def «Authoring/OSt.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.binderOk» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := «Prelude.and»
      («Reader.isList» x4)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x4)) (leaf 2))
        (if (x3).label ≠ 0 then
          «Prelude.and»
            («Authoring.bindable» x0 (Const.child x4 (leaf 0)))
            («Prelude.isSome» («Authoring.itype» x2 (Const.child x4 (leaf 1))))
        else
          «Prelude.and»
            («Authoring.declared» (Const.child x4 (leaf 0)))
            («Prelude.isSome»
              («Authoring.kernelType» x1 (Const.child x4 (leaf 1))))));
    x5

def «Authoring.hypOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x2)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x2)) (leaf 2))
        (if (x1).label ≠ 0 then
          «Authoring.bindable» x0 (Const.child x2 (leaf 0))
        else
          «Authoring.declared» (Const.child x2 (leaf 0))));
    x3

def «Authoring.readQuantified» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : T) =>
    let x8 : T := (let x8 : T := «Authoring.form»
                     x7
                     (mk 0 [leaf 102, leaf 111, leaf 114, leaf 97, leaf 108, leaf 108])
                     (leaf 3);
                   let x9 : List
                     T := (if (x8).label ≠ 0 then
                     Const.children (Const.child x7 (leaf 1))
                   else
                     ([] : List T));
                   let x10 : T := (if (x8).label ≠ 0 then
                     Const.child x7 (leaf 2)
                   else
                     x7);
                   let x11 : T := «Prelude.length» (Const.children x10);
                   let x12 : T := «Prelude.and»
                     («Authoring.headed»
                       x10
                       (if («Prelude.and» (Const.lt (leaf 4) x0) x6).label ≠ 0 then
                         mk 0 [leaf 97,
                           leaf 115,
                           leaf 115,
                           leaf 117,
                           leaf 109,
                           leaf 105,
                           leaf 110,
                           leaf 103]
                       else
                         mk 0 [leaf 105,
                           leaf 109,
                           leaf 112,
                           leaf 108,
                           leaf 105,
                           leaf 101,
                           leaf 115]))
                     (Const.lt (leaf 2) x11);
                   let x13 : List
                     T := (if (x12).label ≠ 0 then
                     «Base.take»
                       (Const.sub x11 (leaf 2))
                       («Prelude.drop» (leaf 1) (Const.children x10))
                   else
                     ([] : List T));
                   let x14 : T := (if (x12).label ≠ 0 then
                     «Prelude.at» (Const.children x10) (Const.sub x11 (leaf 1))
                   else
                     x10);
                   let x15 : List
                     T := «Prelude.reverse» («Base.mapT» «Authoring.binderName» x9);
                   let x16 : List T := «Base.mapT» «Authoring.binderName» x13;
                   let x17 : T := «Prelude.length» x5;
                   if («Prelude.and»
                     («Prelude.or»
                       («Base.not» x8)
                       («Prelude.and»
                         («Reader.isList» (Const.child x7 (leaf 1)))
                         («Base.not» («Base.isEmpty» x9))))
                     («Prelude.and»
                       («Base.allT» («Authoring.binderOk» x0 x3 x5 x6) x9)
                       («Prelude.and»
                         («Base.allT» («Authoring.hypOk» x0 x6) x13)
                         («Authoring.distinctFrom»
                           x4
                           («Prelude.append» x15 x16))))).label ≠ 0 then
                     let x18 : List
                       T := «Prelude.reverse»
                       («Base.mapT»
                         (fun (x18 : T) =>
                           «Base.getD»
                             («Authoring.itype» x5 (Const.child x18 (leaf 1)))
                             «Theory.one»)
                         x9);
                     let x19 : List
                       T := «Prelude.reverse»
                       («Base.mapT»
                         (fun (x19 : T) =>
                           «Authoring.kernelType» x3 (Const.child x19 (leaf 1)))
                         x9);
                     let x20 : T →
                       T := (fun (x20 : T) =>
                       if (x6).label ≠ 0 then
                         «Authoring.iterm» x0 x2 x3 x5 x20 x15 x19
                       else
                         «Authoring.ikernel» x2 x3 x20 x15 x19);
                     let x21 : T := «Base.allSomeT»
                       («Base.mapT»
                         (fun (x21 : T) =>
                           «Authoring.readFormula»
                             x0
                             x6
                             x1
                             x17
                             x18
                             x20
                             (Const.child x21 (leaf 1)))
                         x13);
                     let x22 : T := «Authoring.readFormula» x0 x6 x1 x17 x18 x20 x14;
                     if («Prelude.and»
                       («Prelude.isSome» x21)
                       («Prelude.isSome» x22)).label ≠ 0 then
                       «Authoring/OSt.just»
                         («Authoring.statement»
                           (Const.node (leaf 0) x5)
                           (Const.node (leaf 0) x15)
                           (Const.node (leaf 0) x19)
                           (Const.node (leaf 0) x16)
                           («Derivation.mkThm»
                             x17
                             («Language.objs» x18)
                             («Derivation.terms» (Const.children («Prelude.get» x21)))
                             («Prelude.get» x22)))
                     else
                       «Authoring/OSt.nothing»
                   else
                     «Authoring/OSt.nothing»);
    x8

def «Authoring.readStatement» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (if («Prelude.and»
      (Const.lt (leaf 1) x0)
      («Authoring.form»
        x5
        (mk 0 [leaf 105,
          leaf 110,
          leaf 116,
          leaf 101,
          leaf 114,
          leaf 110,
          leaf 97,
          leaf 108])
        (leaf 3))).label ≠ 0 then
      let x6 : List
        T := «Base.mapT»
        «Reader.nameOf»
        (Const.children (Const.child x5 (leaf 1)));
      if («Prelude.and»
        («Reader.isList» (Const.child x5 (leaf 1)))
        («Prelude.and»
          («Base.allT»
            («Authoring.bindable» x0)
            (Const.children (Const.child x5 (leaf 1))))
          («Authoring.distinctFrom» x4 x6))).label ≠ 0 then
        «Authoring.readQuantified»
          x0
          x1
          x2
          x3
          («Prelude.append» x4 x6)
          x6
          (leaf 1)
          (Const.child x5 (leaf 2))
      else
        «Authoring/OSt.nothing»
    else
      «Authoring.readQuantified» x0 x1 x2 x3 x4 ([] : List T) (leaf 0) x5);
    x6

def «Authoring/SRs.single» :=
  fun (x0 : List T →
      List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := (x0 ::
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))));
    x1

def «Authoring/SRs.length» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : T := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := T)
      (fun (_ : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : T) =>
        Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/SRs.append» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x2 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x3 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/SRs.reverse» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)) →
        List
          (List T →
            List T →
              List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x1 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T)) →
           List
             (List T →
               List T →
                 List T → T × (T → List T → List T → List T → List T → T → T → T)))
         (x3 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x1)
      x0
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)));
    x1

def «Authoring/SRs.tail» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.lcase
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      x0
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (_ : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2);
    x1

def «Authoring/SRs.drop» :=
  fun (x0 : T)
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.iter
      (α := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      «Authoring/SRs.tail»
      x1
      x0;
    x2

def «Authoring/SRs.atOr» :=
  fun (x0 : List T →
      List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x2 : T) =>
    let x3 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := Const.lcase
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring/SRs.drop» x2 x1)
      x0
      (fun (x3 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (_ : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x3);
    x3

def «Authoring.failTac» :=
  fun (_ : T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : T)
    (_ : T) =>
    «Prelude.none»

def «Authoring.failSR» :=
  fun (_ : List T) (_ : List T) (_ : List T) =>
    (leaf 0, «Authoring.failTac»)

def «Authoring.foldedId» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (if («Reader.isAtom» x1).label ≠ 0 then
      «Base.mapO»
        (fun (x2 : T) =>
          Const.add («Authoring/LD.length» «Translation.lib») x2)
        («Reader.indexOf» («Reader.nameOf» x1) x0)
    else
      if («Authoring.isDeclaredRef» x1).label ≠ 0 then
        «Prelude.some»
          (Const.add («Authoring.declaredAt» x0) (Const.child x1 (leaf 0)))
      else
        if («Prelude.and»
          («Authoring.form» x1 (mk 0 [leaf 108, leaf 105, leaf 98]) (leaf 2))
          («Reader.isAtom» (Const.child x1 (leaf 1)))).label ≠ 0 then
          «Reader.lookupAbbrev»
            («Reader.nameOf» (Const.child x1 (leaf 1)))
            «Authoring.libTable»
        else
          «Prelude.none»);
    x2

def «Authoring.isFolded» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      (Const.lt (leaf 2) x0)
      («Authoring.headed»
        x1
        (mk 0 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 101, leaf 100]));
    x2

def «Authoring.isUnfold» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Authoring.form»
        x0
        (mk 0 [leaf 117, leaf 110, leaf 102, leaf 111, leaf 108, leaf 100])
        (leaf 2))
      («Authoring.isDeclaredRef» (Const.child x0 (leaf 1)));
    x1

def «Authoring.ruleOk» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (if («Authoring.isFolded» x0 x5).label ≠ 0 then
      «Base.allT»
        (fun (x6 : T) => «Prelude.isSome» («Authoring.foldedId» x1 x6))
        («Prelude.drop» (leaf 1) (Const.children x5))
    else
      if («Authoring.isUnfold» x5).label ≠ 0 then
        leaf 1
      else
        if («Reader.isAtom» x5).label ≠ 0 then
          «Prelude.or»
            («Authoring.has» («Reader.nameOf» x5) x3)
            («Authoring.has» («Reader.nameOf» x5) x4)
        else
          «Prelude.and»
            (Const.lt (leaf 1) x0)
            («Prelude.and»
              («Reader.isList» x5)
              («Prelude.and»
                («Reader.isAtom» (Const.child x5 (leaf 0)))
                («Prelude.and»
                  («Authoring.has» («Reader.nameOf» (Const.child x5 (leaf 0))) x4)
                  («Base.allT»
                    (fun (x6 : T) => «Prelude.isSome» («Authoring.itype» x2 x6))
                    («Prelude.drop» (leaf 1) (Const.children x5)))))));
    x6

def «Authoring.ruleOf» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (let x6 : T := (if («Reader.isAtom» x5).label ≠ 0 then
                     «Reader.indexOf» («Reader.nameOf» x5) x3
                   else
                     «Prelude.none»);
                   if («Authoring.headed»
                     x5
                     (mk 0 [leaf 102,
                       leaf 111,
                       leaf 108,
                       leaf 100,
                       leaf 101,
                       leaf 100])).label ≠ 0 then
                     «Prover.nrBelow»
                       (leaf 0)
                       («Derivation.terms»
                         («Base.mapT»
                           (fun (x7 : T) => «Base.getD» («Authoring.foldedId» x1 x7) (leaf 0))
                           («Prelude.drop» (leaf 1) (Const.children x5))))
                   else
                     if («Authoring.isUnfold» x5).label ≠ 0 then
                       «Prover.nrDelta»
                         (Const.add
                           («Authoring.declaredAt» x1)
                           (Const.child (Const.child x5 (leaf 1)) (leaf 0)))
                     else
                       if («Prelude.isSome» x6).label ≠ 0 then
                         «Prover.nrHyp» («Prelude.get» x6)
                       else
                         «Prover.nrThm»
                           (Const.add
                             x0
                             (Const.add
                               (Const.mul
                                 (leaf 2)
                                 («Base.getD»
                                   («Reader.indexOf»
                                     («Reader.nameOf»
                                       (if («Reader.isAtom» x5).label ≠ 0 then
                                         x5
                                       else
                                         Const.child x5 (leaf 0)))
                                     x4)
                                   (leaf 0)))
                               (leaf 1)))
                           («Language.objs»
                             (if («Reader.isAtom» x5).label ≠ 0 then
                               ([] : List T)
                             else
                               «Base.mapT»
                                 (fun (x7 : T) =>
                                   «Base.getD» («Authoring.itype» x2 x7) «Theory.one»)
                                 («Prelude.drop» (leaf 1) (Const.children x5)))));
    x6

def «Authoring.rulesFrom» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x6 : T) (x7 : List T) =>
        ((«Authoring.ruleOf» x0 x1 x2 x3 x4 x6) :: x7))
      ([] : List T)
      x5;
    x6

def «Authoring.foldedOf» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let x6 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          let x7 : T := Const.lcase
            (α := T)
            (β := T)
            x6
            (leaf 0)
            (fun (x7 : T) (_ : List T) => x7);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x6
            ([] : List T)
            (fun (_ : T) (x9 : List T) => x9);
          if (Const.eq x5 (leaf 0)).label ≠ 0 then
            «Derivation/OTerms.just» x7
          else
            x2
        else
          x2)
      «Derivation/OTerms.nothing»
      x0;
    x1

def «Authoring.refold» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let x5 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     if (Const.lt (leaf 0) x4).label ≠ 0 then
                       «Prover.nrBelow» x4 x0
                     else
                       x1
                   else
                     x1);
    x2

def «Authoring.languageRules» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 4)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let x6 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x6
            (leaf 0)
            (fun (x7 : T) (_ : List T) => x7);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x6
            ([] : List T)
            (fun (_ : T) (x9 : List T) => x9);
          x2
        else
          if (Const.eq (Const.label x3) (leaf 5)).label ≠ 0 then
            let x4 : List T := Const.children x3;
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x4
              (leaf 0)
              (fun (x5 : T) (_ : List T) => x5);
            let x6 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x4
              ([] : List T)
              (fun (_ : T) (x7 : List T) => x7);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x7 : T) (_ : List T) => x7);
            let x8 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x6
              ([] : List T)
              (fun (_ : T) (x9 : List T) => x9);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x8
              (leaf 0)
              (fun (x9 : T) (_ : List T) => x9);
            let x10 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x8
              ([] : List T)
              (fun (_ : T) (x11 : List T) => x11);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x10
              (leaf 0)
              (fun (x11 : T) (_ : List T) => x11);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x10
              ([] : List T)
              (fun (_ : T) (x13 : List T) => x13);
            x2
          else
            if (Const.eq (Const.label x3) (leaf 6)).label ≠ 0 then
              let x4 : List T := Const.children x3;
              let _ : T := Const.lcase
                (α := T)
                (β := T)
                x4
                (leaf 0)
                (fun (x5 : T) (_ : List T) => x5);
              let _ : List
                T := Const.lcase
                (α := T)
                (β := List T)
                x4
                ([] : List T)
                (fun (_ : T) (x7 : List T) => x7);
              x2
            else
              if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                let x4 : List T := Const.children x3;
                let x5 : T := Const.lcase
                  (α := T)
                  (β := T)
                  x4
                  (leaf 0)
                  (fun (x5 : T) (_ : List T) => x5);
                let x6 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x4
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x6
                  (leaf 0)
                  (fun (x7 : T) (_ : List T) => x7);
                let _ : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x6
                  ([] : List T)
                  (fun (_ : T) (x9 : List T) => x9);
                if (Const.eq x5 (leaf 0)).label ≠ 0 then
                  x2
                else
                  ((«Prover.nrBelow» x5 («Derivation.terms» ([] : List T))) :: x2)
              else
                (x1 :: x2))
      ([] : List T)
      x0;
    x1

def «Authoring.rulesIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) =>
    let x3 : List
      T := «Authoring/Rules.append»
      («Prover.prepareRules» x0 x1)
      (let x3 : T := «Authoring.foldedOf» x1;
       if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
         let _ : List T := Const.children x3; x2
       else
         let x4 : List T := Const.children x3;
         let x5 : T := Const.lcase
           (α := T)
           (β := T)
           x4
           (leaf 0)
           (fun (x5 : T) (_ : List T) => x5);
         let _ : List
           T := Const.lcase
           (α := T)
           (β := List T)
           x4
           ([] : List T)
           (fun (_ : T) (x7 : List T) => x7);
         Const.foldr
           (α := T)
           (β := List T)
           (fun (x7 : T) (x8 : List T) => ((«Authoring.refold» x5 x7) :: x8))
           ([] : List T)
           x2);
    x3

def «Authoring.depthOf» :=
  fun (x0 : T) =>
    let x1 : T := (if («Authoring.word»
      x0
      (mk 0 [leaf 104, leaf 101, leaf 97, leaf 100])).label ≠ 0 then
      «Prelude.some» (leaf 0)
    else
      if («Authoring.word»
        x0
        (mk 0 [leaf 119, leaf 101, leaf 97, leaf 107])).label ≠ 0 then
        «Prelude.some» (leaf 1)
      else
        if («Authoring.word»
          x0
          (mk 0 [leaf 111, leaf 112, leaf 101, leaf 110])).label ≠ 0 then
          «Prelude.some» (leaf 2)
        else
          if («Authoring.word»
            x0
            (mk 0 [leaf 102, leaf 117, leaf 108, leaf 108])).label ≠ 0 then
            «Prelude.some» (leaf 3)
          else
            «Prelude.none»);
    x1

def «Authoring.lemmaOf» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (if («Reader.isAtom» x2).label ≠ 0 then
      «Base.mapO»
        (fun (x3 : T) => Const.add x0 (Const.mul (leaf 2) x3))
        («Reader.indexOf» («Reader.nameOf» x2) x1)
    else
      «Prelude.none»);
    x3

def «Authoring.byInstance» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List T)
    (x7 : List T)
    (x8 : T) =>
    let x9 : List T →
      List T →
        T →
          T →
            T := (fun (x9 : List T) (x10 : List T) (x11 : T) (x12 : T) =>
      let x13 : T := «Derivation.thmAt» x1 x3;
      if (Const.eq (Const.label x13) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x13; «Prelude.none»
      else
        let x14 : List T := Const.children x13;
        let x15 : T := Const.lcase
          (α := T)
          (β := T)
          x14
          (leaf 0)
          (fun (x15 : T) (_ : List T) => x15);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x14
          ([] : List T)
          (fun (_ : T) (x17 : List T) => x17);
        «Derivation.bindPT»
          («Derivation.eqParts» («Derivation.thConcl» x15))
          (fun (x17 : T) =>
            let x18 : T := «Tactics.apps»
              («Derivation.instTerm» x4 x5 («Language.p1» x17))
              x6;
            let x19 : T := «Tactics.apps»
              («Derivation.instTerm» x4 x5 («Language.p2» x17))
              x6;
            «Prover.bindNT»
              («Prover.eval» x0 x1 x2 x7 (leaf 4096) x8 x9 x10 x18)
              (fun (x20 : T) =>
                «Prover.bindNT»
                  («Prover.eval» x0 x1 x2 x7 (leaf 4096) x8 x9 x10 x19)
                  (fun (x21 : T) =>
                    «Prover.bindNT»
                      («Prover.eval» x0 x1 x2 x7 (leaf 4096) x8 x9 x10 x11)
                      (fun (x22 : T) =>
                        «Prover.bindNT»
                          («Prover.eval» x0 x1 x2 x7 (leaf 4096) x8 x9 x10 x12)
                          (fun (x23 : T) =>
                            if («Prelude.and»
                              (Const.equal («Prover.nfTerm» x22) («Prover.nfTerm» x20))
                              (Const.equal
                                («Prover.nfTerm» x23)
                                («Prover.nfTerm» x21))).label ≠ 0 then
                              «Prelude.some»
                                («Prover.dNode»
                                  (leaf 23)
                                  ([] : List T)
                                  («Theory.l2»
                                    («Prover.dNode»
                                      (leaf 2)
                                      ([] : List T)
                                      («Theory.l2»
                                        («Prover.mDeriv» («Prover.nfMarked» x22))
                                        («Prover.mDeriv» («Prover.nfMarked» x23))))
                                    («Prover.dNode»
                                      (leaf 24)
                                      («Prelude.single» («Language.mEq» x18 x19))
                                      («Theory.l2»
                                        («Prover.dNode»
                                          (leaf 2)
                                          ([] : List T)
                                          («Theory.l2»
                                            («Prover.mDeriv» («Prover.nfMarked» x20))
                                            («Prover.mDeriv» («Prover.nfMarked» x21))))
                                        («Prover.dNode»
                                          (leaf 18)
                                          ([] : List T)
                                          («Theory.l2»
                                            (Const.foldr
                                              (α := T)
                                              (β := T)
                                              (fun (_ : T) (x25 : T) =>
                                                «Prover.dNode»
                                                  (leaf 2)
                                                  ([] : List T)
                                                  («Theory.l2»
                                                    x25
                                                    («Prover.dNode»
                                                      (leaf 0)
                                                      ([] : List T)
                                                      ([] : List T))))
                                              («Prover.dNode»
                                                (leaf 16)
                                                («Theory.l4»
                                                  x3
                                                  (Const.node (leaf 0) x4)
                                                  (Const.node (leaf 0) x5)
                                                  (leaf 0))
                                                ([] : List T))
                                              x6)
                                            («Prover.dNode»
                                              (leaf 0)
                                              ([] : List T)
                                              ([] : List T))))))))
                            else
                              «Prelude.none»))))));
    x9

def «Authoring.byPointwise» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : List T) (x5 : T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      let x10 : T := «Derivation.thmAt» x1 x3;
      if (Const.eq (Const.label x10) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x10; «Prelude.none»
      else
        let x11 : List T := Const.children x10;
        let x12 : T := Const.lcase
          (α := T)
          (β := T)
          x11
          (leaf 0)
          (fun (x12 : T) (_ : List T) => x12);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x11
          ([] : List T)
          (fun (_ : T) (x14 : List T) => x14);
        «Authoring.byInstance»
          x0
          x1
          x2
          x3
          («Base.mapT» «Theory.x» («Base.range» x2))
          («Base.mapT»
            (fun (x14 : T) => «Language.var» (Const.add x14 (leaf 1)))
            («Base.range» («Prelude.length» («Derivation.thCtx» x12))))
          («Prelude.single» («Language.var» (leaf 0)))
          x4
          x5
          x6
          x7
          x8
          x9);
    x6

def «Authoring.byListFold» :=
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
      Const.lcase
        (α := T)
        (β := T)
        x5
        «Prelude.none»
        (fun (x9 : T) (x10 : List T) =>
          «Base.bindO»
            («Language.listPart» x9)
            (fun (x11 : T) =>
              «Prover.bindHT»
                («Derivation.lowerHyps» x0 x1 x10 x6)
                (fun (x12 : T) =>
                  let x13 : List T := «Prover.termsOf» x12;
                  let x14 : List T := (x9 :: (x11 :: x10));
                  let x15 : List T := «Base.mapT» «Derivation.weaken2» x13;
                  «Base.bindO»
                    (x3
                      x10
                      x13
                      («Prover.instAt» (leaf 0) («Prelude.single» x11) x7)
                      («Prover.instAt» (leaf 0) («Prelude.single» x11) x8))
                    (fun (x16 : T) =>
                      «Base.bindO»
                        (x4
                          x14
                          x15
                          («Derivation.listConsAt» (leaf 1) x11 x7)
                          («Language.subst»
                            x2
                            («Derivation.atVar0» («Derivation.weakenElem» x7))))
                        (fun (x17 : T) =>
                          «Base.mapO»
                            (fun (x18 : T) =>
                              «Prover.dNode»
                                (leaf 20)
                                («Theory.l3» (leaf 0) (leaf 1) x2)
                                («Theory.l3» x16 x17 x18))
                            (x4
                              x14
                              x15
                              («Derivation.listConsAt» (leaf 1) x11 x8)
                              («Language.subst»
                                x2
                                («Derivation.atVar0» («Derivation.weakenElem» x8))))))))));
    x5

def «Authoring.script3» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List T)
    (x8 : List T)
    (x9 : List T) =>
    let x10 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x10 : List T := Const.children x6;
                           let x11 : T := «Prelude.length» x10;
                           let x12 : T := «Prelude.length» x4;
                           let x13 : T := «Prelude.at» x10 (leaf 1);
                           let x14 : T →
                             T := (fun (x14 : T) => «Authoring.iterm» x0 x2 x3 x4 x14 x7 x8);
                           if («Authoring.headed»
                             x6
                             (mk 0 [leaf 112,
                               leaf 111,
                               leaf 105,
                               leaf 110,
                               leaf 116,
                               leaf 119,
                               leaf 105,
                               leaf 115,
                               leaf 101])).label ≠ 0 then
                             let x15 : T := «Authoring.lemmaOf» x1 x5 x13;
                             («Prelude.and»
                               (Const.lt (leaf 2) x11)
                               («Prelude.and»
                                 («Prelude.isSome» x15)
                                 («Prelude.and»
                                   («Prelude.isSome»
                                     («Authoring.depthOf» («Prelude.at» x10 (leaf 2))))
                                   («Base.allT»
                                     («Authoring.ruleOk» (leaf 2) x3 x4 x9 x5)
                                     («Prelude.drop» (leaf 3) x10)))),
                               fun (x16 : T) (x17 : List T) (x18 : List T) =>
                                 «Authoring.byPointwise»
                                   x16
                                   x17
                                   x12
                                   («Base.getD» x15 (leaf 0))
                                   («Authoring.rulesIn»
                                     x17
                                     («Authoring.rulesFrom»
                                       x1
                                       x3
                                       x4
                                       x9
                                       x5
                                       («Prelude.drop» (leaf 3) x10))
                                     x18)
                                   («Base.getD»
                                     («Authoring.depthOf» («Prelude.at» x10 (leaf 2)))
                                     (leaf 0)))
                           else
                             if («Authoring.form»
                               x6
                               (mk 0 [leaf 109,
                                 leaf 97,
                                 leaf 115,
                                 leaf 107,
                                 leaf 45,
                                 leaf 114,
                                 leaf 101,
                                 leaf 119,
                                 leaf 114,
                                 leaf 105,
                                 leaf 116,
                                 leaf 101])
                               (leaf 12)).label ≠ 0 then
                               let x15 : T := «Authoring.itype» x4 x13;
                               let x16 : T := «Authoring.itype» x4 («Prelude.at» x10 (leaf 2));
                               let x17 : T := «Authoring.lemmaOf» x1 x5 («Prelude.at» x10 (leaf 3));
                               let x18 : T := «Prelude.at» x10 (leaf 4);
                               let x19 : T := «Authoring.lemmaOf»
                                 x1
                                 x5
                                 (if («Reader.isAtom» x18).label ≠ 0 then
                                   x18
                                 else
                                   Const.child x18 (leaf 0));
                               let x20 : T := «Base.allSomeT»
                                 («Base.mapT»
                                   («Authoring.itype» x4)
                                   (if («Reader.isAtom» x18).label ≠ 0 then
                                     ([] : List T)
                                   else
                                     «Prelude.drop» (leaf 1) (Const.children x18)));
                               let x21 : T := «Base.allSomeT»
                                 («Base.mapT» x14 (Const.children («Prelude.at» x10 (leaf 5))));
                               let x22 : T := «Base.allSomeT»
                                 («Base.mapT» x14 («Prelude.drop» (leaf 6) x10));
                               («Prelude.and»
                                 («Prelude.isSome» x15)
                                 («Prelude.and»
                                   («Prelude.isSome» x16)
                                   («Prelude.and»
                                     («Prelude.isSome» x17)
                                     («Prelude.and»
                                       («Prelude.isSome» x19)
                                       («Prelude.and»
                                         («Prelude.isSome» x20)
                                         («Prelude.and»
                                           («Reader.isList» («Prelude.at» x10 (leaf 5)))
                                           («Prelude.and»
                                             («Prelude.isSome» x21)
                                             («Prelude.isSome» x22))))))),
                                 fun (_ : T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : T)
                                   (_ : T) =>
                                   let x30 : List
                                     T := Const.children
                                     («Base.getD» x22 (Const.node (leaf 0) ([] : List T)));
                                   «Prelude.some»
                                     («Tactics.maskRw»
                                       («Base.getD» x15 «Theory.one»)
                                       («Base.getD» x16 «Theory.one»)
                                       («Base.getD» x17 (leaf 0))
                                       («Base.getD» x19 (leaf 0))
                                       (Const.children
                                         («Base.getD» x20 (Const.node (leaf 0) ([] : List T))))
                                       (Const.children
                                         («Base.getD» x21 (Const.node (leaf 0) ([] : List T))))
                                       («Prelude.at» x30 (leaf 0))
                                       («Prelude.at» x30 (leaf 1))
                                       («Prelude.at» x30 (leaf 2))
                                       («Prelude.at» x30 (leaf 3))
                                       («Prelude.at» x30 (leaf 4))
                                       («Prelude.at» x30 (leaf 5))))
                             else
                               (leaf 0, «Authoring.failTac»));
    x10

def «Authoring/Kids.single» :=
  fun (x0 : List (List T)) =>
    let x1 : List (List (List T)) := (x0 :: ([] : List (List (List T))));
    x1

def «Authoring/Kids.length» :=
  fun (x0 : List (List (List T))) =>
    let x1 : T := Const.foldr
      (α := List (List T))
      (β := T)
      (fun (_ : List (List T)) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Kids.append» :=
  fun (x0 : List (List (List T))) (x1 : List (List (List T))) =>
    let x2 : List
      (List
        (List
          T)) := Const.foldr
      (α := List (List T))
      (β := List (List (List T)))
      (fun (x2 : List (List T)) (x3 : List (List (List T))) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Kids.reverse» :=
  fun (x0 : List (List (List T))) =>
    let x1 : List
      (List
        (List
          T)) := Const.foldr
      (α := List (List T))
      (β := List (List (List T)) → List (List (List T)))
      (fun (x1 : List (List T))
         (x2 : List (List (List T)) → List (List (List T)))
         (x3 : List (List (List T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List (List T))) => x1)
      x0
      ([] : List (List (List T)));
    x1

def «Authoring/Kids.tail» :=
  fun (x0 : List (List (List T))) =>
    let x1 : List
      (List
        (List
          T)) := Const.lcase
      (α := List (List T))
      (β := List (List (List T)))
      x0
      ([] : List (List (List T)))
      (fun (_ : List (List T)) (x2 : List (List (List T))) => x2);
    x1

def «Authoring/Kids.drop» :=
  fun (x0 : T) (x1 : List (List (List T))) =>
    let x2 : List
      (List
        (List
          T)) := Const.iter
      (α := List (List (List T)))
      «Authoring/Kids.tail»
      x1
      x0;
    x2

def «Authoring/Kids.atOr» :=
  fun (x0 : List (List T)) (x1 : List (List (List T))) (x2 : T) =>
    let x3 : List
      (List
        T) := Const.lcase
      (α := List (List T))
      (β := List (List T))
      («Authoring/Kids.drop» x2 x1)
      x0
      (fun (x3 : List (List T)) (_ : List (List (List T))) => x3);
    x3

def «Authoring.unnamed» := Const.node (leaf 0) ([] : List T)

def «Authoring.instancesOk» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x1)
      («Base.allT»
        (fun (x2 : T) =>
          «Prelude.and»
            («Reader.isList» x2)
            («Prelude.and»
              (Const.lt (leaf 0) («Prelude.length» (Const.children x2)))
              («Prelude.and»
                («Authoring.bindable» (leaf 3) (Const.child x2 (leaf 0)))
                («Base.allT»
                  (fun (x3 : T) => «Prelude.isSome» (x0 x3))
                  («Prelude.drop» (leaf 1) (Const.children x2))))))
        (Const.children x1));
    x2

def «Authoring.instanceNames» :=
  fun (x0 : T) =>
    let x1 : List
      T := «Base.mapT»
      (fun (x1 : T) => «Reader.nameOf» (Const.child x1 (leaf 0)))
      (Const.children x0);
    x1

def «Authoring.instanceArgs» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : List
      (List
        T) := Const.foldr
      (α := T)
      (β := List (List T))
      (fun (x2 : T) (x3 : List (List T)) =>
        ((«Base.mapT»
          (fun (x4 : T) => «Base.getD» (x0 x4) «Language.mStar»)
          («Prelude.drop» (leaf 1) (Const.children x2))) ::
          x3))
      ([] : List (List T))
      (Const.children x1);
    x2

def «Authoring.withInstance» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T → List T → T → T → T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      let x10 : T := «Derivation.thmAt» x0 x1;
      if (Const.eq (Const.label x10) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x10; «Prelude.none»
      else
        let x11 : List T := Const.children x10;
        let x12 : T := Const.lcase
          (α := T)
          (β := T)
          x11
          (leaf 0)
          (fun (x12 : T) (_ : List T) => x12);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x11
          ([] : List T)
          (fun (_ : T) (x14 : List T) => x14);
        «Derivation.bindPT»
          («Derivation.eqParts» («Derivation.thConcl» x12))
          (fun (x14 : T) =>
            let x15 : T := «Language.mEq»
              («Tactics.apps» («Derivation.instTerm» x2 x3 («Language.p1» x14)) x4)
              («Tactics.apps» («Derivation.instTerm» x2 x3 («Language.p2» x14)) x4);
            «Base.mapO»
              (fun (x16 : T) =>
                «Prover.dNode»
                  (leaf 22)
                  («Prelude.single» x15)
                  («Theory.l2»
                    («Prover.dNode»
                      (leaf 18)
                      ([] : List T)
                      («Theory.l2»
                        (Const.foldr
                          (α := T)
                          (β := T)
                          (fun (_ : T) (x18 : T) =>
                            «Prover.dNode»
                              (leaf 2)
                              ([] : List T)
                              («Theory.l2»
                                x18
                                («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                          («Prover.dNode»
                            (leaf 16)
                            («Theory.l4»
                              x1
                              (Const.node (leaf 0) x2)
                              (Const.node (leaf 0) x3)
                              (leaf 0))
                            ([] : List T))
                          x4)
                        («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                    x16))
              (x5 x6 («Prelude.append» x7 («Prelude.single» x15)) x8 x9)));
    x6

def «Authoring.withCongruence» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «Derivation.bindPT»
        («Language.bindTP» («Prelude.nth» x4 x0) «Derivation.eqParts»)
        (fun (x7 : T) =>
          let x8 : T := «Language.mEq»
            («Language.app» x1 («Language.p1» x7))
            («Language.app» x1 («Language.p2» x7));
          «Base.mapO»
            (fun (x9 : T) =>
              «Prover.dNode»
                (leaf 22)
                («Prelude.single» x8)
                («Theory.l2»
                  («Prover.dNode»
                    (leaf 18)
                    ([] : List T)
                    («Theory.l2»
                      («Prover.dNode»
                        (leaf 2)
                        ([] : List T)
                        («Theory.l2»
                          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))
                          («Prover.dNode» (leaf 17) («Theory.l2» x0 (leaf 0)) ([] : List T))))
                      («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                  x9))
            (x2 x3 («Prelude.append» x4 («Prelude.single» x8)) x5 x6)));
    x3

def «Authoring.withHolds» :=
  fun (x0 : T) (x1 : List T → List T → T → T → T) =>
    let x2 : List T →
      List T →
        T →
          T →
            T := (fun (x2 : List T) (x3 : List T) (x4 : T) (x5 : T) =>
      «Derivation.bindPT»
        («Language.bindTP» («Prelude.nth» x3 x0) «Derivation.eqParts»)
        (fun (x6 : T) =>
          «Base.mapO»
            (fun (x7 : T) =>
              «Prover.dNode»
                (leaf 22)
                («Prelude.single» («Language.p1» x6))
                («Theory.l2»
                  («Prover.dNode»
                    (leaf 23)
                    ([] : List T)
                    («Theory.l2»
                      («Prover.dNode» (leaf 17) («Theory.l2» x0 (leaf 0)) ([] : List T))
                      («Prover.dNode»
                        (leaf 18)
                        ([] : List T)
                        («Theory.l2»
                          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))
                          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))))
                  x7))
            (x1
              x2
              («Prelude.append» x3 («Prelude.single» («Language.p1» x6)))
              x4
              x5)));
    x2

def «Authoring.isCall» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      (Const.eq (Const.label x1) (leaf 11))
      («Prelude.and»
        (Const.eq («Language.mD» x1 (leaf 0)) x0)
        (Const.equal
          («Language.mD» x1 (leaf 1))
          (Const.node (leaf 0) ([] : List T))));
    x2

def «Authoring.callArgs» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := Const.iter
                     (α := T)
                     (fun (x3 : T) =>
                       if («Prelude.isSome» x3).label ≠ 0 then
                         let x4 : T := Const.child («Prelude.get» x3) (leaf 0);
                         if («Language.mIs» (leaf 6) (leaf 2) x4).label ≠ 0 then
                           «Prelude.some»
                             (Const.node
                               (leaf 0)
                               ((«Language.mArg» x4 (leaf 0)) ::
                                 ((«Language.mArg» x4 (leaf 1)) ::
                                   («Prelude.drop» (leaf 1) (Const.children («Prelude.get» x3))))))
                         else
                           «Prelude.none»
                       else
                         «Prelude.none»)
                     («Prelude.some» (Const.node (leaf 0) («Prelude.single» x2)))
                     x1;
                   if («Prelude.isSome» x3).label ≠ 0 then
                     if («Authoring.isCall»
                       x0
                       (Const.child («Prelude.get» x3) (leaf 0))).label ≠ 0 then
                       «Prelude.some»
                         (Const.node
                           (leaf 0)
                           («Prelude.drop» (leaf 1) (Const.children («Prelude.get» x3))))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x3

def «Authoring.testMatches» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Authoring.callArgs» x0 («Prelude.length» x1) x2;
                   «Prelude.and»
                     («Prelude.isSome» x3)
                     («Base.allT»
                       (fun (x4 : T) =>
                         let x5 : T := «Prelude.at» x1 x4;
                         «Prelude.or»
                           («Base.not» («Prelude.isSome» x5))
                           (Const.equal
                             («Prelude.get» x5)
                             («Prelude.at» (Const.children («Prelude.get» x3)) x4)))
                       («Base.range» («Prelude.length» x1))));
    x3

def «Authoring.findTest» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x3 : T) (x4 : T) =>
        if («Authoring.testMatches» x0 x1 x3).label ≠ 0 then
          «Prelude.some» x3
        else
          x4)
      «Prelude.none»
      («Tactics.openSubterms» x2);
    x3

def «Authoring.byTests» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T → List T → List T → T → T → T)
    (x8 : T → List T → List T → T → T → T)
    (x9 : T) =>
    let x10 : List T →
      List T →
        T →
          T →
            T := Const.iter
      (α := T → List T → List T → T → T → T)
      (fun (x10 : T → List T → List T → T → T → T) (x11 : T) =>
        «Tactics.byNF»
          x0
          x1
          x2
          x6
          (leaf 1)
          (fun (x12 : List T) (x13 : List T) (x14 : T) (x15 : T) =>
            let x16 : T := (let x16 : T := «Authoring.findTest» x3 x4 x14;
                            if («Prelude.isSome» x16).label ≠ 0 then
                              x16
                            else
                              «Authoring.findTest» x3 x4 x15);
            if («Prelude.isSome» x16).label ≠ 0 then
              «Tactics.byGeneralize»
                «Translation.treeTy»
                («Prelude.get» x16)
                («Tactics.byTreeSplit»
                  x5
                  (leaf 0)
                  («Tactics.byListSplit»
                    x0
                    x2
                    (leaf 1)
                    (x10 (Const.add x11 (leaf 1)))
                    (x7 x11)))
                x12
                x13
                x14
                x15
            else
              x8 x11 x12 x13 x14 x15))
      x8
      x9
      (leaf 0);
    x10

def «Authoring.script6» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x8 : List T)
    (x9 : List T)
    (x10 : List T) =>
    let x11 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x11 : List T := Const.children x6;
                           let x12 : T := «Prelude.length» x11;
                           let x13 : T := «Prelude.length» x4;
                           let x14 : T := «Prelude.at» x11 (leaf 1);
                           let x15 : T := «Prelude.at» x11 (leaf 2);
                           let x16 : T →
                             List T →
                               List T →
                                 List T →
                                   T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := (fun (x16 : T) =>
                             «Authoring/SRs.atOr» «Authoring.failSR» x7 x16);
                           let x17 : T →
                             T := (fun (x17 : T) => «Authoring.iterm» x0 x2 x3 x4 x17 x8 x9);
                           let x18 : List T →
                             T := (fun (x18 : List T) =>
                             «Authoring.distinctFrom»
                               («Prelude.append» x8 («Prelude.append» x10 x5))
                               x18);
                           let x19 : T →
                             T := (fun (x19 : T) =>
                             if («Reader.isAtom» x19).label ≠ 0 then
                               «Reader.indexOf» («Reader.nameOf» x19) x10
                             else
                               «Prelude.none»);
                           let x20 : T →
                             List
                               T := (fun (x20 : T) =>
                             «Base.mapT» (fun (_ : T) => «Authoring.unnamed») («Base.range» x20));
                           let x21 : T →
                             List
                               T := (fun (x21 : T) =>
                             «Base.mapT» (fun (_ : T) => «Prelude.none») («Base.range» x21));
                           if («Authoring.form»
                             x6
                             (mk 0 [leaf 104, leaf 97, leaf 118, leaf 101])
                             (leaf 6)).label ≠ 0 then
                             let x22 : T := «Authoring.lemmaOf»
                               x1
                               x5
                               (if («Reader.isAtom» x15).label ≠ 0 then
                                 x15
                               else
                                 Const.child x15 (leaf 0));
                             let x23 : T := «Base.allSomeT»
                               («Base.mapT»
                                 («Authoring.itype» x4)
                                 (if («Reader.isAtom» x15).label ≠ 0 then
                                   ([] : List T)
                                 else
                                   «Prelude.drop» (leaf 1) (Const.children x15)));
                             let x24 : T := «Base.allSomeT»
                               («Base.mapT» x17 (Const.children («Prelude.at» x11 (leaf 3))));
                             let x25 : T := «Base.allSomeT»
                               («Base.mapT» x17 (Const.children («Prelude.at» x11 (leaf 4))));
                             let x26 : T ×
                               (T →
                                 List T →
                                   List T →
                                     List T →
                                       List T →
                                         T →
                                           T →
                                             T) := x16
                               (leaf 5)
                               x8
                               x9
                               («Prelude.append» x10 («Prelude.single» («Reader.nameOf» x14)));
                             («Prelude.and»
                               («Authoring.bindable» x0 x14)
                               («Prelude.and»
                                 (x18 («Prelude.single» («Reader.nameOf» x14)))
                                 («Prelude.and»
                                   («Prelude.isSome» x22)
                                   («Prelude.and»
                                     («Prelude.isSome» x23)
                                     («Prelude.and»
                                       («Reader.isList» («Prelude.at» x11 (leaf 3)))
                                       («Prelude.and»
                                         («Prelude.isSome» x24)
                                         («Prelude.and»
                                           («Reader.isList» («Prelude.at» x11 (leaf 4)))
                                           («Prelude.and» («Prelude.isSome» x25) (x26).1))))))),
                               fun (x27 : T) (x28 : List T) (x29 : List T) =>
                                 «Authoring.withInstance»
                                   x28
                                   («Base.getD» x22 (leaf 0))
                                   (Const.children
                                     («Base.getD» x23 (Const.node (leaf 0) ([] : List T))))
                                   (Const.children
                                     («Base.getD» x24 (Const.node (leaf 0) ([] : List T))))
                                   (Const.children
                                     («Base.getD» x25 (Const.node (leaf 0) ([] : List T))))
                                   ((x26).2 x27 x28 x29))
                           else
                             if («Authoring.form»
                               x6
                               (mk 0 [leaf 99,
                                 leaf 111,
                                 leaf 110,
                                 leaf 103,
                                 leaf 114,
                                 leaf 117,
                                 leaf 101,
                                 leaf 110,
                                 leaf 99,
                                 leaf 101])
                               (leaf 4)).label ≠ 0 then
                               let x22 : List T := Const.children x15;
                               let x23 : T := «Reader.nameOf» («Prelude.at» x22 (leaf 0));
                               let x24 : T := «Prelude.at» x22 (leaf 1);
                               let x25 : T := «Authoring.iterm»
                                 x0
                                 x2
                                 x3
                                 x4
                                 («Prelude.at» x22 (leaf 2))
                                 ((«Reader.nameOf» (Const.child x24 (leaf 0))) :: x8)
                                 ((«Authoring.kernelType» x3 (Const.child x24 (leaf 1))) :: x9);
                               let x26 : T ×
                                 (T →
                                   List T →
                                     List T →
                                       List T →
                                         List T →
                                           T →
                                             T →
                                               T) := x16
                                 (leaf 3)
                                 x8
                                 x9
                                 («Prelude.append» x10 («Prelude.single» x23));
                               («Prelude.and»
                                 («Prelude.isSome» (x19 x14))
                                 («Prelude.and»
                                   («Prelude.and»
                                     («Reader.isList» x15)
                                     (Const.eq («Prelude.length» x22) (leaf 3)))
                                   («Prelude.and»
                                     («Authoring.bindable» x0 («Prelude.at» x22 (leaf 0)))
                                     («Prelude.and»
                                       (x18 («Prelude.single» x23))
                                       («Prelude.and»
                                         («Authoring.ibinder» x0 x4 x24)
                                         («Prelude.and»
                                           (x18
                                             («Prelude.single»
                                               («Reader.nameOf» (Const.child x24 (leaf 0)))))
                                           («Prelude.and» («Prelude.isSome» x25) (x26).1)))))),
                                 fun (x27 : T) (x28 : List T) (x29 : List T) =>
                                   «Authoring.withCongruence»
                                     («Base.getD» (x19 x14) (leaf 0))
                                     («Language.mLam»
                                       («Base.getD»
                                         («Authoring.itype» x4 (Const.child x24 (leaf 1)))
                                         «Theory.one»)
                                       («Base.getD» x25 «Language.mStar»))
                                     ((x26).2 x27 x28 x29))
                             else
                               if («Authoring.form»
                                 x6
                                 (mk 0 [leaf 104, leaf 111, leaf 108, leaf 100, leaf 115])
                                 (leaf 4)).label ≠ 0 then
                                 let x22 : T := «Reader.nameOf» (Const.child x15 (leaf 0));
                                 let x23 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x16
                                   (leaf 3)
                                   x8
                                   x9
                                   («Prelude.append» x10 («Prelude.single» x22));
                                 («Prelude.and»
                                   («Prelude.isSome» (x19 x14))
                                   («Prelude.and»
                                     («Authoring.namesOk» x0 (leaf 1) x15)
                                     («Prelude.and» (x18 («Prelude.single» x22)) (x23).1)),
                                   fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                     «Authoring.withHolds»
                                       («Base.getD» (x19 x14) (leaf 0))
                                       ((x23).2 x24 x25 x26))
                               else
                                 if («Authoring.form»
                                   x6
                                   (mk 0 [leaf 114,
                                     leaf 101,
                                     leaf 100,
                                     leaf 117,
                                     leaf 99,
                                     leaf 101,
                                     leaf 100])
                                   (leaf 3)).label ≠ 0 then
                                   let x22 : T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T → List T → T → T → T) := x16 (leaf 2) x8 x9 x10;
                                   («Prelude.and»
                                     («Prelude.isSome» («Authoring.depthOf» x14))
                                     (x22).1,
                                     fun (x23 : T) (x24 : List T) (x25 : List T) =>
                                       «Tactics.byNF»
                                         x23
                                         x24
                                         x13
                                         x25
                                         («Base.getD» («Authoring.depthOf» x14) (leaf 0))
                                         ((x22).2 x23 x24 x25))
                                 else
                                   if («Authoring.form»
                                     x6
                                     (mk 0 [leaf 116,
                                       leaf 101,
                                       leaf 115,
                                       leaf 116,
                                       leaf 45,
                                       leaf 99,
                                       leaf 97,
                                       leaf 115,
                                       leaf 101,
                                       leaf 115])
                                     (leaf 6)).label ≠ 0 then
                                     let x22 : List T := Const.children x14;
                                     let x23 : T := (if («Reader.isAtom»
                                       («Prelude.at» x22 (leaf 0))).label ≠ 0 then
                                       «Reader.indexOf»
                                         («Reader.nameOf» («Prelude.at» x22 (leaf 0)))
                                         x3
                                     else
                                       «Prelude.none»);
                                     let x24 : List
                                       T := «Base.mapT»
                                       (fun (x24 : T) =>
                                         if («Authoring.word»
                                           x24
                                           (mk 0 [leaf 97, leaf 110, leaf 121])).label ≠ 0 then
                                           «Prelude.none»
                                         else
                                           «Prelude.some» («Base.getD» (x17 x24) «Language.mStar»))
                                       («Prelude.drop» (leaf 1) x22);
                                     let x25 : T := «Authoring.number» x15;
                                     let x26 : T := «Authoring.lemmaOf»
                                       x1
                                       x5
                                       («Prelude.at» x11 (leaf 3));
                                     let x27 : T →
                                       T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := (fun (x27 : T) =>
                                       x16
                                         (leaf 4)
                                         («Prelude.append»
                                           (x20 (Const.add (Const.mul (leaf 3) x27) (leaf 5)))
                                           x8)
                                         («Prelude.append»
                                           (x21 (Const.add (Const.mul (leaf 3) x27) (leaf 5)))
                                           x9)
                                         («Prelude.append»
                                           x10
                                           («Prelude.single» «Authoring.unnamed»)));
                                     let x28 : T →
                                       T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := (fun (x28 : T) =>
                                       x16
                                         (leaf 5)
                                         («Prelude.append» (x20 (Const.mul (leaf 3) x28)) x8)
                                         («Prelude.append» (x21 (Const.mul (leaf 3) x28)) x9)
                                         x10);
                                     («Prelude.and»
                                       («Reader.isList» x14)
                                       («Prelude.and»
                                         (Const.lt (leaf 1) («Prelude.length» x22))
                                         («Prelude.and»
                                           («Prelude.isSome» x23)
                                           («Prelude.and»
                                             («Base.allT»
                                               (fun (x29 : T) =>
                                                 «Prelude.or»
                                                   («Authoring.word»
                                                     x29
                                                     (mk 0 [leaf 97, leaf 110, leaf 121]))
                                                   («Prelude.isSome» (x17 x29)))
                                               («Prelude.drop» (leaf 1) x22))
                                             («Prelude.and»
                                               («Prelude.isSome» x25)
                                               («Prelude.and»
                                                 («Prelude.isSome» x26)
                                                 («Prelude.and»
                                                   («Base.allT»
                                                     (fun (x29 : T) => (x27 x29).1)
                                                     («Base.range» («Base.getD» x25 (leaf 0))))
                                                   («Base.allT»
                                                     (fun (x29 : T) => (x28 x29).1)
                                                     («Base.range»
                                                       (Const.add
                                                         («Base.getD» x25 (leaf 0))
                                                         (leaf 1)))))))))),
                                       fun (x29 : T) (x30 : List T) (x31 : List T) =>
                                         «Authoring.byTests»
                                           x29
                                           x30
                                           x13
                                           (Const.add
                                             («Authoring/LD.length» «Translation.lib»)
                                             («Base.getD» x23 (leaf 0)))
                                           x24
                                           («Base.getD» x26 (leaf 0))
                                           x31
                                           (fun (x32 : T) => (x27 x32).2 x29 x30 x31)
                                           (fun (x32 : T) => (x28 x32).2 x29 x30 x31)
                                           («Base.getD» x25 (leaf 0)))
                                   else
                                     if («Authoring.form»
                                       x6
                                       (mk 0 [leaf 109,
                                         leaf 97,
                                         leaf 115,
                                         leaf 107,
                                         leaf 45,
                                         leaf 104,
                                         leaf 121,
                                         leaf 112,
                                         leaf 111,
                                         leaf 116,
                                         leaf 104,
                                         leaf 101,
                                         leaf 115,
                                         leaf 101,
                                         leaf 115])
                                       (leaf 5)).label ≠ 0 then
                                       let x22 : T := «Authoring.lemmaOf» x1 x5 x14;
                                       let x23 : T := «Authoring.lemmaOf» x1 x5 x15;
                                       let x24 : T := «Authoring.number»
                                         («Prelude.at» x11 (leaf 3));
                                       let x25 : T →
                                         T ×
                                           (T →
                                             List T →
                                               List T →
                                                 List T →
                                                   List T →
                                                     T →
                                                       T →
                                                         T) := (fun (x25 : T) =>
                                         x16 (leaf 4) x8 x9 («Prelude.append» x10 (x20 x25)));
                                       («Prelude.and»
                                         («Prelude.isSome» x22)
                                         («Prelude.and»
                                           («Prelude.isSome» x23)
                                           («Prelude.and»
                                             («Prelude.isSome» x24)
                                             («Base.allT»
                                               (fun (x26 : T) => (x25 x26).1)
                                               («Base.range»
                                                 (Const.add
                                                   («Base.getD» x24 (leaf 0))
                                                   (leaf 1)))))),
                                         fun (x26 : T) (x27 : List T) (x28 : List T) =>
                                           «Tactics.byMaskSubs»
                                             x26
                                             x27
                                             («Base.getD» x22 (leaf 0))
                                             («Base.getD» x23 (leaf 0))
                                             x28
                                             («Base.getD» x24 (leaf 0))
                                             (fun (x29 : List T) =>
                                               (x25 («Authoring/Rules.length» x29)).2
                                                 x26
                                                 x27
                                                 («Authoring/Rules.append» x29 x28)))
                                     else
                                       if («Authoring.headed»
                                         x6
                                         (mk 0 [leaf 97,
                                           leaf 117,
                                           leaf 116,
                                           leaf 111,
                                           leaf 45,
                                           leaf 99,
                                           leaf 111,
                                           leaf 110,
                                           leaf 100,
                                           leaf 105,
                                           leaf 116,
                                           leaf 105,
                                           leaf 111,
                                           leaf 110,
                                           leaf 115])).label ≠ 0 then
                                         let x22 : T := «Authoring.lemmaOf» x1 x5 x15;
                                         («Prelude.and»
                                           (Const.lt (leaf 2) x12)
                                           («Prelude.and»
                                             («Prelude.isSome» («Authoring.number» x14))
                                             («Prelude.and»
                                               («Prelude.isSome» x22)
                                               («Base.allT»
                                                 («Authoring.ruleOk» x0 x3 x4 x10 x5)
                                                 («Prelude.drop» (leaf 3) x11)))),
                                           fun (x23 : T) (x24 : List T) (x25 : List T) =>
                                             «Tactics.byAutoC»
                                               x23
                                               x24
                                               x13
                                               («Base.getD» x22 (leaf 0))
                                               («Authoring.rulesIn»
                                                 x24
                                                 («Authoring.rulesFrom»
                                                   x1
                                                   x3
                                                   x4
                                                   x10
                                                   x5
                                                   («Prelude.drop» (leaf 3) x11))
                                                 x25)
                                               («Base.getD» («Authoring.number» x14) (leaf 0)))
                                       else
                                         «Authoring.script3» x0 x1 x2 x3 x4 x5 x6 x8 x9 x10);
    x11

def «Authoring.script5» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x8 : List T)
    (x9 : List T)
    (x10 : List T) =>
    let x11 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x11 : List T := Const.children x6;
                           let x12 : T := «Prelude.length» x11;
                           let x13 : T := «Prelude.length» x4;
                           let x14 : T := «Prelude.at» x11 (leaf 1);
                           let x15 : List
                             T := «Base.mapT»
                             «Reader.nameOf»
                             (Const.children («Prelude.at» x11 (leaf 2)));
                           let x16 : T →
                             List T →
                               List T →
                                 List T →
                                   T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := (fun (x16 : T) =>
                             «Authoring/SRs.atOr» «Authoring.failSR» x7 x16);
                           let x17 : T →
                             T := (fun (x17 : T) => «Authoring.iterm» x0 x2 x3 x4 x17 x8 x9);
                           let x18 : List T := «Prelude.drop» (leaf 1) x8;
                           if («Authoring.form»
                             x6
                             (mk 0 [leaf 102,
                               leaf 111,
                               leaf 108,
                               leaf 100,
                               leaf 45,
                               leaf 117,
                               leaf 110,
                               leaf 105,
                               leaf 113,
                               leaf 117,
                               leaf 101,
                               leaf 110,
                               leaf 101,
                               leaf 115,
                               leaf 115])
                             (leaf 6)).label ≠ 0 then
                             let x19 : T := «Authoring.iterm»
                               x0
                               x2
                               x3
                               x4
                               («Prelude.at» x11 (leaf 3))
                               ((«Prelude.at» x15 (leaf 2)) :: ((«Prelude.at» x15 (leaf 0)) :: x18))
                               («Prelude.none» ::
                                 ((«Authoring.listElem» («Prelude.at» x9 (leaf 0))) ::
                                   («Prelude.drop» (leaf 1) x9)));
                             let x20 : T ×
                               (T →
                                 List T →
                                   List T →
                                     List T →
                                       List T →
                                         T →
                                           T →
                                             T) := x16
                               (leaf 4)
                               x18
                               («Prelude.drop» (leaf 1) x9)
                               x10;
                             let x21 : T ×
                               (T →
                                 List T →
                                   List T →
                                     List T →
                                       List T →
                                         T →
                                           T →
                                             T) := x16
                               (leaf 5)
                               ((«Prelude.at» x15 (leaf 1)) :: ((«Prelude.at» x15 (leaf 0)) :: x18))
                               ((«Prelude.at» x9 (leaf 0)) ::
                                 ((«Authoring.listElem» («Prelude.at» x9 (leaf 0))) ::
                                   («Prelude.drop» (leaf 1) x9)))
                               x10;
                             («Prelude.and»
                               («Prelude.and»
                                 («Base.not» («Base.isEmpty» x8))
                                 («Authoring.word» x14 («Prelude.at» x8 (leaf 0))))
                               («Prelude.and»
                                 («Authoring.namesOk» x0 (leaf 3) («Prelude.at» x11 (leaf 2)))
                                 («Prelude.and»
                                   («Authoring.distinctFrom»
                                     («Prelude.append» x18 («Prelude.append» x10 x5))
                                     x15)
                                   («Prelude.and»
                                     («Prelude.isSome» x19)
                                     («Prelude.and» (x20).1 (x21).1)))),
                               fun (x22 : T) (x23 : List T) (x24 : List T) =>
                                 «Authoring.byListFold»
                                   x22
                                   x13
                                   («Base.getD» x19 «Language.mStar»)
                                   ((x20).2 x22 x23 x24)
                                   ((x21).2 x22 x23 x24))
                           else
                             if («Authoring.form»
                               x6
                               (mk 0 [leaf 116,
                                 leaf 114,
                                 leaf 101,
                                 leaf 101,
                                 leaf 45,
                                 leaf 102,
                                 leaf 111,
                                 leaf 108,
                                 leaf 100,
                                 leaf 45,
                                 leaf 117,
                                 leaf 110,
                                 leaf 105,
                                 leaf 113,
                                 leaf 117,
                                 leaf 101,
                                 leaf 110,
                                 leaf 101,
                                 leaf 115,
                                 leaf 115])
                               (leaf 5)).label ≠ 0 then
                               let x19 : T := «Authoring.iterm»
                                 x0
                                 x2
                                 x3
                                 x4
                                 («Prelude.at» x11 (leaf 3))
                                 ((«Prelude.at» x15 (leaf 2)) ::
                                   ((«Prelude.at» x15 (leaf 0)) :: ([] : List T)))
                                 («Prelude.none» :: («Prelude.none» :: ([] : List T)));
                               let x20 : T ×
                                 (T →
                                   List T →
                                     List T →
                                       List T →
                                         List T →
                                           T →
                                             T →
                                               T) := x16
                                 (leaf 4)
                                 ((«Prelude.at» x15 (leaf 1)) ::
                                   ((«Prelude.at» x15 (leaf 0)) :: ([] : List T)))
                                 ((«Base.mapO»
                                   (fun (x20 : T) => Const.node (leaf 4) («Prelude.single» x20))
                                   («Prelude.at» x9 (leaf 0))) ::
                                   («Prelude.none» :: ([] : List T)))
                                 ([] : List T);
                               («Prelude.and»
                                 («Prelude.and»
                                   (Const.eq («Prelude.length» x8) (leaf 1))
                                   («Authoring.word» x14 («Prelude.at» x8 (leaf 0))))
                                 («Prelude.and»
                                   («Base.isEmpty» x10)
                                   («Prelude.and»
                                     («Authoring.namesOk» x0 (leaf 3) («Prelude.at» x11 (leaf 2)))
                                     («Prelude.and»
                                       («Authoring.distinctFrom» x5 x15)
                                       («Prelude.and» («Prelude.isSome» x19) (x20).1)))),
                                 fun (x21 : T) (x22 : List T) (x23 : List T) =>
                                   «Tactics.byRoseIndWith»
                                     x21
                                     x13
                                     («Base.getD» x19 «Language.mStar»)
                                     ((x20).2 x21 x22 x23))
                             else
                               if («Authoring.form»
                                 x6
                                 (mk 0 [leaf 115,
                                   leaf 117,
                                   leaf 99,
                                   leaf 99,
                                   leaf 45,
                                   leaf 112,
                                   leaf 114,
                                   leaf 101,
                                   leaf 100])
                                 (leaf 3)).label ≠ 0 then
                                 let x19 : T := «Authoring.lemmaOf» x1 x5 x14;
                                 let x20 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T → List T → T → T → T) := x16 (leaf 2) x8 x9 x10;
                                 («Prelude.and» («Prelude.isSome» x19) (x20).1,
                                   fun (x21 : T) (x22 : List T) (x23 : List T) =>
                                     «Tactics.bySuccPred»
                                       x22
                                       («Base.getD» x19 (leaf 0))
                                       ((x20).2 x21 x22 x23))
                               else
                                 if («Authoring.form»
                                   x6
                                   (mk 0 [leaf 119,
                                     leaf 105,
                                     leaf 116,
                                     leaf 104,
                                     leaf 45,
                                     leaf 114,
                                     leaf 117,
                                     leaf 108,
                                     leaf 101,
                                     leaf 115])
                                   (leaf 3)).label ≠ 0 then
                                   let x19 : T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T → List T → T → T → T) := x16 (leaf 2) x8 x9 x10;
                                   («Prelude.and»
                                     («Reader.isList» x14)
                                     («Prelude.and»
                                       («Base.allT»
                                         («Authoring.ruleOk» x0 x3 x4 x10 x5)
                                         (Const.children x14))
                                       (x19).1),
                                     fun (x20 : T) (x21 : List T) (x22 : List T) =>
                                       (x19).2
                                         x20
                                         x21
                                         («Authoring.rulesIn»
                                           x21
                                           («Authoring.rulesFrom»
                                             x1
                                             x3
                                             x4
                                             x10
                                             x5
                                             (Const.children x14))
                                           («Authoring.languageRules» x22)))
                                 else
                                   if («Authoring.headed»
                                     x6
                                     (mk 0 [leaf 105,
                                       leaf 110,
                                       leaf 115,
                                       leaf 116,
                                       leaf 97,
                                       leaf 110,
                                       leaf 99,
                                       leaf 101])).label ≠ 0 then
                                     let x19 : T := «Authoring.lemmaOf»
                                       x1
                                       x5
                                       (if («Reader.isAtom» x14).label ≠ 0 then
                                         x14
                                       else
                                         Const.child x14 (leaf 0));
                                     let x20 : T := «Base.allSomeT»
                                       («Base.mapT»
                                         («Authoring.itype» x4)
                                         (if («Reader.isAtom» x14).label ≠ 0 then
                                           ([] : List T)
                                         else
                                           «Prelude.drop» (leaf 1) (Const.children x14)));
                                     let x21 : T := «Base.allSomeT»
                                       («Base.mapT»
                                         x17
                                         (Const.children («Prelude.at» x11 (leaf 2))));
                                     let x22 : T := «Base.allSomeT»
                                       («Base.mapT»
                                         x17
                                         (Const.children («Prelude.at» x11 (leaf 3))));
                                     («Prelude.and»
                                       (Const.lt (leaf 4) x12)
                                       («Prelude.and»
                                         («Prelude.isSome» x19)
                                         («Prelude.and»
                                           («Prelude.isSome» x20)
                                           («Prelude.and»
                                             («Reader.isList» («Prelude.at» x11 (leaf 2)))
                                             («Prelude.and»
                                               («Prelude.isSome» x21)
                                               («Prelude.and»
                                                 («Reader.isList» («Prelude.at» x11 (leaf 3)))
                                                 («Prelude.and»
                                                   («Prelude.isSome» x22)
                                                   («Prelude.and»
                                                     («Prelude.isSome»
                                                       («Authoring.depthOf»
                                                         («Prelude.at» x11 (leaf 4))))
                                                     («Base.allT»
                                                       («Authoring.ruleOk» x0 x3 x4 x10 x5)
                                                       («Prelude.drop» (leaf 5) x11))))))))),
                                       fun (x23 : T) (x24 : List T) (x25 : List T) =>
                                         «Authoring.byInstance»
                                           x23
                                           x24
                                           x13
                                           («Base.getD» x19 (leaf 0))
                                           (Const.children
                                             («Base.getD» x20 (Const.node (leaf 0) ([] : List T))))
                                           (Const.children
                                             («Base.getD» x21 (Const.node (leaf 0) ([] : List T))))
                                           (Const.children
                                             («Base.getD» x22 (Const.node (leaf 0) ([] : List T))))
                                           («Authoring.rulesIn»
                                             x24
                                             («Authoring.rulesFrom»
                                               x1
                                               x3
                                               x4
                                               x10
                                               x5
                                               («Prelude.drop» (leaf 5) x11))
                                             x25)
                                           («Base.getD»
                                             («Authoring.depthOf» («Prelude.at» x11 (leaf 4)))
                                             (leaf 0)))
                                   else
                                     «Authoring.script6» x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10);
    x11

def «Authoring.scriptBits» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T →
      List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x6 : T := «Prelude.length» x1;
                           let x7 : T →
                             List
                               T := (fun (x7 : T) =>
                             «Base.mapT» (fun (_ : T) => «Authoring.unnamed») («Base.range» x7));
                           let x8 : T := (if («Reader.isAtom»
                             («Prelude.at» x1 (leaf 1))).label ≠ 0 then
                             «Reader.indexOf» («Reader.nameOf» («Prelude.at» x1 (leaf 1))) x3
                           else
                             «Prelude.none»);
                           let x9 : T := «Authoring.number» («Prelude.at» x1 (leaf 2));
                           let x10 : T →
                             T →
                               T ×
                                 (T →
                                   List T →
                                     List T →
                                       List T →
                                         List T →
                                           T →
                                             T →
                                               T) := (fun (x10 : T) (x11 : T) =>
                             x2
                               x10
                               («Prelude.append» (x7 (Const.mul (leaf 3) x11)) x3)
                               («Prelude.append»
                                 («Base.mapT»
                                   (fun (_ : T) => «Prelude.none»)
                                   («Base.range» (Const.mul (leaf 3) x11)))
                                 x4)
                               («Prelude.append» x5 (x7 x11)));
                           let x11 : List
                             T := «Base.range» (Const.div (Const.sub x6 (leaf 4)) (leaf 2));
                           let x12 : T →
                             List
                               T := (fun (x12 : T) =>
                             «Base.mapT»
                               (fun (x13 : T) => «Base.getD» («Authoring.number» x13) (leaf 0))
                               (Const.children
                                 («Prelude.at» x1 (Const.add (leaf 4) (Const.mul (leaf 2) x12)))));
                           let x13 : T →
                             T := (fun (x13 : T) =>
                             Const.foldr
                               (α := T)
                               (β := T)
                               (fun (x14 : T) (x15 : T) =>
                                 if («Authoring.has» x13 (x12 x14)).label ≠ 0 then
                                   Const.add (leaf 5) (Const.mul (leaf 2) x14)
                                 else
                                   x15)
                               (leaf 3)
                               x11);
                           («Prelude.and»
                             (Const.lt (leaf 3) x6)
                             («Prelude.and»
                               (Const.eq (Const.mod x6 (leaf 2)) (leaf 0))
                               («Prelude.and»
                                 («Prelude.isSome» x8)
                                 («Prelude.and»
                                   («Prelude.isSome» x9)
                                   («Prelude.and»
                                     («Base.allT»
                                       (fun (x14 : T) => (x10 (leaf 3) x14).1)
                                       («Base.range»
                                         (Const.add («Base.getD» x9 (leaf 0)) (leaf 1))))
                                     («Base.allT»
                                       (fun (x14 : T) =>
                                         let x15 : T := «Prelude.at»
                                           x1
                                           (Const.add (leaf 4) (Const.mul (leaf 2) x14));
                                         «Prelude.and»
                                           («Reader.isList» x15)
                                           («Base.allT»
                                             (fun (x16 : T) =>
                                               «Prelude.and»
                                                 («Prelude.isSome» («Authoring.number» x16))
                                                 (let x17 : T := Const.log2
                                                    (Const.add
                                                      («Base.getD»
                                                        («Authoring.number» x16)
                                                        (leaf 0))
                                                      (leaf 1));
                                                  «Prelude.and»
                                                    (Const.lt x17 («Base.getD» x9 (leaf 0)))
                                                    (x10
                                                      (Const.add (leaf 5) (Const.mul (leaf 2) x14))
                                                      x17).1))
                                             (Const.children x15)))
                                       x11))))),
                             fun (x14 : T) (x15 : List T) (x16 : List T) =>
                               Const.foldr
                                 (α := T)
                                 (β := T → T → List T → List T → T → T → T)
                                 (fun (x17 : T)
                                    (x18 : T → T → List T → List T → T → T → T)
                                    (x19 : T)
                                    (x20 : T) =>
                                   let x21 : T := Const.iter
                                     (α := T)
                                     (fun (x21 : T) => Const.mul (leaf 2) x21)
                                     (leaf 1)
                                     x17;
                                   «Tactics.byListSplit»
                                     x14
                                     x0
                                     x19
                                     ((x10 (x13 (Const.sub x20 (leaf 1))) x17).2 x14 x15 x16)
                                     («Tactics.bySplit2»
                                       (leaf 3)
                                       (leaf 4)
                                       (leaf 1)
                                       (x18 (leaf 1) (Const.add x20 x21))
                                       (x18 (leaf 1) (Const.add x20 (Const.mul (leaf 2) x21)))))
                                 (fun (_ : T) (_ : T) =>
                                   (x10 (leaf 3) («Base.getD» x9 (leaf 0))).2 x14 x15 x16)
                                 («Base.range» («Base.getD» x9 (leaf 0)))
                                 («Base.getD» x8 (leaf 0))
                                 (leaf 1)));
    x6

def «Authoring.script4» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x8 : List T)
    (x9 : List T)
    (x10 : List T) =>
    let x11 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x11 : List T := Const.children x6;
                           let x12 : T := «Prelude.length» x4;
                           let x13 : T := «Authoring.connectivesAt» x3;
                           let x14 : T := «Prelude.at» x11 (leaf 1);
                           let x15 : T := «Prelude.at» x11 (leaf 2);
                           let x16 : T := «Prelude.at» x11 (leaf 3);
                           let x17 : T →
                             List T →
                               List T →
                                 List T →
                                   T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := (fun (x17 : T) =>
                             «Authoring/SRs.atOr» «Authoring.failSR» x7 x17);
                           let x18 : T →
                             T := (fun (x18 : T) => «Authoring.iterm» x0 x2 x3 x4 x18 x8 x9);
                           let x19 : List T →
                             T := (fun (x19 : List T) =>
                             «Authoring.distinctFrom»
                               («Prelude.append» x8 («Prelude.append» x10 x5))
                               x19);
                           let x20 : T →
                             T := (fun (x20 : T) =>
                             if («Reader.isAtom» x20).label ≠ 0 then
                               «Reader.indexOf» («Reader.nameOf» x20) x10
                             else
                               «Prelude.none»);
                           let x21 : List T →
                             List
                               T := (fun (x21 : List T) =>
                             «Base.mapT»
                               (fun (x22 : T) =>
                                 if («Authoring.has» x22 x21).label ≠ 0 then
                                   «Authoring.unnamed»
                                 else
                                   x22)
                               x10);
                           let x22 : T →
                             List
                               T := (fun (x22 : T) =>
                             «Base.mapT» (fun (_ : T) => «Authoring.unnamed») («Base.range» x22));
                           if («Authoring.form»
                             x6
                             (mk 0 [leaf 116,
                               leaf 114,
                               leaf 101,
                               leaf 101,
                               leaf 45,
                               leaf 105,
                               leaf 110,
                               leaf 100,
                               leaf 117,
                               leaf 99,
                               leaf 116,
                               leaf 105,
                               leaf 111,
                               leaf 110])
                             (leaf 4)).label ≠ 0 then
                             let x23 : List T := «Base.mapT» «Reader.nameOf» (Const.children x15);
                             let x24 : List T := «Prelude.drop» (leaf 1) x8;
                             let x25 : T ×
                               (T →
                                 List T →
                                   List T →
                                     List T →
                                       List T →
                                         T →
                                           T →
                                             T) := x17
                               (leaf 3)
                               ((«Prelude.at» x23 (leaf 1)) :: ((«Prelude.at» x23 (leaf 0)) :: x24))
                               ((«Base.mapO»
                                 (fun (x25 : T) => Const.node (leaf 4) («Prelude.single» x25))
                                 («Prelude.at» x9 (leaf 0))) ::
                                 («Prelude.none» :: («Prelude.drop» (leaf 1) x9)))
                               («Prelude.single» («Prelude.at» x23 (leaf 2)));
                             («Prelude.and»
                               («Prelude.and»
                                 («Base.not» («Base.isEmpty» x8))
                                 («Authoring.word» x14 («Prelude.at» x8 (leaf 0))))
                               («Prelude.and»
                                 («Base.isEmpty» x10)
                                 («Prelude.and»
                                   («Authoring.namesOk» x0 (leaf 3) x15)
                                   («Prelude.and»
                                     («Authoring.distinctFrom» («Prelude.append» x24 x5) x23)
                                     (x25).1))),
                               fun (x26 : T) (x27 : List T) (x28 : List T) =>
                                 «Prover.byRoseIndHyp»
                                   (leaf 2)
                                   (leaf 0)
                                   (leaf 1)
                                   ((x25).2 x26 x27 x28))
                           else
                             if («Authoring.form»
                               x6
                               (mk 0 [leaf 99,
                                 leaf 104,
                                 leaf 105,
                                 leaf 108,
                                 leaf 100,
                                 leaf 45,
                                 leaf 104,
                                 leaf 121,
                                 leaf 112,
                                 leaf 111,
                                 leaf 116,
                                 leaf 104,
                                 leaf 101,
                                 leaf 115,
                                 leaf 101,
                                 leaf 115])
                               (leaf 5)).label ≠ 0 then
                               let x23 : List T := Const.children x16;
                               let x24 : List
                                 T := Const.foldr
                                 (α := T)
                                 (β := List T)
                                 (fun (x24 : T) (x25 : List T) =>
                                   «Prelude.append» («Authoring.instanceNames» x24) x25)
                                 ([] : List T)
                                 x23;
                               let x25 : List
                                 T := Const.foldr
                                 (α := T)
                                 (β := List T)
                                 (fun (x25 : T) (x26 : List T) =>
                                   «Prelude.append»
                                     (x22
                                       (Const.add (leaf 2) («Prelude.length» (Const.children x25))))
                                     x26)
                                 ([] : List T)
                                 x23;
                               let x26 : T ×
                                 (T →
                                   List T →
                                     List T →
                                       List T →
                                         List T →
                                           T →
                                             T →
                                               T) := x17
                                 (leaf 4)
                                 x8
                                 x9
                                 («Prelude.append» x10 («Prelude.append» x25 x24));
                               let x27 : List
                                 (List
                                   (List
                                     T)) := Const.foldr
                                 (α := T)
                                 (β := List (List (List T)))
                                 (fun (x27 : T) (x28 : List (List (List T))) =>
                                   ((«Authoring.instanceArgs» x18 x27) :: x28))
                                 ([] : List (List (List T)))
                                 x23;
                               («Prelude.and»
                                 («Prelude.isSome» («Authoring.depthOf» x14))
                                 («Prelude.and»
                                   («Prelude.isSome» (x20 x15))
                                   («Prelude.and»
                                     («Reader.isList» x16)
                                     («Prelude.and»
                                       («Base.not» («Base.isEmpty» x23))
                                       («Prelude.and»
                                         («Base.allT» («Authoring.instancesOk» x18) x23)
                                         («Prelude.and» (x19 x24) (x26).1))))),
                                 fun (x28 : T) (x29 : List T) (x30 : List T) =>
                                   «Tactics.withChildHyps»
                                     x28
                                     x29
                                     x12
                                     x30
                                     («Base.getD» (x20 x15) (leaf 0))
                                     («Base.range» («Prelude.length» x23))
                                     (fun (x31 : T) =>
                                       «Authoring/Kids.atOr» ([] : List (List T)) x27 x31)
                                     (fun (x31 : List T) =>
                                       «Tactics.withWeakHyps»
                                         x28
                                         x29
                                         x12
                                         x30
                                         x31
                                         (fun (_ : List T) => (x26).2 x28 x29 x30)
                                         («Base.getD» («Authoring.depthOf» x14) (leaf 0))))
                             else
                               if («Authoring.form»
                                 x6
                                 (mk 0 [leaf 105,
                                   leaf 110,
                                   leaf 115,
                                   leaf 116,
                                   leaf 97,
                                   leaf 110,
                                   leaf 99,
                                   leaf 101,
                                   leaf 115])
                                 (leaf 5)).label ≠ 0 then
                                 let x23 : List T := «Authoring.instanceNames» x16;
                                 let x24 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x17
                                   (leaf 4)
                                   x8
                                   x9
                                   («Prelude.append»
                                     x10
                                     («Prelude.append» (x22 («Prelude.length» x23)) x23));
                                 («Prelude.and»
                                   («Prelude.isSome» («Authoring.depthOf» x14))
                                   («Prelude.and»
                                     («Prelude.isSome» (x20 x15))
                                     («Prelude.and»
                                       («Authoring.instancesOk» x18 x16)
                                       («Prelude.and»
                                         («Base.not» («Base.isEmpty» x23))
                                         («Prelude.and» (x19 x23) (x24).1)))),
                                   fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                     «Tactics.withInsts»
                                       x25
                                       x26
                                       x12
                                       x27
                                       («Base.getD» (x20 x15) (leaf 0))
                                       («Authoring.instanceArgs» x18 x16)
                                       (fun (_ : List T) => (x24).2 x25 x26 x27)
                                       («Base.getD» («Authoring.depthOf» x14) (leaf 0)))
                               else
                                 if («Authoring.form»
                                   x6
                                   (mk 0 [leaf 97,
                                     leaf 115,
                                     leaf 115,
                                     leaf 117,
                                     leaf 109,
                                     leaf 101])
                                   (leaf 3)).label ≠ 0 then
                                   let x23 : T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := x17
                                     (leaf 2)
                                     x8
                                     x9
                                     («Prelude.append»
                                       x10
                                       («Theory.l2» «Authoring.unnamed» («Reader.nameOf» x14)));
                                   («Prelude.and»
                                     («Authoring.bindable» x0 x14)
                                     («Prelude.and»
                                       (x19 («Prelude.single» («Reader.nameOf» x14)))
                                       (x23).1),
                                     fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                       «Tactics.byImpI» x24 x25 x13 (leaf 0) ((x23).2 x24 x25 x26))
                                 else
                                   if («Authoring.form»
                                     x6
                                     (mk 0 [leaf 109,
                                       leaf 111,
                                       leaf 100,
                                       leaf 117,
                                       leaf 115,
                                       leaf 45,
                                       leaf 112,
                                       leaf 111,
                                       leaf 110,
                                       leaf 101,
                                       leaf 110,
                                       leaf 115])
                                     (leaf 4)).label ≠ 0 then
                                     let x23 : List
                                       T := «Base.mapT» «Reader.nameOf» (Const.children x15);
                                     let x24 : T ×
                                       (T →
                                         List T →
                                           List T →
                                             List T →
                                               List T →
                                                 T →
                                                   T →
                                                     T) := x17
                                       (leaf 3)
                                       x8
                                       x9
                                       («Prelude.append» (x21 x23) x23);
                                     («Prelude.and»
                                       («Prelude.isSome» (x20 x14))
                                       («Prelude.and»
                                         («Reader.isList» x15)
                                         («Prelude.and»
                                           («Base.not» («Base.isEmpty» x23))
                                           («Prelude.and»
                                             («Base.allT»
                                               (fun (x25 : T) => «Prelude.isSome» (x20 x25))
                                               (Const.children x15))
                                             («Prelude.and»
                                               («Authoring.distinctFrom» ([] : List T) x23)
                                               (x24).1)))),
                                       fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                         «Tactics.withImpElim»
                                           x13
                                           (leaf 0)
                                           («Base.getD» (x20 x14) (leaf 0))
                                           («Base.mapT»
                                             (fun (x28 : T) =>
                                               «Base.getD» («Reader.indexOf» x28 x10) (leaf 0))
                                             x23)
                                           (fun (_ : List T) => (x24).2 x25 x26 x27))
                                   else
                                     if («Authoring.form»
                                       x6
                                       (mk 0 [leaf 114,
                                         leaf 101,
                                         leaf 118,
                                         leaf 101,
                                         leaf 114,
                                         leaf 116,
                                         leaf 45,
                                         leaf 99,
                                         leaf 97,
                                         leaf 115,
                                         leaf 101,
                                         leaf 115])
                                       (leaf 6)).label ≠ 0 then
                                       let x23 : List
                                         T := «Base.mapT» «Reader.nameOf» (Const.children x16);
                                       let x24 : T := «Reader.nameOf» x14;
                                       let x25 : T := (if («Reader.isAtom» x15).label ≠ 0 then
                                         «Reader.indexOf» («Reader.nameOf» x15) x8
                                       else
                                         «Prelude.none»);
                                       let x26 : T := «Prelude.at» x9 («Base.getD» x25 (leaf 0));
                                       let x27 : List T := x21 («Prelude.single» x24);
                                       let x28 : T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := x17
                                         (leaf 4)
                                         x8
                                         x9
                                         («Prelude.append»
                                           x27
                                           («Theory.l2» «Authoring.unnamed» x24));
                                       let x29 : T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := x17
                                         (leaf 5)
                                         ((«Prelude.at» x23 (leaf 1)) ::
                                           ((«Prelude.at» x23 (leaf 0)) :: x8))
                                         (x26 :: ((«Authoring.listElem» x26) :: x9))
                                         («Prelude.append»
                                           x27
                                           («Theory.l3»
                                             «Authoring.unnamed»
                                             «Authoring.unnamed»
                                             x24));
                                       («Prelude.and»
                                         («Prelude.isSome» (x20 x14))
                                         («Prelude.and»
                                           («Prelude.isSome» x25)
                                           («Prelude.and»
                                             («Authoring.namesOk» x0 (leaf 2) x16)
                                             («Prelude.and»
                                               (x19 x23)
                                               («Prelude.and» (x28).1 (x29).1)))),
                                         fun (x30 : T) (x31 : List T) (x32 : List T) =>
                                           «Tactics.revertCase»
                                             x30
                                             x12
                                             x13
                                             (leaf 0)
                                             («Base.getD» x25 (leaf 0))
                                             («Base.getD» (x20 x14) (leaf 0))
                                             ((x28).2 x30 x31 x32)
                                             ((x29).2 x30 x31 x32))
                                     else
                                       if («Authoring.form»
                                         x6
                                         (mk 0 [leaf 102, leaf 105, leaf 114, leaf 115, leaf 116])
                                         (leaf 3)).label ≠ 0 then
                                         let x23 : T ×
                                           (T →
                                             List T →
                                               List T →
                                                 List T →
                                                   List T → T → T → T) := x17 (leaf 1) x8 x9 x10;
                                         let x24 : T ×
                                           (T →
                                             List T →
                                               List T →
                                                 List T →
                                                   List T → T → T → T) := x17 (leaf 2) x8 x9 x10;
                                         («Prelude.and» (x23).1 (x24).1,
                                           fun (x25 : T)
                                             (x26 : List T)
                                             (x27 : List T)
                                             (x28 : List T)
                                             (x29 : List T)
                                             (x30 : T)
                                             (x31 : T) =>
                                             let x32 : T := (x23).2 x25 x26 x27 x28 x29 x30 x31;
                                             if («Prelude.isSome» x32).label ≠ 0 then
                                               x32
                                             else
                                               (x24).2 x25 x26 x27 x28 x29 x30 x31)
                                       else
                                         if («Authoring.headed»
                                           x6
                                           (mk 0 [leaf 98,
                                             leaf 105,
                                             leaf 116,
                                             leaf 115,
                                             leaf 45,
                                             leaf 99,
                                             leaf 97,
                                             leaf 115,
                                             leaf 101,
                                             leaf 115])).label ≠ 0 then
                                           «Authoring.scriptBits» x12 x11 x17 x8 x9 x10
                                         else
                                           «Authoring.script5» x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10);
    x11

def «Authoring.script2» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x8 : List T)
    (x9 : List T)
    (x10 : List T) =>
    let x11 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x11 : List T := Const.children x6;
                           let x12 : T := «Prelude.length» x11;
                           let x13 : T := «Prelude.length» x4;
                           let x14 : T := «Prelude.at» x11 (leaf 1);
                           let x15 : List
                             T := «Base.mapT»
                             «Reader.nameOf»
                             (Const.children («Prelude.at» x11 (leaf 2)));
                           let x16 : T →
                             List T →
                               List T →
                                 List T →
                                   T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := (fun (x16 : T) =>
                             «Authoring/SRs.atOr» «Authoring.failSR» x7 x16);
                           let x17 : T →
                             List
                               T := (fun (x17 : T) =>
                             «Authoring.rulesFrom» x1 x3 x4 x10 x5 («Prelude.drop» x17 x11));
                           let x18 : T →
                             T := (fun (x18 : T) =>
                             «Base.allT»
                               («Authoring.ruleOk» (leaf 2) x3 x4 x10 x5)
                               («Prelude.drop» x18 x11));
                           let x19 : List T →
                             List T →
                               T := (fun (x19 : List T) (x20 : List T) =>
                             «Authoring.distinctFrom»
                               («Prelude.append» x19 («Prelude.append» x10 x5))
                               x20);
                           let x20 : T := «Reader.indexOf» («Reader.nameOf» x14) x8;
                           let x21 : T := «Authoring.number» («Prelude.at» x11 (leaf 4));
                           if («Authoring.headed»
                             x6
                             (mk 0 [leaf 102,
                               leaf 111,
                               leaf 108,
                               leaf 100,
                               leaf 45,
                               leaf 105,
                               leaf 110,
                               leaf 100,
                               leaf 117,
                               leaf 99,
                               leaf 116,
                               leaf 105,
                               leaf 111,
                               leaf 110])).label ≠ 0 then
                             let x22 : List T := «Prelude.drop» (leaf 1) x8;
                             let x23 : T := «Authoring.iterm»
                               x0
                               x2
                               x3
                               x4
                               («Prelude.at» x11 (leaf 3))
                               ((«Prelude.at» x15 (leaf 1)) :: ((«Prelude.at» x15 (leaf 0)) :: x22))
                               («Prelude.none» :: («Prelude.none» :: («Prelude.drop» (leaf 1) x9)));
                             («Prelude.and»
                               (Const.lt (leaf 4) x12)
                               («Prelude.and»
                                 («Prelude.and»
                                   («Base.not» («Base.isEmpty» x8))
                                   («Authoring.word» x14 («Prelude.at» x8 (leaf 0))))
                                 («Prelude.and»
                                   («Authoring.namesOk» x0 (leaf 2) («Prelude.at» x11 (leaf 2)))
                                   («Prelude.and»
                                     (x19 x22 x15)
                                     («Prelude.and»
                                       («Prelude.isSome» x23)
                                       («Prelude.and» («Prelude.isSome» x21) (x18 (leaf 5))))))),
                               fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                 «Prover.byListInd»
                                   x24
                                   x25
                                   x13
                                   (leaf 0)
                                   (leaf 1)
                                   («Base.getD» x23 «Language.mStar»)
                                   («Authoring.rulesIn» x25 (x17 (leaf 5)) x26)
                                   («Base.getD» x21 (leaf 0)))
                           else
                             if («Authoring.headed»
                               x6
                               (mk 0 [leaf 116,
                                 leaf 114,
                                 leaf 101,
                                 leaf 101,
                                 leaf 45,
                                 leaf 102,
                                 leaf 111,
                                 leaf 108,
                                 leaf 100,
                                 leaf 45,
                                 leaf 105,
                                 leaf 110,
                                 leaf 100,
                                 leaf 117,
                                 leaf 99,
                                 leaf 116,
                                 leaf 105,
                                 leaf 111,
                                 leaf 110])).label ≠ 0 then
                               let x22 : T := «Authoring.iterm»
                                 x0
                                 x2
                                 x3
                                 x4
                                 («Prelude.at» x11 (leaf 3))
                                 ((«Prelude.at» x15 (leaf 1)) ::
                                   ((«Prelude.at» x15 (leaf 0)) :: ([] : List T)))
                                 («Prelude.none» :: («Prelude.none» :: ([] : List T)));
                               («Prelude.and»
                                 (Const.lt (leaf 4) x12)
                                 («Prelude.and»
                                   («Prelude.and»
                                     (Const.eq («Prelude.length» x8) (leaf 1))
                                     («Authoring.word» x14 («Prelude.at» x8 (leaf 0))))
                                   («Prelude.and»
                                     («Base.isEmpty» x10)
                                     («Prelude.and»
                                       («Authoring.namesOk» x0 (leaf 2) («Prelude.at» x11 (leaf 2)))
                                       («Prelude.and»
                                         (x19 ([] : List T) x15)
                                         («Prelude.and»
                                           («Prelude.isSome» x22)
                                           («Prelude.and»
                                             («Prelude.isSome» x21)
                                             (x18 (leaf 5)))))))),
                                 fun (x23 : T)
                                   (x24 : List T)
                                   (x25 : List T)
                                   (x26 : List T)
                                   (_ : List T)
                                   (x28 : T)
                                   (x29 : T) =>
                                   «Prover.byRoseInd»
                                     x23
                                     x24
                                     x13
                                     (leaf 2)
                                     (leaf 0)
                                     (leaf 1)
                                     («Base.getD» x22 «Language.mStar»)
                                     («Authoring.rulesIn» x24 (x17 (leaf 5)) x25)
                                     («Base.getD» x21 (leaf 0))
                                     x26
                                     x28
                                     x29)
                             else
                               if («Authoring.form»
                                 x6
                                 (mk 0 [leaf 115,
                                   leaf 117,
                                   leaf 109,
                                   leaf 45,
                                   leaf 99,
                                   leaf 97,
                                   leaf 115,
                                   leaf 101,
                                   leaf 115])
                                 (leaf 5)).label ≠ 0 then
                                 let x22 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x16
                                   (leaf 3)
                                   ((«Prelude.at» x15 (leaf 0)) :: x8)
                                   («Prelude.none» :: x9)
                                   x10;
                                 let x23 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x16
                                   (leaf 4)
                                   ((«Prelude.at» x15 (leaf 0)) :: x8)
                                   («Prelude.none» :: x9)
                                   x10;
                                 («Prelude.and»
                                   («Prelude.isSome» x20)
                                   («Prelude.and»
                                     («Authoring.namesOk» x0 (leaf 1) («Prelude.at» x11 (leaf 2)))
                                     («Prelude.and» (x19 x8 x15) («Prelude.and» (x22).1 (x23).1))),
                                   fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                     «Tactics.bySplit2»
                                       (leaf 3)
                                       (leaf 4)
                                       («Base.getD» x20 (leaf 0))
                                       ((x22).2 x24 x25 x26)
                                       ((x23).2 x24 x25 x26))
                               else
                                 if («Authoring.form»
                                   x6
                                   (mk 0 [leaf 116,
                                     leaf 114,
                                     leaf 101,
                                     leaf 101,
                                     leaf 45,
                                     leaf 99,
                                     leaf 97,
                                     leaf 115,
                                     leaf 101,
                                     leaf 115])
                                   (leaf 5)).label ≠ 0 then
                                   let x22 : T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := x16
                                     (leaf 4)
                                     ((«Prelude.at» x15 (leaf 1)) ::
                                       ((«Prelude.at» x15 (leaf 0)) :: x8))
                                     («Prelude.none» :: («Prelude.none» :: x9))
                                     x10;
                                   let x23 : T := «Authoring.lemmaOf»
                                     x1
                                     x5
                                     («Prelude.at» x11 (leaf 3));
                                   («Prelude.and»
                                     («Prelude.isSome» x20)
                                     («Prelude.and»
                                       («Authoring.namesOk» x0 (leaf 2) («Prelude.at» x11 (leaf 2)))
                                       («Prelude.and»
                                         (x19 x8 x15)
                                         («Prelude.and» («Prelude.isSome» x23) (x22).1))),
                                     fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                       «Tactics.byTreeSplit»
                                         («Base.getD» x23 (leaf 0))
                                         («Base.getD» x20 (leaf 0))
                                         ((x22).2 x24 x25 x26))
                                 else
                                   if («Authoring.headed»
                                     x6
                                     (mk 0 [leaf 97,
                                       leaf 117,
                                       leaf 116,
                                       leaf 111,
                                       leaf 45,
                                       leaf 116,
                                       leaf 114,
                                       leaf 101,
                                       leaf 101,
                                       leaf 115])).label ≠ 0 then
                                     let x22 : T := «Authoring.lemmaOf»
                                       x1
                                       x5
                                       («Prelude.at» x11 (leaf 3));
                                     («Prelude.and»
                                       (Const.lt (leaf 3) x12)
                                       («Prelude.and»
                                         («Prelude.isSome» («Authoring.depthOf» x14))
                                         («Prelude.and»
                                           («Prelude.isSome»
                                             («Authoring.number» («Prelude.at» x11 (leaf 2))))
                                           («Prelude.and» («Prelude.isSome» x22) (x18 (leaf 4))))),
                                       fun (x23 : T) (x24 : List T) (x25 : List T) =>
                                         «Tactics.byAutoT»
                                           x23
                                           x24
                                           x13
                                           («Base.getD» x22 (leaf 0))
                                           («Authoring.rulesIn» x24 (x17 (leaf 4)) x25)
                                           («Base.getD»
                                             («Authoring.number» («Prelude.at» x11 (leaf 2)))
                                             (leaf 0))
                                           («Base.getD» («Authoring.depthOf» x14) (leaf 0)))
                                   else
                                     if («Authoring.form»
                                       x6
                                       (mk 0 [leaf 103,
                                         leaf 101,
                                         leaf 110,
                                         leaf 101,
                                         leaf 114,
                                         leaf 97,
                                         leaf 108,
                                         leaf 105,
                                         leaf 122,
                                         leaf 101])
                                       (leaf 4)).label ≠ 0 then
                                       let x22 : T := «Authoring.itype»
                                         x4
                                         (Const.child x14 (leaf 1));
                                       let x23 : T := «Authoring.iterm»
                                         x0
                                         x2
                                         x3
                                         x4
                                         («Prelude.at» x11 (leaf 2))
                                         x8
                                         x9;
                                       let x24 : T := «Reader.nameOf» (Const.child x14 (leaf 0));
                                       let x25 : T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := x16
                                         (leaf 3)
                                         (x24 :: x8)
                                         ((«Authoring.kernelType» x3 (Const.child x14 (leaf 1))) ::
                                           x9)
                                         x10;
                                       («Prelude.and»
                                         («Authoring.ibinder» x0 x4 x14)
                                         («Prelude.and»
                                           (x19 x8 («Prelude.single» x24))
                                           («Prelude.and» («Prelude.isSome» x23) (x25).1)),
                                         fun (x26 : T) (x27 : List T) (x28 : List T) =>
                                           «Tactics.byGeneralize»
                                             («Base.getD» x22 «Theory.one»)
                                             («Base.getD» x23 «Language.mStar»)
                                             ((x25).2 x26 x27 x28))
                                     else
                                       if (Const.lt (leaf 2) x0).label ≠ 0 then
                                         «Authoring.script4» x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
                                       else
                                         «Authoring.script3» x0 x1 x2 x3 x4 x5 x6 x8 x9 x10);
    x11

def «Authoring.deduction» :=
  fun (x0 : T)
    (x1 : T × (T → List T → List T → List T → List T → T → T → T)) =>
    let x2 : T →
      List T →
        List T →
          List T →
            List T →
              T →
                T := (fun (x2 : T) (x3 : List T) (x4 : List T) =>
      «Formula.prove» x0 ((x1).2 x2 x3 x4));
    x2

def «Authoring.logical» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → List T → List T → List T → List T → T → T) =>
    let x3 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (x1,
      fun (x3 : T) (x4 : List T) (x5 : List T) =>
        «Formula.equate» x0 (x2 x3 x4 x5));
    x3

def «Authoring.logicalExact» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T → List T → List T → List T → List T → T → T) =>
    let x3 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (x1,
      fun (x3 : T) (x4 : List T) (x5 : List T) =>
        «Formula.equateExact» x0 (x2 x3 x4 x5));
    x3

def «Authoring.logicalScripts» :=
  Const.children
    (mk 0 [mk 0 [leaf 116, leaf 114, leaf 117, leaf 116, leaf 104],
      mk 0 [leaf 104,
        leaf 121,
        leaf 112,
        leaf 111,
        leaf 116,
        leaf 104,
        leaf 101,
        leaf 115,
        leaf 105,
        leaf 115],
      mk 0 [leaf 97, leaf 115, leaf 115, leaf 117, leaf 109, leaf 101],
      mk 0 [leaf 97,
        leaf 110,
        leaf 100,
        leaf 45,
        leaf 105,
        leaf 110,
        leaf 116,
        leaf 114,
        leaf 111],
      mk 0 [leaf 97,
        leaf 110,
        leaf 100,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 105,
        leaf 109,
        leaf 112,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 111,
        leaf 114,
        leaf 45,
        leaf 108,
        leaf 101,
        leaf 102,
        leaf 116],
      mk 0 [leaf 111,
        leaf 114,
        leaf 45,
        leaf 114,
        leaf 105,
        leaf 103,
        leaf 104,
        leaf 116],
      mk 0 [leaf 111,
        leaf 114,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 97,
        leaf 108,
        leaf 108,
        leaf 45,
        leaf 105,
        leaf 110,
        leaf 116,
        leaf 114,
        leaf 111],
      mk 0 [leaf 97,
        leaf 108,
        leaf 108,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 101,
        leaf 120,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 115,
        leaf 45,
        leaf 105,
        leaf 110,
        leaf 116,
        leaf 114,
        leaf 111],
      mk 0 [leaf 101,
        leaf 120,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 115,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 102,
        leaf 97,
        leaf 108,
        leaf 115,
        leaf 101,
        leaf 45,
        leaf 101,
        leaf 108,
        leaf 105,
        leaf 109],
      mk 0 [leaf 117,
        leaf 110,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100,
        leaf 45,
        leaf 102,
        leaf 111,
        leaf 114,
        leaf 109,
        leaf 117,
        leaf 108,
        leaf 97],
      mk 0 [leaf 117,
        leaf 110,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100,
        leaf 45,
        leaf 104,
        leaf 121,
        leaf 112,
        leaf 111,
        leaf 116,
        leaf 104,
        leaf 101,
        leaf 115,
        leaf 105,
        leaf 115],
      mk 0 [leaf 117, leaf 115, leaf 101]])

def «Authoring.scriptLogic» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x8 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := (fun (x8 : List T) (x9 : List T) (x10 : List T) =>
      let x11 : List T := Const.children x6;
      let x12 : T := «Authoring.connectivesAt» x3;
      let x13 : List
        T := «Prelude.append» x10 («Prelude.single» «Authoring.unnamed»);
      let x14 : T := «Prelude.at» x11 (leaf 1);
      let x15 : T := «Prelude.at» x11 (leaf 2);
      let x16 : T := «Prelude.at» x11 (leaf 3);
      let x17 : T →
        List T →
          List T →
            List T →
              T ×
                (T →
                  List T →
                    List T →
                      List T →
                        List T →
                          T →
                            T →
                              T) := (fun (x17 : T) =>
        «Authoring/SRs.atOr» «Authoring.failSR» x7 x17);
      let x18 : T →
        T ×
          (T →
            List T →
              List T →
                List T → List T → T → T → T) := (fun (x18 : T) =>
        x17 x18 x8 x9 x13);
      let x19 : T →
        T := (fun (x19 : T) => «Authoring.iterm» x0 x2 x3 x4 x19 x8 x9);
      let x20 : List T →
        T := (fun (x20 : List T) =>
        «Prelude.and»
          («Base.allT» («Authoring.bindable» x0) x20)
          («Authoring.distinctFrom»
            («Prelude.append»
              x3
              («Prelude.append» x4 («Prelude.append» x8 («Prelude.append» x10 x5))))
            («Base.mapT» «Reader.nameOf» x20)));
      let x21 : T := (if («Reader.isAtom» x14).label ≠ 0 then
        «Reader.indexOf» («Reader.nameOf» x14) x10
      else
        «Prelude.none»);
      let x22 : T →
        List T →
          List T →
            List T → List T → T → T := «Authoring.deduction»
        x12
        (x18 (leaf 1));
      let x23 : T →
        List T →
          List T →
            List T → List T → T → T := «Authoring.deduction»
        x12
        (x18 (leaf 2));
      if («Authoring.form»
        x6
        (mk 0 [leaf 116, leaf 114, leaf 117, leaf 116, leaf 104])
        (leaf 1)).label ≠ 0 then
        «Authoring.logical»
          x12
          (leaf 1)
          (fun (_ : T) (_ : List T) (_ : List T) => «Formula.truth» x12)
      else
        if («Authoring.form»
          x6
          (mk 0 [leaf 104,
            leaf 121,
            leaf 112,
            leaf 111,
            leaf 116,
            leaf 104,
            leaf 101,
            leaf 115,
            leaf 105,
            leaf 115])
          (leaf 2)).label ≠ 0 then
          «Authoring.logicalExact»
            x12
            («Prelude.isSome» x21)
            (fun (_ : T) (_ : List T) (_ : List T) =>
              «Formula.hypothesis» («Base.getD» x21 (leaf 0)))
        else
          if («Authoring.form»
            x6
            (mk 0 [leaf 97, leaf 115, leaf 115, leaf 117, leaf 109, leaf 101])
            (leaf 3)).label ≠ 0 then
            let x24 : T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T) := x17
              (leaf 2)
              x8
              x9
              («Prelude.append» x13 («Prelude.single» («Reader.nameOf» x14)));
            «Authoring.logical»
              x12
              («Prelude.and» (x20 («Prelude.single» x14)) (x24).1)
              (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                «Formula.assume» x12 («Authoring.deduction» x12 x24 x25 x26 x27))
          else
            if («Authoring.form»
              x6
              (mk 0 [leaf 97,
                leaf 110,
                leaf 100,
                leaf 45,
                leaf 105,
                leaf 110,
                leaf 116,
                leaf 114,
                leaf 111])
              (leaf 3)).label ≠ 0 then
              «Authoring.logical»
                x12
                («Prelude.and» (x18 (leaf 1)).1 (x18 (leaf 2)).1)
                (fun (x24 : T) (x25 : List T) (x26 : List T) =>
                  «Formula.conjunction» x12 (x22 x24 x25 x26) (x23 x24 x25 x26))
            else
              if («Authoring.form»
                x6
                (mk 0 [leaf 97,
                  leaf 110,
                  leaf 100,
                  leaf 45,
                  leaf 101,
                  leaf 108,
                  leaf 105,
                  leaf 109])
                (leaf 4)).label ≠ 0 then
                let x24 : T ×
                  (T →
                    List T →
                      List T →
                        List T →
                          List T →
                            T →
                              T →
                                T) := x17
                  (leaf 3)
                  x8
                  x9
                  («Prelude.append»
                    x13
                    («Base.mapT» «Reader.nameOf» (Const.children x15)));
                «Authoring.logical»
                  x12
                  («Prelude.and»
                    («Prelude.isSome» x21)
                    («Prelude.and»
                      («Authoring.namesOk» x0 (leaf 2) x15)
                      («Prelude.and» (x20 (Const.children x15)) (x24).1)))
                  (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                    «Formula.conjuncts»
                      x12
                      («Base.getD» x21 (leaf 0))
                      («Authoring.deduction» x12 x24 x25 x26 x27))
              else
                if («Authoring.form»
                  x6
                  (mk 0 [leaf 105,
                    leaf 109,
                    leaf 112,
                    leaf 45,
                    leaf 101,
                    leaf 108,
                    leaf 105,
                    leaf 109])
                  (leaf 5)).label ≠ 0 then
                  let x24 : T ×
                    (T →
                      List T →
                        List T →
                          List T →
                            List T →
                              T →
                                T →
                                  T) := x17
                    (leaf 4)
                    x8
                    x9
                    («Prelude.append» x13 («Prelude.single» («Reader.nameOf» x16)));
                  «Authoring.logical»
                    x12
                    («Prelude.and»
                      («Prelude.isSome» x21)
                      («Prelude.and»
                        (x20 («Prelude.single» x16))
                        («Prelude.and» (x18 (leaf 2)).1 (x24).1)))
                    (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                      «Formula.implication»
                        x12
                        («Base.getD» x21 (leaf 0))
                        (x23 x25 x26 x27)
                        («Authoring.deduction» x12 x24 x25 x26 x27))
                else
                  if («Prelude.or»
                    («Authoring.form»
                      x6
                      (mk 0 [leaf 111,
                        leaf 114,
                        leaf 45,
                        leaf 108,
                        leaf 101,
                        leaf 102,
                        leaf 116])
                      (leaf 2))
                    («Authoring.form»
                      x6
                      (mk 0 [leaf 111,
                        leaf 114,
                        leaf 45,
                        leaf 114,
                        leaf 105,
                        leaf 103,
                        leaf 104,
                        leaf 116])
                      (leaf 2))).label ≠ 0 then
                    «Authoring.logical»
                      x12
                      (x18 (leaf 1)).1
                      (fun (x24 : T) (x25 : List T) (x26 : List T) =>
                        «Formula.disjunct»
                          x12
                          («Authoring.headed»
                            x6
                            (mk 0 [leaf 111,
                              leaf 114,
                              leaf 45,
                              leaf 114,
                              leaf 105,
                              leaf 103,
                              leaf 104,
                              leaf 116]))
                          (x22 x24 x25 x26))
                  else
                    if («Authoring.form»
                      x6
                      (mk 0 [leaf 111,
                        leaf 114,
                        leaf 45,
                        leaf 101,
                        leaf 108,
                        leaf 105,
                        leaf 109])
                      (leaf 5)).label ≠ 0 then
                      let x24 : T ×
                        (T →
                          List T →
                            List T →
                              List T →
                                List T →
                                  T →
                                    T →
                                      T) := x17
                        (leaf 3)
                        x8
                        x9
                        («Prelude.append»
                          x13
                          («Prelude.single» («Reader.nameOf» (Const.child x15 (leaf 0)))));
                      let x25 : T ×
                        (T →
                          List T →
                            List T →
                              List T →
                                List T →
                                  T →
                                    T →
                                      T) := x17
                        (leaf 4)
                        x8
                        x9
                        («Prelude.append»
                          x13
                          («Prelude.single» («Reader.nameOf» (Const.child x15 (leaf 1)))));
                      «Authoring.logical»
                        x12
                        («Prelude.and»
                          («Prelude.isSome» x21)
                          («Prelude.and»
                            («Authoring.namesOk» x0 (leaf 2) x15)
                            («Prelude.and»
                              (x20 (Const.children x15))
                              («Prelude.and» (x24).1 (x25).1))))
                        (fun (x26 : T) (x27 : List T) (x28 : List T) =>
                          «Formula.alternatives»
                            x12
                            («Base.getD» x21 (leaf 0))
                            («Authoring.deduction» x12 x24 x26 x27 x28)
                            («Authoring.deduction» x12 x25 x26 x27 x28))
                    else
                      if («Authoring.form»
                        x6
                        (mk 0 [leaf 97,
                          leaf 108,
                          leaf 108,
                          leaf 45,
                          leaf 105,
                          leaf 110,
                          leaf 116,
                          leaf 114,
                          leaf 111])
                        (leaf 3)).label ≠ 0 then
                        let x24 : T ×
                          (T →
                            List T →
                              List T →
                                List T →
                                  List T →
                                    T →
                                      T →
                                        T) := x17
                          (leaf 2)
                          ((«Reader.nameOf» x14) :: x8)
                          («Prelude.none» :: x9)
                          («Prelude.append» x13 («Prelude.single» «Authoring.unnamed»));
                        «Authoring.logical»
                          x12
                          («Prelude.and» (x20 («Prelude.single» x14)) (x24).1)
                          (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                            «Formula.allIntro» x12 («Authoring.deduction» x12 x24 x25 x26 x27))
                      else
                        if («Authoring.form»
                          x6
                          (mk 0 [leaf 97,
                            leaf 108,
                            leaf 108,
                            leaf 45,
                            leaf 101,
                            leaf 108,
                            leaf 105,
                            leaf 109])
                          (leaf 5)).label ≠ 0 then
                          let x24 : T ×
                            (T →
                              List T →
                                List T →
                                  List T →
                                    List T →
                                      T →
                                        T →
                                          T) := x17
                            (leaf 4)
                            x8
                            x9
                            («Prelude.append» x13 («Prelude.single» («Reader.nameOf» x16)));
                          «Authoring.logical»
                            x12
                            («Prelude.and»
                              («Prelude.isSome» x21)
                              («Prelude.and»
                                («Prelude.isSome» (x19 x15))
                                («Prelude.and» (x20 («Prelude.single» x16)) (x24).1)))
                            (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                              «Formula.allElim»
                                x12
                                («Base.getD» x21 (leaf 0))
                                («Base.getD» (x19 x15) «Language.mStar»)
                                («Authoring.deduction» x12 x24 x25 x26 x27))
                        else
                          if («Authoring.form»
                            x6
                            (mk 0 [leaf 101,
                              leaf 120,
                              leaf 105,
                              leaf 115,
                              leaf 116,
                              leaf 115,
                              leaf 45,
                              leaf 105,
                              leaf 110,
                              leaf 116,
                              leaf 114,
                              leaf 111])
                            (leaf 3)).label ≠ 0 then
                            «Authoring.logical»
                              x12
                              («Prelude.and» («Prelude.isSome» (x19 x14)) (x18 (leaf 2)).1)
                              (fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                «Formula.existsIntro»
                                  x12
                                  («Base.getD» (x19 x14) «Language.mStar»)
                                  (x23 x24 x25 x26))
                          else
                            if («Authoring.form»
                              x6
                              (mk 0 [leaf 101,
                                leaf 120,
                                leaf 105,
                                leaf 115,
                                leaf 116,
                                leaf 115,
                                leaf 45,
                                leaf 101,
                                leaf 108,
                                leaf 105,
                                leaf 109])
                              (leaf 4)).label ≠ 0 then
                              let x24 : T ×
                                (T →
                                  List T →
                                    List T →
                                      List T →
                                        List T →
                                          T →
                                            T →
                                              T) := x17
                                (leaf 3)
                                ((«Reader.nameOf» (Const.child x15 (leaf 0))) :: x8)
                                («Prelude.none» :: x9)
                                («Prelude.append»
                                  x13
                                  («Theory.l3»
                                    «Authoring.unnamed»
                                    «Authoring.unnamed»
                                    («Reader.nameOf» (Const.child x15 (leaf 1)))));
                              «Authoring.logical»
                                x12
                                («Prelude.and»
                                  («Prelude.isSome» x21)
                                  («Prelude.and»
                                    («Authoring.namesOk» x0 (leaf 2) x15)
                                    («Prelude.and» (x20 (Const.children x15)) (x24).1)))
                                (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                  «Formula.existsElim»
                                    x12
                                    («Base.getD» x21 (leaf 0))
                                    («Authoring.deduction» x12 x24 x25 x26 x27))
                            else
                              if («Authoring.form»
                                x6
                                (mk 0 [leaf 102,
                                  leaf 97,
                                  leaf 108,
                                  leaf 115,
                                  leaf 101,
                                  leaf 45,
                                  leaf 101,
                                  leaf 108,
                                  leaf 105,
                                  leaf 109])
                                (leaf 2)).label ≠ 0 then
                                «Authoring.logical»
                                  x12
                                  (x18 (leaf 1)).1
                                  (fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                    «Formula.falseElim» x12 (x22 x24 x25 x26))
                              else
                                if («Authoring.form»
                                  x6
                                  (mk 0 [leaf 117,
                                    leaf 110,
                                    leaf 102,
                                    leaf 111,
                                    leaf 108,
                                    leaf 100,
                                    leaf 45,
                                    leaf 102,
                                    leaf 111,
                                    leaf 114,
                                    leaf 109,
                                    leaf 117,
                                    leaf 108,
                                    leaf 97])
                                  (leaf 2)).label ≠ 0 then
                                  «Authoring.logical»
                                    x12
                                    (x18 (leaf 1)).1
                                    (fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                      «Formula.unfoldFormula»
                                        x24
                                        x25
                                        («Prelude.length» x4)
                                        (x22 x24 x25 x26))
                                else
                                  if («Authoring.form»
                                    x6
                                    (mk 0 [leaf 117,
                                      leaf 110,
                                      leaf 102,
                                      leaf 111,
                                      leaf 108,
                                      leaf 100,
                                      leaf 45,
                                      leaf 104,
                                      leaf 121,
                                      leaf 112,
                                      leaf 111,
                                      leaf 116,
                                      leaf 104,
                                      leaf 101,
                                      leaf 115,
                                      leaf 105,
                                      leaf 115])
                                    (leaf 4)).label ≠ 0 then
                                    let x24 : T ×
                                      (T →
                                        List T →
                                          List T →
                                            List T →
                                              List T →
                                                T →
                                                  T →
                                                    T) := x17
                                      (leaf 3)
                                      x8
                                      x9
                                      («Prelude.append»
                                        x13
                                        («Prelude.single» («Reader.nameOf» x15)));
                                    «Authoring.logical»
                                      x12
                                      («Prelude.and»
                                        («Prelude.isSome» x21)
                                        («Prelude.and» (x20 («Prelude.single» x15)) (x24).1))
                                      (fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                        «Formula.unfoldHypothesis»
                                          x25
                                          x26
                                          («Prelude.length» x4)
                                          («Base.getD» x21 (leaf 0))
                                          («Authoring.deduction» x12 x24 x25 x26 x27))
                                  else
                                    if («Authoring.headed»
                                      x6
                                      (mk 0 [leaf 117, leaf 115, leaf 101])).label ≠ 0 then
                                      let x24 : T := «Authoring.lemmaOf» x1 x5 x14;
                                      let x25 : T := «Base.allSomeT»
                                        («Base.mapT» («Authoring.itype» x4) (Const.children x15));
                                      let x26 : T := «Base.allSomeT»
                                        («Base.mapT» x19 («Prelude.reverse» (Const.children x16)));
                                      let x27 : List
                                        T := «Prelude.drop»
                                        (leaf 4)
                                        («Base.range» («Prelude.length» x11));
                                      «Authoring.logicalExact»
                                        x12
                                        («Prelude.and»
                                          (Const.lt (leaf 3) («Prelude.length» x11))
                                          («Prelude.and»
                                            («Prelude.isSome» x24)
                                            («Prelude.and»
                                              («Reader.isList» x15)
                                              («Prelude.and»
                                                («Prelude.isSome» x25)
                                                («Prelude.and»
                                                  («Reader.isList» x16)
                                                  («Prelude.and»
                                                    («Prelude.isSome» x26)
                                                    («Base.allT»
                                                      (fun (x28 : T) => (x18 x28).1)
                                                      x27)))))))
                                        (fun (x28 : T) (x29 : List T) (x30 : List T) =>
                                          «Formula.applyTheorem»
                                            x29
                                            («Base.getD» x24 (leaf 0))
                                            (Const.children («Base.getD» x25 «Authoring.unnamed»))
                                            (Const.children («Base.getD» x26 «Authoring.unnamed»))
                                            (Const.foldr
                                              (α := T)
                                              (β := List (List T → List T → T → T))
                                              (fun (x31 : T)
                                                 (x32 : List (List T → List T → T → T)) =>
                                                ((«Authoring.deduction»
                                                  x12
                                                  (x18 x31)
                                                  x28
                                                  x29
                                                  x30) ::
                                                  x32))
                                              ([] : List (List T → List T → T → T))
                                              x27))
                                    else
                                      (leaf 0, «Authoring.failTac»));
    x8

def «Authoring.equationScript» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x8 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := (let x8 : List T := Const.children x6;
                                 let x9 : T := «Prelude.length» x8;
                                 let x10 : T := «Prelude.length» x4;
                                 let x11 : T := «Prelude.at» x8 (leaf 1);
                                 let x12 : T →
                                   List T →
                                     List T →
                                       List T →
                                         T ×
                                           (T →
                                             List T →
                                               List T →
                                                 List T →
                                                   List T →
                                                     T →
                                                       T →
                                                         T) := (fun (x12 : T) =>
                                   «Authoring/SRs.atOr» «Authoring.failSR» x7 x12);
                                 fun (x13 : List T) (x14 : List T) (x15 : List T) =>
                                   let x16 : T →
                                     List
                                       T := (fun (x16 : T) =>
                                     «Authoring.rulesFrom» x1 x3 x4 x15 x5 («Prelude.drop» x16 x8));
                                   let x17 : T →
                                     T := (fun (x17 : T) =>
                                     «Base.allT»
                                       («Authoring.ruleOk» x0 x3 x4 x15 x5)
                                       («Prelude.drop» x17 x8));
                                   let x18 : List T →
                                     List T →
                                       T := (fun (x18 : List T) (x19 : List T) =>
                                     «Prelude.and»
                                       («Base.allT»
                                         (fun (x20 : T) =>
                                           if (Const.lt (leaf 1) x0).label ≠ 0 then
                                             «Authoring.bindable» x0 x20
                                           else
                                             «Authoring.declared» x20)
                                         x19)
                                       («Authoring.distinctFrom»
                                         («Prelude.append» x18 («Prelude.append» x15 x5))
                                         («Base.mapT» «Reader.nameOf» x19)));
                                   if («Base.not» («Reader.isList» x6)).label ≠ 0 then
                                     (leaf 0, «Authoring.failTac»)
                                   else
                                     if («Prelude.and»
                                       (Const.lt (leaf 3) x0)
                                       («Authoring.headed»
                                         x6
                                         (mk 0 [leaf 110,
                                           leaf 97,
                                           leaf 116,
                                           leaf 45,
                                           leaf 105,
                                           leaf 110,
                                           leaf 100,
                                           leaf 117,
                                           leaf 99,
                                           leaf 116,
                                           leaf 105,
                                           leaf 111,
                                           leaf 110]))).label ≠ 0 then
                                       («Prelude.and»
                                         (Const.lt (leaf 2) x9)
                                         («Prelude.and»
                                           («Prelude.and»
                                             («Base.not» («Base.isEmpty» x13))
                                             («Authoring.word» x11 («Prelude.at» x13 (leaf 0))))
                                           («Prelude.and»
                                             («Prelude.isSome»
                                               («Authoring.number» («Prelude.at» x8 (leaf 2))))
                                             (x17 (leaf 3)))),
                                         fun (x19 : T) (x20 : List T) (x21 : List T) =>
                                           «Prover.byNatIndHyp»
                                             x19
                                             x20
                                             x10
                                             «Authoring.kZero»
                                             «Authoring.kSucc»
                                             («Authoring.rulesIn» x20 (x16 (leaf 3)) x21)
                                             («Base.getD»
                                               («Authoring.number» («Prelude.at» x8 (leaf 2)))
                                               (leaf 0)))
                                     else
                                       if («Authoring.headed»
                                         x6
                                         (mk 0 [leaf 110,
                                           leaf 111,
                                           leaf 114,
                                           leaf 109,
                                           leaf 97,
                                           leaf 108,
                                           leaf 105,
                                           leaf 122,
                                           leaf 101])).label ≠ 0 then
                                         («Prelude.and»
                                           (Const.lt (leaf 1) x9)
                                           («Prelude.and»
                                             («Prelude.isSome» («Authoring.number» x11))
                                             (x17 (leaf 2))),
                                           fun (x19 : T)
                                             (x20 : List T)
                                             (x21 : List T)
                                             (x22 : List T)
                                             (x23 : List T)
                                             (x24 : T)
                                             (x25 : T) =>
                                             «Prover.byNormW»
                                               x19
                                               x20
                                               x10
                                               («Authoring.rulesIn» x20 (x16 (leaf 2)) x21)
                                               («Base.getD» («Authoring.number» x11) (leaf 0))
                                               x22
                                               x23
                                               x24
                                               x25)
                                       else
                                         if («Authoring.headed»
                                           x6
                                           (mk 0 [leaf 114,
                                             leaf 101,
                                             leaf 100,
                                             leaf 117,
                                             leaf 99,
                                             leaf 101])).label ≠ 0 then
                                           («Prelude.and»
                                             (Const.lt (leaf 1) x9)
                                             («Prelude.and»
                                               («Prelude.isSome» («Authoring.depthOf» x11))
                                               (x17 (leaf 2))),
                                             fun (x19 : T) (x20 : List T) (x21 : List T) =>
                                               «Tactics.byMode»
                                                 («Base.getD» («Authoring.depthOf» x11) (leaf 0))
                                                 x19
                                                 x20
                                                 x10
                                                 («Authoring.rulesIn» x20 (x16 (leaf 2)) x21))
                                         else
                                           if («Authoring.headed»
                                             x6
                                             (mk 0 [leaf 97,
                                               leaf 117,
                                               leaf 116,
                                               leaf 111])).label ≠ 0 then
                                             («Prelude.and»
                                               (Const.lt (leaf 2) x9)
                                               («Prelude.and»
                                                 («Prelude.isSome» («Authoring.depthOf» x11))
                                                 («Prelude.and»
                                                   («Prelude.isSome»
                                                     («Authoring.number»
                                                       («Prelude.at» x8 (leaf 2))))
                                                   (x17 (leaf 3)))),
                                               fun (x19 : T) (x20 : List T) (x21 : List T) =>
                                                 «Tactics.byAuto»
                                                   x19
                                                   x20
                                                   x10
                                                   («Authoring.rulesIn» x20 (x16 (leaf 3)) x21)
                                                   («Base.getD»
                                                     («Authoring.number» («Prelude.at» x8 (leaf 2)))
                                                     (leaf 0))
                                                   («Base.getD» («Authoring.depthOf» x11) (leaf 0)))
                                           else
                                             if («Authoring.form»
                                               x6
                                               (mk 0 [leaf 101,
                                                 leaf 120,
                                                 leaf 116,
                                                 leaf 101,
                                                 leaf 110,
                                                 leaf 115,
                                                 leaf 105,
                                                 leaf 111,
                                                 leaf 110,
                                                 leaf 97,
                                                 leaf 108,
                                                 leaf 105,
                                                 leaf 116,
                                                 leaf 121])
                                               (leaf 3)).label ≠ 0 then
                                               let x19 : T ×
                                                 (T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           T →
                                                             T →
                                                               T) := x12
                                                 (leaf 2)
                                                 ((«Reader.nameOf» x11) :: x13)
                                                 («Prelude.none» :: x14)
                                                 x15;
                                               («Prelude.and»
                                                 (x18 x13 («Prelude.single» x11))
                                                 (x19).1,
                                                 fun (x20 : T) (x21 : List T) (x22 : List T) =>
                                                   «Prover.byFunExt» x20 x10 ((x19).2 x20 x21 x22))
                                             else
                                               let x19 : List
                                                 T := Const.children («Prelude.at» x8 (leaf 2));
                                               let x20 : T := «Reader.nameOf»
                                                 («Prelude.at» x19 (leaf 0));
                                               let x21 : T := «Reader.nameOf»
                                                 («Prelude.at» x19 (leaf 1));
                                               if («Authoring.form»
                                                 x6
                                                 (mk 0 [leaf 105,
                                                   leaf 110,
                                                   leaf 100,
                                                   leaf 117,
                                                   leaf 99,
                                                   leaf 116,
                                                   leaf 105,
                                                   leaf 111,
                                                   leaf 110])
                                                 (leaf 5)).label ≠ 0 then
                                                 let x22 : List T := «Prelude.drop» (leaf 1) x13;
                                                 let x23 : T ×
                                                   (T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             T →
                                                               T →
                                                                 T) := x12
                                                   (leaf 3)
                                                   x22
                                                   («Prelude.drop» (leaf 1) x14)
                                                   x15;
                                                 let x24 : T ×
                                                   (T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             T →
                                                               T →
                                                                 T) := x12
                                                   (leaf 4)
                                                   (x21 :: (x20 :: x22))
                                                   ((«Prelude.at» x14 (leaf 0)) ::
                                                     ((«Authoring.listElem»
                                                       («Prelude.at» x14 (leaf 0))) ::
                                                       («Prelude.drop» (leaf 1) x14)))
                                                   («Prelude.append»
                                                     x15
                                                     («Prelude.single»
                                                       («Reader.nameOf»
                                                         («Prelude.at» x19 (leaf 2)))));
                                                 («Prelude.and»
                                                   («Prelude.and»
                                                     («Base.not» («Base.isEmpty» x13))
                                                     («Authoring.word»
                                                       x11
                                                       («Prelude.at» x13 (leaf 0))))
                                                   («Prelude.and»
                                                     («Reader.isList» («Prelude.at» x8 (leaf 2)))
                                                     («Prelude.and»
                                                       (Const.eq («Prelude.length» x19) (leaf 3))
                                                       («Prelude.and»
                                                         (x18 x22 x19)
                                                         («Prelude.and» (x23).1 (x24).1)))),
                                                   fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                                     «Prover.byListIndWith»
                                                       x25
                                                       x10
                                                       (leaf 0)
                                                       (leaf 1)
                                                       ((x23).2 x25 x26 x27)
                                                       ((x24).2 x25 x26 x27))
                                               else
                                                 if («Authoring.form»
                                                   x6
                                                   (mk 0 [leaf 99,
                                                     leaf 97,
                                                     leaf 115,
                                                     leaf 101,
                                                     leaf 115])
                                                   (leaf 5)).label ≠ 0 then
                                                   let x22 : T := «Reader.indexOf»
                                                     («Reader.nameOf» x11)
                                                     x13;
                                                   let x23 : T := «Prelude.at»
                                                     x14
                                                     («Base.getD» x22 (leaf 0));
                                                   let x24 : T ×
                                                     (T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             List T →
                                                               T →
                                                                 T → T) := x12 (leaf 3) x13 x14 x15;
                                                   let x25 : T ×
                                                     (T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             List T →
                                                               T →
                                                                 T →
                                                                   T) := x12
                                                     (leaf 4)
                                                     (x21 :: (x20 :: x13))
                                                     (x23 :: ((«Authoring.listElem» x23) :: x14))
                                                     («Prelude.append»
                                                       x15
                                                       («Prelude.single»
                                                         (Const.node (leaf 0) ([] : List T))));
                                                   («Prelude.and»
                                                     («Reader.isAtom» x11)
                                                     («Prelude.and»
                                                       («Prelude.isSome» x22)
                                                       («Prelude.and»
                                                         («Reader.isList»
                                                           («Prelude.at» x8 (leaf 2)))
                                                         («Prelude.and»
                                                           (Const.eq
                                                             («Prelude.length» x19)
                                                             (leaf 2))
                                                           («Prelude.and»
                                                             (x18 x13 x19)
                                                             («Prelude.and» (x24).1 (x25).1))))),
                                                     fun (x26 : T) (x27 : List T) (x28 : List T) =>
                                                       «Tactics.byListSplit»
                                                         x26
                                                         x10
                                                         («Base.getD» x22 (leaf 0))
                                                         ((x24).2 x26 x27 x28)
                                                         ((x25).2 x26 x27 x28))
                                                 else
                                                   if («Authoring.form»
                                                     x6
                                                     (mk 0 [leaf 114,
                                                       leaf 101,
                                                       leaf 100,
                                                       leaf 117,
                                                       leaf 99,
                                                       leaf 101,
                                                       leaf 45,
                                                       leaf 104,
                                                       leaf 121,
                                                       leaf 112,
                                                       leaf 111,
                                                       leaf 116,
                                                       leaf 104,
                                                       leaf 101,
                                                       leaf 115,
                                                       leaf 101,
                                                       leaf 115])
                                                     (leaf 4)).label ≠ 0 then
                                                     let x22 : List
                                                       T := «Base.mapT»
                                                       «Reader.nameOf»
                                                       (Const.children («Prelude.at» x8 (leaf 2)));
                                                     let x23 : T ×
                                                       (T →
                                                         List T →
                                                           List T →
                                                             List T →
                                                               List T →
                                                                 T →
                                                                   T →
                                                                     T) := x12
                                                       (leaf 3)
                                                       x13
                                                       x14
                                                       («Prelude.append»
                                                         («Base.mapT»
                                                           (fun (x23 : T) =>
                                                             if («Authoring.has»
                                                               x23
                                                               x22).label ≠ 0 then
                                                               Const.node (leaf 0) ([] : List T)
                                                             else
                                                               x23)
                                                           x15)
                                                         x22);
                                                     («Prelude.and»
                                                       («Prelude.isSome» («Authoring.depthOf» x11))
                                                       («Prelude.and»
                                                         («Reader.isList»
                                                           («Prelude.at» x8 (leaf 2)))
                                                         («Prelude.and»
                                                           («Base.not» («Base.isEmpty» x22))
                                                           («Prelude.and»
                                                             («Base.allT»
                                                               (fun (x24 : T) =>
                                                                 «Prelude.and»
                                                                   («Reader.isAtom» x24)
                                                                   («Authoring.has»
                                                                     («Reader.nameOf» x24)
                                                                     x15))
                                                               (Const.children
                                                                 («Prelude.at» x8 (leaf 2))))
                                                             («Prelude.and»
                                                               («Authoring.distinctFrom»
                                                                 ([] : List T)
                                                                 x22)
                                                               (x23).1)))),
                                                       fun (x24 : T)
                                                         (x25 : List T)
                                                         (x26 : List T) =>
                                                         «Tactics.withWeakHyps»
                                                           x24
                                                           x25
                                                           x10
                                                           x26
                                                           («Base.mapT»
                                                             (fun (x27 : T) =>
                                                               «Base.getD»
                                                                 («Reader.indexOf» x27 x15)
                                                                 (leaf 0))
                                                             x22)
                                                           (fun (_ : List T) => (x23).2 x24 x25 x26)
                                                           («Base.getD»
                                                             («Authoring.depthOf» x11)
                                                             (leaf 0)))
                                                   else
                                                     if (Const.lt (leaf 1) x0).label ≠ 0 then
                                                       «Authoring.script2»
                                                         x0
                                                         x1
                                                         x2
                                                         x3
                                                         x4
                                                         x5
                                                         x6
                                                         x7
                                                         x13
                                                         x14
                                                         x15
                                                     else
                                                       (leaf 0, «Authoring.failTac»));
    x8

def «Authoring.scriptStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x8 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := (if («Prelude.and»
      (Const.lt (leaf 4) x0)
      («Prelude.and»
        («Reader.isList» x6)
        («Authoring.has»
          («Reader.nameOf» (Const.child x6 (leaf 0)))
          «Authoring.logicalScripts»))).label ≠ 0 then
      «Authoring.scriptLogic» x0 x1 x2 x3 x4 x5 x6 x7
    else
      «Authoring.equationScript» x0 x1 x2 x3 x4 x5 x6 x7);
    x8

def «Authoring.openRule» := leaf 255

def «Authoring.obligation» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Prelude.some»
      («Prover.dNode»
        «Authoring.openRule»
        (x0 ::
          (x1 ::
            ((Const.node (leaf 0) («Prelude.reverse» x2)) ::
              ((Const.node (leaf 0) x3) ::
                ((Const.node (leaf 0) x4) ::
                  ((Const.node (leaf 0) x5) ::
                    («Theory.l3» (Const.node (leaf 0) x6) x7 x8)))))))
        ([] : List T));
    x9

def «Authoring.located» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T)
    (x7 : List
      (T →
        List T →
          List T →
            List T →
              List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x8 : T →
      List T →
        List T →
          List T →
            List T →
              T ×
                (T →
                  List T →
                    List T →
                      List T →
                        List T →
                          T →
                            T →
                              T) := (fun (x8 : T) (x9 : List T) =>
      if («Prelude.and»
        (Const.lt (leaf 2) x0)
        («Prelude.and»
          («Authoring.form» x6 «Reader.kwHole» (leaf 2))
          («Reader.isAtom» (Const.child x6 (leaf 1))))).label ≠ 0 then
        fun (x10 : List T) (_ : List T) (x12 : List T) =>
          (leaf 1,
            fun (_ : T)
              (_ : List T)
              (_ : List T)
              (x16 : List T)
              (x17 : List T)
              (x18 : T)
              (x19 : T) =>
              «Authoring.obligation»
                (leaf 0)
                («Reader.nameOf» (Const.child x6 (leaf 1)))
                x9
                x10
                x12
                x16
                x17
                x18
                x19)
      else
        let x10 : T := «Prelude.and»
          (Const.lt (leaf 2) x0)
          («Authoring.form»
            x6
            (mk 0 [leaf 102, leaf 105, leaf 114, leaf 115, leaf 116])
            (leaf 3));
        let x11 : List
          (List T →
            List T →
              List T →
                T ×
                  (T →
                    List T →
                      List T →
                        List T →
                          List T →
                            T →
                              T →
                                T)) := Const.foldr
          (α := T →
            List T →
              List T →
                List T →
                  List T → T × (T → List T → List T → List T → List T → T → T → T))
          (β := T →
            List
              (List T →
                List T →
                  List T → T × (T → List T → List T → List T → List T → T → T → T)))
          (fun (x11 : T →
               List T →
                 List T →
                   List T →
                     List T → T × (T → List T → List T → List T → List T → T → T → T))
             (x12 : T →
               List
                 (List T →
                   List T →
                     List T → T × (T → List T → List T → List T → List T → T → T → T)))
             (x13 : T) =>
            ((x11
              (if («Prelude.and» x10 (Const.eq x13 (leaf 1))).label ≠ 0 then
                leaf 0
              else
                x8)
              (x13 :: x9)) ::
              (x12 (Const.add x13 (leaf 1)))))
          (fun (_ : T) =>
            ([] : List (List T →
              List T →
                List T → T × (T → List T → List T → List T → List T → T → T → T))))
          x7
          (leaf 0);
        let x12 : List T →
          List T →
            List T →
              T ×
                (T →
                  List T →
                    List T →
                      List T →
                        List T →
                          T → T → T) := «Authoring.scriptStep»
          x0
          x1
          x2
          x3
          x4
          x5
          x6
          x11;
        if (Const.eq x8 (leaf 0)).label ≠ 0 then
          x12
        else
          fun (x13 : List T) (x14 : List T) (x15 : List T) =>
            let x16 : T ×
              (T →
                List T → List T → List T → List T → T → T → T) := x12 x13 x14 x15;
            ((x16).1,
              fun (x17 : T)
                (x18 : List T)
                (x19 : List T)
                (x20 : List T)
                (x21 : List T)
                (x22 : T)
                (x23 : T) =>
                let x24 : T := (x16).2 x17 x18 x19 x20 x21 x22 x23;
                if («Prelude.isSome» x24).label ≠ 0 then
                  x24
                else
                  «Authoring.obligation»
                    (leaf 1)
                    «Authoring.unnamed»
                    x9
                    x13
                    x15
                    x20
                    x21
                    x22
                    x23));
    x8

def «Authoring.readScript» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T →
      List T →
        List T →
          List T →
            List T →
              T ×
                (T →
                  List T →
                    List T →
                      List T →
                        List T →
                          T →
                            T →
                              T) := Const.para
      (α := T →
        List T →
          List T →
            List T →
              List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring.located» x0 x1 x2 x3 x4 x5)
      x6;
    x7

def «Authoring.holed» :=
  fun (x0 : T) =>
    let x1 : T := Const.para
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        «Prelude.or»
          («Authoring.form» x1 «Reader.kwHole» (leaf 2))
          («Base.anyT» (fun (x3 : T) => x3) x2))
      x0;
    x1

def «Authoring.obligationsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := Const.para
      (α := List T)
      (fun (x1 : T) (x2 : List (List T)) =>
        if («Prelude.and»
          (Const.eq (Const.label x1) «Authoring.openRule»)
          (Const.eq (Const.arity x1) (leaf 1))).label ≠ 0 then
          «Prelude.single» x1
        else
          Const.lcase
            (α := List T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : List T) (x4 : List (List T)) =>
              Const.foldr
                (α := List T)
                (β := List T)
                (fun (x5 : List T) (x6 : List T) => «Prelude.append» x5 x6)
                ([] : List T)
                x4))
      x0;
    x1

def «Authoring.atomOf» :=
  fun (x0 : T) =>
    let x1 : T := Const.node (leaf 1) (Const.children x0); x1

def «Authoring.listOf» :=
  fun (x0 : List T) => let x1 : T := Const.node (leaf 2) x0; x1

def «Authoring.digits» :=
  fun (x0 : T) =>
    let x1 : List
      T := (Const.iter
      (α := T × List T)
      (fun (x1 : T × List T) =>
        if («Prelude.and»
          (Const.eq (x1).1 (leaf 0))
          («Base.not» («Base.isEmpty» (x1).2))).label ≠ 0 then
          x1
        else
          (Const.div (x1).1 (leaf 10),
            ((Const.add (leaf 48) (Const.mod (x1).1 (leaf 10))) :: (x1).2)))
      (x0, ([] : List T))
      (Const.add (Const.log2 (Const.add x0 (leaf 1))) (leaf 1))).2;
    x1

def «Authoring.nameOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (if («Base.isEmpty» (Const.children x0)).label ≠ 0 then
      Const.node (leaf 0) («Prelude.append» x1 («Authoring.digits» x2))
    else
      x0);
    x3

def «Authoring.opaqueOf» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Authoring.listOf»
      ((«Authoring.atomOf»
        (mk 0 [leaf 111, leaf 112, leaf 97, leaf 113, leaf 117, leaf 101])) ::
        ((Const.node (leaf 1) («Authoring.digits» x0)) :: x1));
    x2

def «Authoring.showType» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.child x2 (leaf 0);
        let x5 : T →
          T := (fun (x5 : T) =>
          «Authoring.listOf»
            («Theory.l3»
              («Authoring.atomOf» x5)
              («Prelude.at» x3 (leaf 0))
              («Prelude.at» x3 (leaf 1))));
        let x6 : T →
          T := (fun (x6 : T) =>
          «Authoring.listOf»
            («Theory.l2» («Authoring.atomOf» x6) («Prelude.at» x3 (leaf 0))));
        if (Const.equal x2 «Theory.nat»).label ≠ 0 then
          «Authoring.atomOf» (mk 0 [leaf 78, leaf 97, leaf 116])
        else
          if (Const.equal x2 «Translation.treeTy»).label ≠ 0 then
            «Authoring.atomOf» «Reader.kwT»
          else
            if (Const.equal x2 «Translation.bitsTy»).label ≠ 0 then
              «Authoring.atomOf» (mk 0 [leaf 66, leaf 105, leaf 116, leaf 115])
            else
              if (Const.equal
                x2
                («Theory.coprod» «Theory.one» «Theory.one»)).label ≠ 0 then
                «Authoring.atomOf» (mk 0 [leaf 66, leaf 105, leaf 116])
              else
                if (Const.equal x2 «Theory.one»).label ≠ 0 then
                  «Authoring.atomOf» «Reader.kwUnit»
                else
                  if (Const.equal x2 «Theory.omega»).label ≠ 0 then
                    «Authoring.atomOf»
                      (mk 0 [leaf 79, leaf 109, leaf 101, leaf 103, leaf 97])
                  else
                    if (Const.equal
                      x2
                      («Theory.prod» x4 (Const.child x2 (leaf 1)))).label ≠ 0 then
                      x5 «Reader.kwProd»
                    else
                      if (Const.equal
                        x2
                        («Theory.coprod» x4 (Const.child x2 (leaf 1)))).label ≠ 0 then
                        x5 (mk 0 [leaf 83, leaf 117, leaf 109])
                      else
                        if (Const.equal
                          x2
                          («Theory.exp» x4 (Const.child x2 (leaf 1)))).label ≠ 0 then
                          x5 «Reader.kwArrow»
                        else
                          if (Const.equal x2 («Theory.list» x4)).label ≠ 0 then
                            x6 «Reader.kwList»
                          else
                            if (Const.equal x2 («Theory.lrose» x4)).label ≠ 0 then
                              x6 (mk 0 [leaf 82, leaf 111, leaf 115, leaf 101])
                            else
                              if (Const.equal x2 («Theory.x» (Const.label x4))).label ≠ 0 then
                                «Authoring.atomOf»
                                  («Authoring.nameOr»
                                    («Prelude.at» x0 (Const.label x4))
                                    («Theory.l2» (leaf 95) (leaf 88))
                                    (Const.label x4))
                              else
                                «Authoring.opaqueOf» (Const.label x2) x3)
      x1;
    x2

def «Authoring/Shows.single» :=
  fun (x0 : List T → T) =>
    let x1 : List (List T → T) := (x0 :: ([] : List (List T → T))); x1

def «Authoring/Shows.length» :=
  fun (x0 : List (List T → T)) =>
    let x1 : T := Const.foldr
      (α := List T → T)
      (β := T)
      (fun (_ : List T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Shows.append» :=
  fun (x0 : List (List T → T)) (x1 : List (List T → T)) =>
    let x2 : List
      (List T →
        T) := Const.foldr
      (α := List T → T)
      (β := List (List T → T))
      (fun (x2 : List T → T) (x3 : List (List T → T)) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Shows.reverse» :=
  fun (x0 : List (List T → T)) =>
    let x1 : List
      (List T →
        T) := Const.foldr
      (α := List T → T)
      (β := List (List T → T) → List (List T → T))
      (fun (x1 : List T → T)
         (x2 : List (List T → T) → List (List T → T))
         (x3 : List (List T → T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List T → T)) => x1)
      x0
      ([] : List (List T → T));
    x1

def «Authoring/Shows.tail» :=
  fun (x0 : List (List T → T)) =>
    let x1 : List
      (List T →
        T) := Const.lcase
      (α := List T → T)
      (β := List (List T → T))
      x0
      ([] : List (List T → T))
      (fun (_ : List T → T) (x2 : List (List T → T)) => x2);
    x1

def «Authoring/Shows.drop» :=
  fun (x0 : T) (x1 : List (List T → T)) =>
    let x2 : List
      (List T →
        T) := Const.iter
      (α := List (List T → T))
      «Authoring/Shows.tail»
      x1
      x0;
    x2

def «Authoring/Shows.atOr» :=
  fun (x0 : List T → T) (x1 : List (List T → T)) (x2 : T) =>
    let x3 : List T →
      T := Const.lcase
      (α := List T → T)
      (β := List T → T)
      («Authoring/Shows.drop» x2 x1)
      x0
      (fun (x3 : List T → T) (_ : List (List T → T)) => x3);
    x3

def «Authoring.showNothing» :=
  fun (_ : List T) => «Authoring.opaqueOf» (leaf 0) ([] : List T)

def «Authoring.libName» :=
  fun (x0 : T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        if (Const.eq (Const.child x1 (leaf 1)) x0).label ≠ 0 then
          «Prelude.some» (Const.child x1 (leaf 0))
        else
          x2)
      «Prelude.none»
      «Authoring.libTable»;
    x1

def «Authoring.showPrim» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Prelude.length» x1;
                   if («Prelude.and»
                     (Const.eq x0 (leaf 0))
                     («Prelude.and»
                       (Const.eq x4 (leaf 1))
                       («Language.mIs» (leaf 1) (leaf 0) x2))).label ≠ 0 then
                     «Authoring.listOf»
                       («Theory.l2»
                         («Authoring.atomOf» «Reader.kwNil»)
                         («Prelude.at» x1 (leaf 0)))
                   else
                     if («Prelude.and»
                       (Const.eq x0 (leaf 1))
                       («Prelude.and»
                         (Const.eq x4 (leaf 1))
                         («Language.mIs» (leaf 2) (leaf 2) x2))).label ≠ 0 then
                       «Authoring.listOf»
                         («Theory.l4»
                           («Authoring.atomOf» «Reader.kwCons»)
                           («Prelude.at» x1 (leaf 0))
                           (Const.child x3 (leaf 1))
                           (Const.child x3 (leaf 2)))
                     else
                       if («Prelude.and»
                         (Const.eq x0 (leaf 2))
                         (Const.eq x4 (leaf 1))).label ≠ 0 then
                         «Authoring.listOf»
                           («Theory.l3»
                             («Authoring.atomOf» (mk 0 [leaf 110, leaf 111, leaf 100, leaf 101]))
                             («Prelude.at» x1 (leaf 0))
                             x3)
                       else
                         if («Prelude.and»
                           («Prelude.or» (Const.eq x0 (leaf 3)) (Const.eq x0 (leaf 4)))
                           (Const.eq x4 (leaf 2))).label ≠ 0 then
                           «Authoring.listOf»
                             («Theory.l4»
                               («Authoring.atomOf»
                                 (if (Const.eq x0 (leaf 3)).label ≠ 0 then
                                   mk 0 [leaf 105, leaf 110, leaf 108]
                                 else
                                   mk 0 [leaf 105, leaf 110, leaf 114]))
                               («Prelude.at» x1 (leaf 0))
                               («Prelude.at» x1 (leaf 1))
                               x3)
                         else
                           if («Prelude.and»
                             (Const.eq x0 (leaf 5))
                             (Const.eq x4 (leaf 3))).label ≠ 0 then
                             «Authoring.listOf»
                               («Theory.l5»
                                 («Authoring.atomOf» (mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]))
                                 («Prelude.at» x1 (leaf 0))
                                 («Prelude.at» x1 (leaf 1))
                                 («Prelude.at» x1 (leaf 2))
                                 x3)
                           else
                             if («Prelude.and»
                               (Const.eq x0 «Authoring.kZero»)
                               («Prelude.and»
                                 (Const.eq x4 (leaf 0))
                                 («Language.mIs» (leaf 1) (leaf 0) x2))).label ≠ 0 then
                               «Authoring.atomOf» (mk 0 [leaf 122, leaf 101, leaf 114, leaf 111])
                             else
                               if («Prelude.and»
                                 (Const.eq x0 «Authoring.kSucc»)
                                 (Const.eq x4 (leaf 0))).label ≠ 0 then
                                 «Authoring.listOf»
                                   («Theory.l2»
                                     («Authoring.atomOf»
                                       (mk 0 [leaf 115, leaf 117, leaf 99, leaf 99]))
                                     x3)
                               else
                                 «Authoring.opaqueOf» (leaf 7) («Prelude.single» x3));
    x4

def «Authoring.showCall» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := (let x6 : T := «Authoring/LD.length» «Translation.lib»;
                   let x7 : T := «Prelude.and» («Base.isEmpty» x4) («Base.isEmpty» x5);
                   let x8 : List
                     T := Const.children
                     (mk 0 [mk 0 [leaf 116, leaf 114, leaf 117, leaf 101],
                       mk 0 [leaf 97, leaf 110, leaf 100],
                       mk 0 [leaf 105,
                         leaf 109,
                         leaf 112,
                         leaf 108,
                         leaf 105,
                         leaf 101,
                         leaf 115],
                       mk 0 [leaf 97, leaf 108, leaf 108],
                       mk 0 [leaf 102, leaf 97, leaf 108, leaf 115, leaf 101],
                       mk 0 [leaf 110, leaf 111, leaf 116],
                       mk 0 [leaf 111, leaf 114],
                       mk 0 [leaf 101, leaf 120, leaf 105, leaf 115, leaf 116, leaf 115],
                       mk 0 [leaf 101,
                         leaf 120,
                         leaf 105,
                         leaf 115,
                         leaf 116,
                         leaf 115,
                         leaf 45,
                         leaf 117,
                         leaf 110,
                         leaf 105,
                         leaf 113,
                         leaf 117,
                         leaf 101]]);
                   let x9 : T := Const.sub x3 («Authoring.declaredAt» x0);
                   if (Const.lt x3 x6).label ≠ 0 then
                     let x10 : T := «Authoring.libName» x3;
                     if («Prelude.isSome» x10).label ≠ 0 then
                       «Authoring.listOf»
                         ((«Authoring.atomOf» (mk 0 [leaf 108, leaf 105, leaf 98])) ::
                           ((«Authoring.atomOf» («Prelude.get» x10)) ::
                             («Prelude.append» x4 («Prelude.reverse» x5))))
                     else
                       «Authoring.opaqueOf» (leaf 11) x5
                   else
                     if («Prelude.and» (Const.lt x3 x2) x7).label ≠ 0 then
                       «Authoring.atomOf» («Prelude.at» x0 (Const.sub x3 x6))
                     else
                       if («Prelude.and»
                         («Base.not» (Const.lt x3 x2))
                         (Const.lt x3 (Const.add x2 (leaf 9)))).label ≠ 0 then
                         let x10 : T := «Authoring.atomOf» («Prelude.at» x8 (Const.sub x3 x2));
                         if (x7).label ≠ 0 then
                           x10
                         else
                           «Authoring.listOf»
                             (x10 :: («Prelude.append» x4 («Prelude.reverse» x5)))
                       else
                         if («Prelude.and»
                           («Base.not» (Const.lt x3 («Authoring.declaredAt» x0)))
                           («Prelude.and»
                             (Const.lt x9 («Prelude.length» x1))
                             («Base.isEmpty» x4))).label ≠ 0 then
                           if («Base.isEmpty» x5).label ≠ 0 then
                             «Authoring.atomOf» («Prelude.at» x1 x9)
                           else
                             «Authoring.listOf»
                               ((«Authoring.atomOf» («Prelude.at» x1 x9)) :: («Prelude.reverse» x5))
                         else
                           «Authoring.opaqueOf» (leaf 11) x5);
    x6

def «Authoring.showStep» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (List T → T)) =>
    let x5 : List T →
      T := (fun (x5 : List T) =>
      let x6 : T := Const.label x3;
      let x7 : T := «Prelude.length» («Language.mArgs» x3);
      let x8 : T →
        List T →
          T := (fun (x8 : T) =>
        «Authoring/Shows.atOr»
          «Authoring.showNothing»
          x4
          (Const.add x8 (leaf 1)));
      let x9 : T → T := (fun (x9 : T) => x8 x9 x5);
      let x10 : T → T := «Authoring.showType» x2;
      let x11 : T → T := «Authoring.atomOf»;
      let x12 : T := «Authoring.nameOr»
        «Authoring.unnamed»
        («Prelude.single» (leaf 95))
        («Prelude.length» x5);
      let x13 : T := «Authoring.nameOr»
        «Authoring.unnamed»
        («Prelude.single» (leaf 95))
        (Const.add («Prelude.length» x5) (leaf 1));
      let x14 : T := «Language.mD» x3 (leaf 0);
      let x15 : List T := Const.children («Language.mD» x3 (leaf 1));
      let x16 : T := «Authoring.connectivesAt» x0;
      let x17 : T →
        T := (fun (_ : T) =>
        «Authoring.opaqueOf» x6 («Base.mapT» x9 («Base.range» x7)));
      if (Const.eq x6 (leaf 0)).label ≠ 0 then
        x11
          («Authoring.nameOr»
            («Prelude.at» x5 x14)
            («Theory.l5» (leaf 95) (leaf 102) (leaf 114) (leaf 101) (leaf 101))
            x14)
      else
        if (Const.eq x6 (leaf 1)).label ≠ 0 then
          x11 «Reader.kwUnitValue»
        else
          if («Prelude.and»
            (Const.eq x6 (leaf 2))
            (Const.eq x7 (leaf 2))).label ≠ 0 then
            «Authoring.listOf»
              («Theory.l3» (x11 «Reader.kwPair») (x9 (leaf 0)) (x9 (leaf 1)))
          else
            if («Prelude.and»
              (Const.eq x6 (leaf 3))
              (Const.eq x7 (leaf 1))).label ≠ 0 then
              «Authoring.listOf» («Theory.l2» (x11 «Reader.kwFst») (x9 (leaf 0)))
            else
              if («Prelude.and»
                (Const.eq x6 (leaf 4))
                (Const.eq x7 (leaf 1))).label ≠ 0 then
                «Authoring.listOf» («Theory.l2» (x11 «Reader.kwSnd») (x9 (leaf 0)))
              else
                if («Prelude.and»
                  (Const.eq x6 (leaf 5))
                  (Const.eq x7 (leaf 1))).label ≠ 0 then
                  «Authoring.listOf»
                    («Theory.l3»
                      (x11 «Reader.kwLam»)
                      («Authoring.listOf»
                        («Prelude.single»
                          («Authoring.listOf» («Theory.l2» (x11 x12) (x10 x14)))))
                      (x8 (leaf 0) (x12 :: x5)))
                else
                  if («Prelude.and»
                    (Const.eq x6 (leaf 6))
                    (Const.eq x7 (leaf 2))).label ≠ 0 then
                    if («Language.mIs»
                      (leaf 6)
                      (leaf 2)
                      («Language.mArg» x3 (leaf 0))).label ≠ 0 then
                      «Authoring.listOf»
                        («Prelude.append»
                          (Const.children (x9 (leaf 0)))
                          («Prelude.single» (x9 (leaf 1))))
                    else
                      «Authoring.listOf» («Theory.l2» (x9 (leaf 0)) (x9 (leaf 1)))
                  else
                    if («Prelude.and»
                      (Const.eq x6 (leaf 7))
                      (Const.eq x7 (leaf 1))).label ≠ 0 then
                      «Authoring.showPrim»
                        x14
                        («Base.mapT» x10 x15)
                        («Language.mArg» x3 (leaf 0))
                        (x9 (leaf 0))
                    else
                      if («Prelude.and»
                        (Const.eq x6 (leaf 8))
                        (Const.eq x7 (leaf 3))).label ≠ 0 then
                        «Authoring.listOf»
                          («Theory.l5»
                            (x11
                              (mk 0 [leaf 110,
                                leaf 97,
                                leaf 116,
                                leaf 45,
                                leaf 114,
                                leaf 101,
                                leaf 99]))
                            (x9 (leaf 0))
                            («Authoring.listOf» («Prelude.single» (x11 x12)))
                            (x8 (leaf 1) (x12 :: x5))
                            (x9 (leaf 2)))
                      else
                        if («Prelude.and»
                          (Const.eq x6 (leaf 9))
                          (Const.eq x7 (leaf 3))).label ≠ 0 then
                          «Authoring.listOf»
                            («Theory.l5»
                              (x11
                                (mk 0 [leaf 108,
                                  leaf 105,
                                  leaf 115,
                                  leaf 116,
                                  leaf 45,
                                  leaf 114,
                                  leaf 101,
                                  leaf 99]))
                              (x9 (leaf 0))
                              («Authoring.listOf» («Theory.l2» (x11 x12) (x11 x13)))
                              (x8 (leaf 1) (x13 :: (x12 :: x5)))
                              (x9 (leaf 2)))
                        else
                          if («Prelude.and»
                            (Const.eq x6 (leaf 10))
                            (Const.eq x7 (leaf 2))).label ≠ 0 then
                            «Authoring.listOf»
                              («Theory.l5»
                                (x11
                                  (mk 0 [leaf 114,
                                    leaf 111,
                                    leaf 115,
                                    leaf 101,
                                    leaf 45,
                                    leaf 114,
                                    leaf 101,
                                    leaf 99]))
                                (x10 x14)
                                («Authoring.listOf» («Prelude.single» (x11 x12)))
                                (x8 (leaf 0) (x12 :: x5))
                                (x9 (leaf 1)))
                          else
                            if (Const.eq x6 (leaf 11)).label ≠ 0 then
                              «Authoring.showCall»
                                x0
                                x1
                                x16
                                x14
                                («Base.mapT» x10 x15)
                                («Base.mapT» x9 («Base.range» x7))
                            else
                              if («Prelude.and»
                                (Const.eq x6 (leaf 12))
                                (Const.eq x7 (leaf 2))).label ≠ 0 then
                                «Authoring.listOf»
                                  («Theory.l3»
                                    (x11 (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108]))
                                    (x9 (leaf 0))
                                    (x9 (leaf 1)))
                              else
                                x17 (leaf 0));
    x5

def «Authoring.showTerm» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T) =>
    let x5 : T := Const.para
      (α := List T → T)
      («Authoring.showStep» x0 x1 x2)
      x3
      x4;
    x5

def «Authoring.displayRules» :=
  ((«Prover.nrRule» (leaf 3) («Derivation.terms» ([] : List T))) ::
    ((«Prover.nrRule» (leaf 4) («Derivation.terms» ([] : List T))) ::
      («Authoring/Rules.single»
        («Prover.nrRule» (leaf 5) («Derivation.terms» ([] : List T))))))

def «Authoring.showGoal» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (let x7 : List T := Const.children («Language.mD» x6 (leaf 5));
                   let x8 : List T := Const.children («Language.mD» x6 (leaf 6));
                   let x9 : T := «Prelude.length» x7;
                   let x10 : List
                     T := «Base.mapT»
                     (fun (x10 : T) =>
                       «Authoring.nameOr»
                         («Prelude.at» (Const.children («Language.mD» x6 (leaf 3))) x10)
                         («Prelude.single» (leaf 95))
                         (Const.sub (Const.sub x9 (leaf 1)) x10))
                     («Base.range» x9);
                   let x11 : T →
                     T := (fun (x11 : T) =>
                     «Authoring.showTerm»
                       x3
                       x4
                       x5
                       (let x12 : T := «Prover.eval»
                          x1
                          x2
                          («Prelude.length» x5)
                          «Authoring.displayRules»
                          (leaf 4096)
                          (leaf 3)
                          x7
                          x8
                          x11;
                        if (Const.eq (Const.label x12) (leaf 0)).label ≠ 0 then
                          let _ : List T := Const.children x12; x11
                        else
                          let x13 : List T := Const.children x12;
                          let x14 : T := Const.lcase
                            (α := T)
                            (β := T)
                            x13
                            (leaf 0)
                            (fun (x14 : T) (_ : List T) => x14);
                          let _ : List
                            T := Const.lcase
                            (α := T)
                            (β := List T)
                            x13
                            ([] : List T)
                            (fun (_ : T) (x16 : List T) => x16);
                          «Prover.nfTerm» x14)
                       x10);
                   let x12 : T := (if («Prelude.and»
                     (Const.lt (leaf 4) x0)
                     (Const.equal
                       («Language.mD» x6 (leaf 8))
                       («Tactics.ttL» («Authoring.connectivesAt» x3)))).label ≠ 0 then
                     x11 («Language.mD» x6 (leaf 7))
                   else
                     «Authoring.listOf»
                       («Theory.l3»
                         («Authoring.atomOf»
                           (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108]))
                         (x11 («Language.mD» x6 (leaf 7)))
                         (x11 («Language.mD» x6 (leaf 8)))));
                   let x13 : T := (if («Base.isEmpty» x8).label ≠ 0 then
                     x12
                   else
                     «Authoring.listOf»
                       ((«Authoring.atomOf»
                         (if (Const.lt (leaf 4) x0).label ≠ 0 then
                           mk 0 [leaf 97,
                             leaf 115,
                             leaf 115,
                             leaf 117,
                             leaf 109,
                             leaf 105,
                             leaf 110,
                             leaf 103]
                         else
                           mk 0 [leaf 105,
                             leaf 109,
                             leaf 112,
                             leaf 108,
                             leaf 105,
                             leaf 101,
                             leaf 115])) ::
                         («Prelude.append»
                           («Base.mapT»
                             (fun (x13 : T) =>
                               «Authoring.listOf»
                                 («Theory.l2»
                                   («Authoring.atomOf»
                                     («Authoring.nameOr»
                                       («Prelude.at»
                                         (Const.children («Language.mD» x6 (leaf 4)))
                                         x13)
                                       («Theory.l2» (leaf 95) (leaf 104))
                                       x13))
                                   (x11 («Prelude.at» x8 x13))))
                             («Base.range» («Prelude.length» x8)))
                           («Prelude.single» x12))));
                   «Authoring.listOf»
                     («Theory.l3»
                       («Authoring.atomOf»
                         (mk 0 [leaf 105,
                           leaf 110,
                           leaf 116,
                           leaf 101,
                           leaf 114,
                           leaf 110,
                           leaf 97,
                           leaf 108]))
                       («Authoring.listOf» («Base.mapT» «Authoring.atomOf» x5))
                       (if (Const.eq x9 (leaf 0)).label ≠ 0 then
                         x13
                       else
                         «Authoring.listOf»
                           («Theory.l3»
                             («Authoring.atomOf»
                               (mk 0 [leaf 102, leaf 111, leaf 114, leaf 97, leaf 108, leaf 108]))
                             («Authoring.listOf»
                               («Prelude.reverse»
                                 («Base.mapT»
                                   (fun (x14 : T) =>
                                     «Authoring.listOf»
                                       («Theory.l2»
                                         («Authoring.atomOf» («Prelude.at» x10 x14))
                                         («Authoring.showType» x5 («Prelude.at» x7 x14))))
                                   («Base.range» x9))))
                             x13))));
    x7

def «Authoring.reportOf» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := Const.node
      («Language.mD» x6 (leaf 0))
      («Theory.l3»
        («Language.mD» x6 (leaf 1))
        («Language.mD» x6 (leaf 2))
        («Authoring.showGoal» x0 x1 x2 x3 x4 x5 x6));
    x7

def «Authoring.request» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Authoring.requestName» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x3);
    x1

def «Authoring.requestThm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let x13 : T := x5;
                   let x14 : List T := Const.children x13;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let x16 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x16
                     (leaf 0)
                     (fun (x17 : T) (_ : List T) => x17);
                   let x18 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x16
                     ([] : List T)
                     (fun (_ : T) (x19 : List T) => x19);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x18
                     (leaf 0)
                     (fun (x19 : T) (_ : List T) => x19);
                   let x20 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x18
                     ([] : List T)
                     (fun (_ : T) (x21 : List T) => x21);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x20
                     (leaf 0)
                     (fun (x21 : T) (_ : List T) => x21);
                   let x22 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x20
                     ([] : List T)
                     (fun (_ : T) (x23 : List T) => x23);
                   let x23 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x22
                     (leaf 0)
                     (fun (x23 : T) (_ : List T) => x23);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x22
                     ([] : List T)
                     (fun (_ : T) (x25 : List T) => x25);
                   x23);
    x1

def «Authoring.requestScript» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x7);
    x1

def «Authoring.requestVersion» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x9);
    x1

def «Authoring.requestSpec» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x11);
    x1

def «Authoring.requestObjects» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1;
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x2
              (leaf 0)
              (fun (x3 : T) (_ : List T) => x3);
            let x4 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x2
              ([] : List T)
              (fun (_ : T) (x5 : List T) => x5);
            let x5 : T := Const.lcase
              (α := T)
              (β := T)
              x4
              (leaf 0)
              (fun (x5 : T) (_ : List T) => x5);
            let x6 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x4
              ([] : List T)
              (fun (_ : T) (x7 : List T) => x7);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x7 : T) (_ : List T) => x7);
            let x8 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x6
              ([] : List T)
              (fun (_ : T) (x9 : List T) => x9);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x8
              (leaf 0)
              (fun (x9 : T) (_ : List T) => x9);
            let x10 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x8
              ([] : List T)
              (fun (_ : T) (x11 : List T) => x11);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x10
              (leaf 0)
              (fun (x11 : T) (_ : List T) => x11);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x10
              ([] : List T)
              (fun (_ : T) (x13 : List T) => x13);
            let x13 : T := x5;
            let x14 : List T := Const.children x13;
            let x15 : T := Const.lcase
              (α := T)
              (β := T)
              x14
              (leaf 0)
              (fun (x15 : T) (_ : List T) => x15);
            let x16 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x14
              ([] : List T)
              (fun (_ : T) (x17 : List T) => x17);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x16
              (leaf 0)
              (fun (x17 : T) (_ : List T) => x17);
            let x18 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x16
              ([] : List T)
              (fun (_ : T) (x19 : List T) => x19);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x18
              (leaf 0)
              (fun (x19 : T) (_ : List T) => x19);
            let x20 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x18
              ([] : List T)
              (fun (_ : T) (x21 : List T) => x21);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x20
              (leaf 0)
              (fun (x21 : T) (_ : List T) => x21);
            let x22 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x20
              ([] : List T)
              (fun (_ : T) (x23 : List T) => x23);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x22
              (leaf 0)
              (fun (x23 : T) (_ : List T) => x23);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x22
              ([] : List T)
              (fun (_ : T) (x25 : List T) => x25);
            Const.children x15);
    x1

def «Authoring.normalOk» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (if («Prelude.isSome» x5).label ≠ 0 then
      let x6 : T := «Prelude.get» x5;
      «Prelude.and»
        (Const.lt (leaf 1) («Prelude.length» (Const.children x6)))
        («Prelude.and»
          («Prelude.isSome» («Authoring.depthOf» (Const.child x6 (leaf 1))))
          («Base.allT»
            («Authoring.ruleOk» x0 x1 x2 x3 x4)
            («Prelude.drop» (leaf 2) (Const.children x6))))
    else
      leaf 1);
    x6

def «Authoring.normalDepth» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   if («Prelude.isSome» x11).label ≠ 0 then
                     «Base.getD»
                       («Authoring.depthOf» (Const.child («Prelude.get» x11) (leaf 1)))
                       (leaf 1)
                   else
                     leaf 1);
    x1

def «Authoring.normalRules» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : List
      T := (let x4 : T := x3;
            let x5 : List T := Const.children x4;
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x5
              (leaf 0)
              (fun (x6 : T) (_ : List T) => x6);
            let x7 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x5
              ([] : List T)
              (fun (_ : T) (x8 : List T) => x8);
            let x8 : T := Const.lcase
              (α := T)
              (β := T)
              x7
              (leaf 0)
              (fun (x8 : T) (_ : List T) => x8);
            let x9 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x7
              ([] : List T)
              (fun (_ : T) (x10 : List T) => x10);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x9
              (leaf 0)
              (fun (x10 : T) (_ : List T) => x10);
            let x11 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x9
              ([] : List T)
              (fun (_ : T) (x12 : List T) => x12);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x11
              (leaf 0)
              (fun (x12 : T) (_ : List T) => x12);
            let x13 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x11
              ([] : List T)
              (fun (_ : T) (x14 : List T) => x14);
            let x14 : T := Const.lcase
              (α := T)
              (β := T)
              x13
              (leaf 0)
              (fun (x14 : T) (_ : List T) => x14);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x13
              ([] : List T)
              (fun (_ : T) (x16 : List T) => x16);
            let x16 : T := x8;
            let x17 : List T := Const.children x16;
            let x18 : T := Const.lcase
              (α := T)
              (β := T)
              x17
              (leaf 0)
              (fun (x18 : T) (_ : List T) => x18);
            let x19 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x17
              ([] : List T)
              (fun (_ : T) (x20 : List T) => x20);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x19
              (leaf 0)
              (fun (x20 : T) (_ : List T) => x20);
            let x21 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x19
              ([] : List T)
              (fun (_ : T) (x22 : List T) => x22);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x21
              (leaf 0)
              (fun (x22 : T) (_ : List T) => x22);
            let x23 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x21
              ([] : List T)
              (fun (_ : T) (x24 : List T) => x24);
            let x24 : T := Const.lcase
              (α := T)
              (β := T)
              x23
              (leaf 0)
              (fun (x24 : T) (_ : List T) => x24);
            let x25 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x23
              ([] : List T)
              (fun (_ : T) (x26 : List T) => x26);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x25
              (leaf 0)
              (fun (x26 : T) (_ : List T) => x26);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x25
              ([] : List T)
              (fun (_ : T) (x28 : List T) => x28);
            if («Prelude.isSome» x14).label ≠ 0 then
              «Authoring.rulesFrom»
                x0
                x1
                (Const.children x18)
                (Const.children x24)
                x2
                («Prelude.drop» (leaf 2) (Const.children («Prelude.get» x14)))
            else
              ([] : List T));
    x4

def «Authoring.failed» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    let x3 : T := Const.node (leaf 0) (x0 :: (x1 :: x2)); x3

def «Authoring.failure» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node
      (leaf 2)
      («Prelude.single» («Authoring.failed» x0 x1 ([] : List T)));
    x2

def «Authoring.requestOk» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Authoring.requestBad» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring.version0» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.child x1 (leaf 2);
                   let x3 : T := Const.child x1 (leaf 3);
                   «Prelude.and»
                     («Authoring.form»
                       x2
                       (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
                       (leaf 3))
                     («Prelude.and»
                       («Prelude.and»
                         («Reader.isAtom» (Const.child x2 (leaf 1)))
                         («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 1))) x0))
                       («Prelude.and»
                         («Prelude.and»
                           («Reader.isAtom» (Const.child x2 (leaf 2)))
                           («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 2))) x0))
                         («Prelude.and»
                           («Authoring.form» x3 (mk 0 [leaf 98, leaf 121]) (leaf 2))
                           («Authoring.form»
                             (Const.child x3 (leaf 1))
                             (mk 0 [leaf 110,
                               leaf 111,
                               leaf 114,
                               leaf 109,
                               leaf 97,
                               leaf 108,
                               leaf 105,
                               leaf 122,
                               leaf 101])
                             (leaf 2))))));
    x2

def «Authoring.theoremName» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      («Reader.isList» x0)
      (Const.lt
        (leaf 1)
        («Prelude.length» (Const.children x0)))).label ≠ 0 then
      «Reader.nameOf» (Const.child x0 (leaf 1))
    else
      Const.node (leaf 0) ([] : List T));
    x1

def «Authoring.readRequest» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (if («Prelude.and»
      («Prelude.or»
        («Authoring.form»
          x6
          (mk 0 [leaf 116,
            leaf 104,
            leaf 101,
            leaf 111,
            leaf 114,
            leaf 101,
            leaf 109])
          (leaf 4))
        («Prelude.and»
          (Const.lt (leaf 2) x0)
          («Prelude.and»
            («Authoring.form»
              x6
              (mk 0 [leaf 116,
                leaf 104,
                leaf 101,
                leaf 111,
                leaf 114,
                leaf 101,
                leaf 109])
              (leaf 5))
            («Authoring.headed»
              (Const.child x6 (leaf 4))
              (mk 0 [leaf 110, leaf 111, leaf 114, leaf 109, leaf 97, leaf 108])))))
      («Prelude.and»
        («Reader.isAtom» (Const.child x6 (leaf 1)))
        («Prelude.and»
          («Base.not»
            («Base.isEmpty» (Const.children (Const.child x6 (leaf 1)))))
          («Prelude.and»
            («Authoring.form»
              (Const.child x6 (leaf 3))
              (mk 0 [leaf 98, leaf 121])
              (leaf 2))
            («Prelude.or»
              (Const.lt (leaf 0) x0)
              («Authoring.version0» x3 x6)))))).label ≠ 0 then
      let x7 : T := «Authoring.readStatement»
        x0
        x1
        x2
        x3
        («Prelude.append» x3 x4)
        (Const.child x6 (leaf 2));
      if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x7; «Authoring.requestBad» (leaf 2)
      else
        let x8 : List T := Const.children x7;
        let x9 : T := Const.lcase
          (α := T)
          (β := T)
          x8
          (leaf 0)
          (fun (x9 : T) (_ : List T) => x9);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x8
          ([] : List T)
          (fun (_ : T) (x11 : List T) => x11);
        let x11 : T := x9;
        let x12 : List T := Const.children x11;
        let x13 : T := Const.lcase
          (α := T)
          (β := T)
          x12
          (leaf 0)
          (fun (x13 : T) (_ : List T) => x13);
        let x14 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x12
          ([] : List T)
          (fun (_ : T) (x15 : List T) => x15);
        let x15 : T := Const.lcase
          (α := T)
          (β := T)
          x14
          (leaf 0)
          (fun (x15 : T) (_ : List T) => x15);
        let x16 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x14
          ([] : List T)
          (fun (_ : T) (x17 : List T) => x17);
        let x17 : T := Const.lcase
          (α := T)
          (β := T)
          x16
          (leaf 0)
          (fun (x17 : T) (_ : List T) => x17);
        let x18 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x16
          ([] : List T)
          (fun (_ : T) (x19 : List T) => x19);
        let x19 : T := Const.lcase
          (α := T)
          (β := T)
          x18
          (leaf 0)
          (fun (x19 : T) (_ : List T) => x19);
        let x20 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x18
          ([] : List T)
          (fun (_ : T) (x21 : List T) => x21);
        let _ : T := Const.lcase
          (α := T)
          (β := T)
          x20
          (leaf 0)
          (fun (x21 : T) (_ : List T) => x21);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x20
          ([] : List T)
          (fun (_ : T) (x23 : List T) => x23);
        let x23 : T := Const.child (Const.child x6 (leaf 3)) (leaf 1);
        let x24 : T := (if («Authoring.form»
          x6
          (mk 0 [leaf 116,
            leaf 104,
            leaf 101,
            leaf 111,
            leaf 114,
            leaf 101,
            leaf 109])
          (leaf 5)).label ≠ 0 then
          «Prelude.some» (Const.child x6 (leaf 4))
        else
          «Prelude.none»);
        if («Prelude.and»
          («Authoring.readScript»
            x0
            (leaf 0)
            x2
            x3
            (Const.children x13)
            x5
            x23
            (leaf 0)
            ([] : List T)
            (Const.children x15)
            (Const.children x17)
            (Const.children x19)).1
          («Authoring.normalOk»
            x0
            x3
            (Const.children x13)
            (Const.children x19)
            x5
            x24)).label ≠ 0 then
          «Authoring.requestOk»
            («Authoring.request»
              («Reader.nameOf» (Const.child x6 (leaf 1)))
              x9
              x23
              x0
              x24)
        else
          «Authoring.requestBad» (leaf 3)
    else
      «Authoring.requestBad» (leaf 2));
    x7

def «Authoring.expandItems» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List
      T := Const.para
      (α := List T)
      (fun (x2 : T) (x3 : List (List T)) =>
        if («Reader.isAtom» x2).label ≠ 0 then
          let x4 : T := «Reader.lookupAbbrev» («Reader.nameOf» x2) x0;
          if («Prelude.isSome» x4).label ≠ 0 then
            Const.children («Prelude.get» x4)
          else
            «Prelude.single» x2
        else
          «Prelude.single»
            (Const.node
              (Const.label x2)
              (Const.foldr
                (α := List T)
                (β := List T)
                (fun (x4 : List T) (x5 : List T) => «Prelude.append» x4 x5)
                ([] : List T)
                x3)))
      x1;
    x2

def «Authoring.expandForms» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := «Prelude.reverse»
      (Const.foldr
        (α := T)
        (β := List T × List T)
        (fun (x2 : T) (x3 : List T × List T) =>
          if («Prelude.and»
            (Const.lt (leaf 2) x0)
            («Prelude.and»
              («Authoring.headed»
                x2
                (mk 0 [leaf 97,
                  leaf 98,
                  leaf 98,
                  leaf 114,
                  leaf 101,
                  leaf 118,
                  leaf 105,
                  leaf 97,
                  leaf 116,
                  leaf 105,
                  leaf 111,
                  leaf 110]))
              («Prelude.and»
                (Const.lt (leaf 2) («Prelude.length» (Const.children x2)))
                («Authoring.declared» (Const.child x2 (leaf 1)))))).label ≠ 0 then
            (((Const.node
              (leaf 0)
              («Theory.l2»
                («Reader.nameOf» (Const.child x2 (leaf 1)))
                (Const.node
                  (leaf 0)
                  (Const.foldr
                    (α := T)
                    (β := List T)
                    (fun (x4 : T) (x5 : List T) =>
                      «Prelude.append» («Authoring.expandItems» (x3).1 x4) x5)
                    ([] : List T)
                    («Prelude.drop» (leaf 2) (Const.children x2)))))) ::
              (x3).1),
              (x3).2)
          else
            ((x3).1, «Prelude.append» («Authoring.expandItems» (x3).1 x2) (x3).2))
        (([] : List T), ([] : List T))
        («Prelude.reverse» x1)).2;
    x2

def «Authoring.document» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring/ODoc.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/ODoc.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/ODoc.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/ODoc.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/ODoc.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/ODoc.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/ODoc.just» x2);
    x2

def «Authoring/ODoc.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.readDocument» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Reader.readSExps» (Const.children x0);
                   let x2 : T := Const.child («Prelude.get» x1) (leaf 0);
                   let x3 : T := «Authoring.number» (Const.child x2 (leaf 1));
                   if («Prelude.and»
                     («Prelude.isSome» x1)
                     («Prelude.and»
                       (Const.eq
                         («Prelude.length» (Const.children («Prelude.get» x1)))
                         (leaf 1))
                       («Prelude.and»
                         («Reader.isList» x2)
                         («Prelude.and»
                           («Authoring.word»
                             (Const.child x2 (leaf 0))
                             (mk 0 [leaf 112, leaf 114, leaf 111, leaf 111, leaf 102, leaf 115]))
                           («Prelude.and»
                             («Prelude.isSome» x3)
                             (Const.lt («Prelude.get» x3) (leaf 6))))))).label ≠ 0 then
                     let x4 : List
                       T := «Authoring.expandForms»
                       («Prelude.get» x3)
                       (Const.foldr
                         (α := T)
                         (β := List T)
                         (fun (x4 : T) (x5 : List T) =>
                           if («Prelude.and»
                             (Const.lt (leaf 1) («Prelude.get» x3))
                             («Prelude.or»
                               («Authoring.form»
                                 x4
                                 (mk 0 [leaf 105, leaf 109, leaf 112, leaf 111, leaf 114, leaf 116])
                                 (leaf 2))
                               («Authoring.form»
                                 x4
                                 (mk 0 [leaf 112,
                                   leaf 114,
                                   leaf 111,
                                   leaf 103,
                                   leaf 114,
                                   leaf 97,
                                   leaf 109])
                                 (leaf 2)))).label ≠ 0 then
                             x5
                           else
                             (x4 :: x5))
                         ([] : List T)
                         («Prelude.drop» (leaf 2) (Const.children x2)));
                     if («Base.isEmpty» x4).label ≠ 0 then
                       «Authoring/ODoc.nothing»
                     else
                       «Authoring/ODoc.just» («Authoring.document» («Prelude.get» x3) x4)
                   else
                     «Authoring/ODoc.nothing»);
    x1

def «Authoring.formList» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring/OForms.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OForms.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OForms.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OForms.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OForms.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OForms.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OForms.just» x2);
    x2

def «Authoring/OForms.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring/Items.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Items.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Items.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Items.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Items.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Items.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Items.tail» x1 x0;
    x2

def «Authoring/Items.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Items.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/ItemsOf.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring/ItemOut.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring.readDocuments» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        let x3 : T := x2;
        if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x3; «Authoring/OForms.nothing»
        else
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          let x7 : T := x5;
          let x8 : List T := Const.children x7;
          let x9 : T := Const.lcase
            (α := T)
            (β := T)
            x8
            (leaf 0)
            (fun (x9 : T) (_ : List T) => x9);
          let x10 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x8
            ([] : List T)
            (fun (_ : T) (x11 : List T) => x11);
          let x11 : List T := x10;
          let x12 : T := «Authoring.readDocument» x1;
          if (Const.eq (Const.label x12) (leaf 0)).label ≠ 0 then
            let _ : List T := Const.children x12; «Authoring/OForms.nothing»
          else
            let x13 : List T := Const.children x12;
            let x14 : T := Const.lcase
              (α := T)
              (β := T)
              x13
              (leaf 0)
              (fun (x14 : T) (_ : List T) => x14);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x13
              ([] : List T)
              (fun (_ : T) (x16 : List T) => x16);
            let x16 : T := x14;
            let x17 : List T := Const.children x16;
            let x18 : T := Const.lcase
              (α := T)
              (β := T)
              x17
              (leaf 0)
              (fun (x18 : T) (_ : List T) => x18);
            let x19 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x17
              ([] : List T)
              (fun (_ : T) (x20 : List T) => x20);
            let x20 : List T := x19;
            if («Prelude.or»
              («Prelude.and»
                (Const.eq x18 (leaf 0))
                (Const.lt (leaf 1) («Prelude.length» x0)))
              («Prelude.and»
                (Const.lt (leaf 0) («Authoring/Items.length» x11))
                (Const.lt x9 x18))).label ≠ 0 then
              «Authoring/OForms.nothing»
            else
              «Authoring/OForms.just»
                («Authoring.formList»
                  (if (Const.eq («Authoring/Items.length» x11) (leaf 0)).label ≠ 0 then
                    x18
                  else
                    x9)
                  («Authoring/Items.append»
                    («Authoring/ItemsOf.map» (fun (x21 : T) => «Language.pr» x18 x21) x20)
                    x11)))
      (if («Base.isEmpty» x0).label ≠ 0 then
        «Authoring/OForms.nothing»
      else
        «Authoring/OForms.just» («Authoring.formList» (leaf 0) ([] : List T)))
      x0;
    x1

def «Authoring/Requests.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Requests.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Requests.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Requests.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Authoring/Requests.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Requests.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Requests.tail» x1 x0;
    x2

def «Authoring/Requests.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Requests.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.results» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring.Results.member» :=
  fun (x0 : T) =>
    Const.child
      (Const.fold
        (α := T)
        (fun (x1 : T) (x2 : List T) =>
          let x3 : T := Const.node (leaf 0) x2;
          Const.node
            (leaf 0)
            ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
              if (Const.lt
                (leaf 1)
                (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                Const.foldr
                  (α := T)
                  (β := T)
                  (fun (x4 : T) (x5 : T) =>
                    if (Const.child x4 (leaf 1)).label ≠ 0 then x5 else leaf 0)
                  (leaf 1)
                  (Const.iter
                    (α := List T)
                    (fun (x4 : List T) =>
                      Const.lcase
                        (α := T)
                        (β := List T)
                        x4
                        ([] : List T)
                        (fun (_ : T) (x6 : List T) => x6))
                    x2
                    (leaf 1))
              else
                leaf 0
            else
              leaf 0).label ≠ 0 then
              leaf 1
            else
              leaf 0) ::
              ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                  Const.child (Const.child x3 (leaf 0)) (leaf 2)
                else
                  leaf 0
              else
                if (Const.eq x1 (leaf 1)).label ≠ 0 then
                  if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                    Const.child (Const.child x3 (leaf 0)) (leaf 3)
                  else
                    leaf 0
                else
                  if (Const.eq x1 (leaf 2)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                      Const.child (Const.child x3 (leaf 0)) (leaf 4)
                    else
                      leaf 0
                  else
                    if (Const.eq x1 (leaf 3)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                        Const.child (Const.child x3 (leaf 0)) (leaf 5)
                      else
                        leaf 0
                    else
                      if (Const.eq x1 (leaf 4)).label ≠ 0 then
                        Const.eq (Const.arity x3) (leaf 3)
                      else
                        if (Const.eq x1 (leaf 5)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 3)
                        else
                          if (Const.eq x1 (leaf 6)).label ≠ 0 then
                            Const.eq (Const.arity x3) (leaf 4)
                          else
                            leaf 0).label ≠ 0 then
                leaf 1
              else
                leaf 0) ::
                ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                  if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                    if (Const.child (Const.child x3 (leaf 1)) (leaf 6)).label ≠ 0 then
                      Const.child (Const.child x3 (leaf 2)) (leaf 10)
                    else
                      leaf 0
                  else
                    leaf 0
                else
                  leaf 0).label ≠ 0 then
                  leaf 1
                else
                  leaf 0) ::
                  ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 3)).label ≠ 0 then
                      if (Const.child (Const.child x3 (leaf 0)) (leaf 7)).label ≠ 0 then
                        if (Const.child (Const.child x3 (leaf 1)) (leaf 8)).label ≠ 0 then
                          Const.child (Const.child x3 (leaf 2)) (leaf 9)
                        else
                          leaf 0
                      else
                        leaf 0
                    else
                      leaf 0
                  else
                    leaf 0).label ≠ 0 then
                    leaf 1
                  else
                    leaf 0) ::
                    ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                        Const.child (Const.child x3 (leaf 1)) (leaf 6)
                      else
                        leaf 0
                    else
                      leaf 0).label ≠ 0 then
                      leaf 1
                    else
                      leaf 0) ::
                      ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                        Const.eq (Const.arity x3) (leaf 4)
                      else
                        leaf 0).label ≠ 0 then
                        leaf 1
                      else
                        leaf 0) ::
                        ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                          Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                        else
                          leaf 0).label ≠ 0 then
                          leaf 1
                        else
                          leaf 0) ::
                          ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                            Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                          else
                            leaf 0).label ≠ 0 then
                            leaf 1
                          else
                            leaf 0) ::
                            ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                              if (Const.lt
                                (leaf 0)
                                (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                                Const.foldr
                                  (α := T)
                                  (β := T)
                                  (fun (x4 : T) (x5 : T) =>
                                    if (Const.child x4 (leaf 9)).label ≠ 0 then x5 else leaf 0)
                                  (leaf 1)
                                  (Const.iter
                                    (α := List T)
                                    (fun (x4 : List T) =>
                                      Const.lcase
                                        (α := T)
                                        (β := List T)
                                        x4
                                        ([] : List T)
                                        (fun (_ : T) (x6 : List T) => x6))
                                    x2
                                    (leaf 0))
                              else
                                leaf 0
                            else
                              leaf 0).label ≠ 0 then
                              leaf 1
                            else
                              leaf 0) ::
                              ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                Const.eq (Const.arity x3) (leaf 2)
                              else
                                leaf 0).label ≠ 0 then
                                leaf 1
                              else
                                leaf 0) ::
                                ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                  Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                                else
                                  leaf 0).label ≠ 0 then
                                  leaf 1
                                else
                                  leaf 0) ::
                                  ([] : List T)))))))))))))
        x0)
      (leaf 0)

def «Authoring/EachDecl.all» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Authoring/EachDecl.any» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Authoring/EachDecl.isEmpty» :=
  fun (x0 : List T) =>
    let x1 : T := Const.eq
      (Const.foldr
        (α := T)
        (β := T)
        (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
        (leaf 0)
        x0)
      (leaf 0);
    x1

def «Authoring/EachDecl.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := Const.foldr
              (α := T)
              (β := T)
              (fun (_ : T) (x3 : T) => Const.add x3 (leaf 1))
              (leaf 0)
              x1;
            (Const.foldr
              (α := T)
              (β := T × List T)
              (fun (x3 : T) (x4 : T × List T) =>
                (Const.add (x4).1 (leaf 1),
                  if (Const.lt
                    (Const.sub (Const.sub x2 (x4).1) (leaf 1))
                    x0).label ≠ 0 then
                    (x3 :: (x4).2)
                  else
                    (x4).2))
              (leaf 0, ([] : List T))
              x1).2);
    x2

def «Authoring.noResults» :=
  «Authoring.results» (Const.node (leaf 0) ([] : List T)) ([] : List T)

def «Authoring.readDefinition» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : List T := Const.children (Const.child x3 (leaf 2));
                   let x5 : T := «Authoring.itype»
                     ([] : List T)
                     (Const.child x3 (leaf 3));
                   if («Prelude.and»
                     («Reader.isList» (Const.child x3 (leaf 2)))
                     («Prelude.and»
                       («Base.allT» («Authoring.ibinder» x0 ([] : List T)) x4)
                       («Prelude.and»
                         («Authoring.distinctFrom»
                           ([] : List T)
                           («Base.mapT» «Authoring.binderName» x4))
                         («Prelude.isSome» x5)))).label ≠ 0 then
                     let x6 : T := «Authoring.iterm»
                       x0
                       x1
                       x2
                       ([] : List T)
                       (Const.child x3 (leaf 4))
                       («Prelude.reverse» («Base.mapT» «Authoring.binderName» x4))
                       («Prelude.reverse»
                         («Base.mapT»
                           (fun (x6 : T) => «Authoring.kernelType» x2 (Const.child x6 (leaf 1)))
                           x4));
                     if («Prelude.isSome» x6).label ≠ 0 then
                       «Language/OLDefn.just»
                         («Language.ldefn»
                           (leaf 0)
                           («Language.objs»
                             («Prelude.reverse»
                               («Base.mapT»
                                 (fun (x7 : T) =>
                                   «Base.getD»
                                     («Authoring.itype» ([] : List T) (Const.child x7 (leaf 1)))
                                     «Theory.one»)
                                 x4)))
                           («Prelude.get» x5)
                           («Prelude.get» x6))
                     else
                       «Language/OLDefn.nothing»
                   else
                     «Language/OLDefn.nothing»);
    x4

def «Authoring.reading» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Authoring.namesOfFour» :=
  «Prelude.single»
    (Const.node
      (leaf 0)
      («Theory.l2» (mk 0 [leaf 78, leaf 97, leaf 116]) «Authoring.natRef»))

def «Authoring.readForm» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := x3;
                   let x5 : List T := Const.children x4;
                   let x6 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x5
                     (leaf 0)
                     (fun (x6 : T) (_ : List T) => x6);
                   let x7 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x5
                     ([] : List T)
                     (fun (_ : T) (x8 : List T) => x8);
                   let x8 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x7
                     (leaf 0)
                     (fun (x8 : T) (_ : List T) => x8);
                   let x9 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x7
                     ([] : List T)
                     (fun (_ : T) (x10 : List T) => x10);
                   let x10 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x9
                     (leaf 0)
                     (fun (x10 : T) (_ : List T) => x10);
                   let x11 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x9
                     ([] : List T)
                     (fun (_ : T) (x12 : List T) => x12);
                   let x12 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x11
                     (leaf 0)
                     (fun (x12 : T) (_ : List T) => x12);
                   let x13 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x11
                     ([] : List T)
                     (fun (_ : T) (x14 : List T) => x14);
                   let x14 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x13
                     (leaf 0)
                     (fun (x14 : T) (_ : List T) => x14);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x13
                     ([] : List T)
                     (fun (_ : T) (x16 : List T) => x16);
                   let x16 : T := x8;
                   let x17 : List T := Const.children x16;
                   let x18 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x17
                     (leaf 0)
                     (fun (x18 : T) (_ : List T) => x18);
                   let x19 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x17
                     ([] : List T)
                     (fun (_ : T) (x20 : List T) => x20);
                   let x20 : List T := x19;
                   let x21 : T := x12;
                   let x22 : List T := Const.children x21;
                   let x23 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x22
                     (leaf 0)
                     (fun (x23 : T) (_ : List T) => x23);
                   let x24 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x22
                     ([] : List T)
                     (fun (_ : T) (x25 : List T) => x25);
                   let x25 : List T := x24;
                   let x26 : T := «Language.p1» x2;
                   let x27 : T := (if (Const.lt (leaf 3) x26).label ≠ 0 then
                     «Authoring.withNames» (Const.children x10) («Language.p2» x2)
                   else
                     «Language.p2» x2);
                   if («Prelude.isSome» x14).label ≠ 0 then
                     x3
                   else
                     if («Prelude.and»
                       (Const.lt (leaf 3) x26)
                       («Authoring.headed»
                         («Language.p2» x2)
                         (mk 0 [leaf 100,
                           leaf 101,
                           leaf 102,
                           leaf 105,
                           leaf 110,
                           leaf 105,
                           leaf 116,
                           leaf 105,
                           leaf 111,
                           leaf 110]))).label ≠ 0 then
                       let x28 : T := Const.child x27 (leaf 1);
                       let x29 : T := «Authoring.reading»
                         x6
                         x8
                         x10
                         x12
                         («Prelude.some» («Authoring.theoremName» («Language.p2» x2)));
                       if («Prelude.and»
                         («Authoring.form»
                           x27
                           (mk 0 [leaf 100,
                             leaf 101,
                             leaf 102,
                             leaf 105,
                             leaf 110,
                             leaf 105,
                             leaf 116,
                             leaf 105,
                             leaf 111,
                             leaf 110])
                           (leaf 5))
                         («Prelude.and»
                           («Authoring.bindable» x26 x28)
                           («Base.not»
                             («Authoring.has» («Reader.nameOf» x28) x1)))).label ≠ 0 then
                         let x30 : T := «Authoring.readDefinition» x26 x0 x1 x27;
                         if (Const.eq (Const.label x30) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x30; x29
                         else
                           let x31 : List T := Const.children x30;
                           let x32 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x31
                             (leaf 0)
                             (fun (x32 : T) (_ : List T) => x32);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x31
                             ([] : List T)
                             (fun (_ : T) (x34 : List T) => x34);
                           let x34 : T := «Derivation.declStep»
                             x6
                             ([] : List T)
                             («Derivation.declDef» x32);
                           if (Const.eq (Const.label x34) (leaf 0)).label ≠ 0 then
                             let _ : List T := Const.children x34; x29
                           else
                             let x35 : List T := Const.children x34;
                             let x36 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x35
                               (leaf 0)
                               (fun (x36 : T) (_ : List T) => x36);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x35
                               ([] : List T)
                               (fun (_ : T) (x38 : List T) => x38);
                             let x38 : T := x36;
                             let x39 : List T := Const.children x38;
                             let x40 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x39
                               (leaf 0)
                               (fun (x40 : T) (_ : List T) => x40);
                             let x41 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x39
                               ([] : List T)
                               (fun (_ : T) (x42 : List T) => x42);
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x41
                               (leaf 0)
                               (fun (x42 : T) (_ : List T) => x42);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x41
                               ([] : List T)
                               (fun (_ : T) (x44 : List T) => x44);
                             «Authoring.reading»
                               x40
                               («Authoring.results»
                                 (Const.node
                                   (leaf 0)
                                   («Prelude.append»
                                     (Const.children x18)
                                     («Prelude.single» («Reader.nameOf» x28))))
                                 («Authoring/Decls.append»
                                   x20
                                   («Authoring/Decls.single» («Derivation.declDef» x32))))
                               (Const.node
                                 (leaf 0)
                                 ((Const.node
                                   (leaf 0)
                                   («Theory.l2»
                                     («Reader.nameOf» x28)
                                     («Authoring.declaredRef»
                                       («Prelude.length» (Const.children x18))
                                       («Prelude.length»
                                         (Const.children (Const.child x27 (leaf 2))))))) ::
                                   (Const.children x10)))
                               x12
                               x14
                       else
                         x29
                     else
                       «Authoring.reading»
                         x6
                         x8
                         x10
                         («Authoring.formList»
                           x23
                           («Authoring/Items.append»
                             x25
                             («Authoring/Items.single» («Language.pr» x26 x27))))
                         x14);
    x4

def «Authoring.requests» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    Const.node (leaf 0) (x0 :: (x1 :: x2))

def «Authoring.readOk» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Authoring.readBad» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Authoring.firstRepeated» :=
  fun (x0 : List T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := List T × T)
      (fun (x1 : T) (x2 : List T × T) =>
        ((x1 :: (x2).1),
          if («Authoring.has» x1 (x2).1).label ≠ 0 then
            «Prelude.some» x1
          else
            (x2).2))
      (([] : List T), «Prelude.none»)
      («Prelude.reverse» x0)).2;
    x1

def «Authoring.readTheorems» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := (let x6 : List
                     T := «Authoring/ItemOut.map»
                     (fun (x6 : T) => «Authoring.theoremName» («Language.p2» x6))
                     x5;
                   Const.foldr
                     (α := T)
                     (β := T)
                     (fun (x7 : T) (x8 : T) =>
                       let x9 : T := «Authoring/Items.atOr»
                         («Language.pr» (leaf 0) (leaf 0))
                         x5
                         x7;
                       let x10 : T := «Authoring.readRequest»
                         («Language.p1» x9)
                         x1
                         x2
                         x3
                         x6
                         («Base.take» x7 x6)
                         («Language.p2» x9);
                       if (Const.eq (Const.label x10) (leaf 1)).label ≠ 0 then
                         let x11 : List T := Const.children x10;
                         let x12 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x11
                           (leaf 0)
                           (fun (x12 : T) (_ : List T) => x12);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x11
                           ([] : List T)
                           (fun (_ : T) (x14 : List T) => x14);
                         «Authoring.readBad» x12 («Prelude.at» x6 x7)
                       else
                         let x11 : List T := Const.children x10;
                         let x12 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x11
                           (leaf 0)
                           (fun (x12 : T) (_ : List T) => x12);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x11
                           ([] : List T)
                           (fun (_ : T) (x14 : List T) => x14);
                         let x14 : T := x8;
                         if (Const.eq (Const.label x14) (leaf 1)).label ≠ 0 then
                           let x15 : List T := Const.children x14;
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x15
                             (leaf 0)
                             (fun (x16 : T) (_ : List T) => x16);
                           let x17 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x15
                             ([] : List T)
                             (fun (_ : T) (x18 : List T) => x18);
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x17
                             (leaf 0)
                             (fun (x18 : T) (_ : List T) => x18);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x17
                             ([] : List T)
                             (fun (_ : T) (x20 : List T) => x20);
                           x8
                         else
                           let x15 : List T := Const.children x14;
                           let x16 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x15
                             (leaf 0)
                             (fun (x16 : T) (_ : List T) => x16);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x15
                             ([] : List T)
                             (fun (_ : T) (x18 : List T) => x18);
                           let x18 : T := x16;
                           let x19 : List T := Const.children x18;
                           let x20 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x19
                             (leaf 0)
                             (fun (x20 : T) (_ : List T) => x20);
                           let x21 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x19
                             ([] : List T)
                             (fun (_ : T) (x22 : List T) => x22);
                           let x22 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x21
                             (leaf 0)
                             (fun (x22 : T) (_ : List T) => x22);
                           let x23 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x21
                             ([] : List T)
                             (fun (_ : T) (x24 : List T) => x24);
                           let x24 : List T := x23;
                           «Authoring.readOk» («Authoring.requests» x20 x22 (x12 :: x24)))
                     («Authoring.readOk» («Authoring.requests» x0 x4 ([] : List T)))
                     («Base.range» («Prelude.length» x6)));
    x6

def «Authoring.readSources» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «Authoring.readDocuments» x3;
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x4;
                     «Authoring.readBad» (leaf 0) (Const.node (leaf 0) ([] : List T))
                   else
                     let x5 : List T := Const.children x4;
                     let x6 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     let x8 : T := x6;
                     let x9 : List T := Const.children x8;
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let x11 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : List T := x11;
                     let x13 : List
                       T := «Authoring/ItemOut.map»
                       (fun (x13 : T) => «Authoring.theoremName» («Language.p2» x13))
                       x12;
                     let x14 : T := «Authoring.firstRepeated»
                       (if (Const.lt (leaf 3) x10).label ≠ 0 then
                         ((mk 0 [leaf 78, leaf 97, leaf 116]) :: x13)
                       else
                         x13);
                     if («Prelude.isSome» x14).label ≠ 0 then
                       «Authoring.readBad» (leaf 1) («Prelude.get» x14)
                     else
                       let x15 : T := Const.foldr
                         (α := T)
                         (β := T → T)
                         (fun (x15 : T) (x16 : T → T) (x17 : T) =>
                           x16 («Authoring.readForm» x0 x1 x15 x17))
                         (fun (x15 : T) => x15)
                         x12
                         («Authoring.reading»
                           («Authoring.globalsFor» x10 x2)
                           «Authoring.noResults»
                           (Const.node (leaf 0) «Authoring.namesOfFour»)
                           («Authoring.formList» x10 ([] : List T))
                           «Prelude.none»);
                       let x16 : List T := Const.children x15;
                       let x17 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x16
                         (leaf 0)
                         (fun (x17 : T) (_ : List T) => x17);
                       let x18 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x16
                         ([] : List T)
                         (fun (_ : T) (x19 : List T) => x19);
                       let x19 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x18
                         (leaf 0)
                         (fun (x19 : T) (_ : List T) => x19);
                       let x20 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x18
                         ([] : List T)
                         (fun (_ : T) (x21 : List T) => x21);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x20
                         (leaf 0)
                         (fun (x21 : T) (_ : List T) => x21);
                       let x22 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x20
                         ([] : List T)
                         (fun (_ : T) (x23 : List T) => x23);
                       let x23 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x22
                         (leaf 0)
                         (fun (x23 : T) (_ : List T) => x23);
                       let x24 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x22
                         ([] : List T)
                         (fun (_ : T) (x25 : List T) => x25);
                       let x25 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x24
                         (leaf 0)
                         (fun (x25 : T) (_ : List T) => x25);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x24
                         ([] : List T)
                         (fun (_ : T) (x27 : List T) => x27);
                       if («Prelude.isSome» x25).label ≠ 0 then
                         «Authoring.readBad» (leaf 8) («Prelude.get» x25)
                       else
                         let x27 : T := x23;
                         let x28 : List T := Const.children x27;
                         let _ : T := Const.lcase
                           (α := T)
                           (β := T)
                           x28
                           (leaf 0)
                           (fun (x29 : T) (_ : List T) => x29);
                         let x30 : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x28
                           ([] : List T)
                           (fun (_ : T) (x31 : List T) => x31);
                         let x31 : List T := x30;
                         if (Const.eq («Authoring/Items.length» x31) (leaf 0)).label ≠ 0 then
                           «Authoring.readBad» (leaf 0) (Const.node (leaf 0) ([] : List T))
                         else
                           «Authoring.readTheorems» x10 x17 x0 x1 x19 x31);
    x4

def «Authoring.proving» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «Authoring.stuck» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 1)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Authoring/OEntries.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OEntries.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OEntries.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Authoring/OEntries.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Authoring/OEntries.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Authoring/OEntries.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OEntries.just» x2);
    x2

def «Authoring/OEntries.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Authoring.admit» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Derivation.declStep» x0 x1 x2;
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; «Authoring/OEntries.nothing»
                   else
                     let x4 : List T := Const.children x3;
                     let x5 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x4
                       (leaf 0)
                       (fun (x5 : T) (_ : List T) => x5);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x4
                       ([] : List T)
                       (fun (_ : T) (x7 : List T) => x7);
                     let x7 : T := x5;
                     let x8 : List T := Const.children x7;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let x10 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     «Authoring/OEntries.just» x11);
    x3

def «Authoring.derive» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : List T)
    (x8 : T) =>
    let x9 : T := (let x9 : T := x8;
                   let x10 : List T := Const.children x9;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let x12 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let x13 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x12
                     (leaf 0)
                     (fun (x13 : T) (_ : List T) => x13);
                   let x14 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   let x15 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let x16 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   let x17 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x16
                     (leaf 0)
                     (fun (x17 : T) (_ : List T) => x17);
                   let x18 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x16
                     ([] : List T)
                     (fun (_ : T) (x19 : List T) => x19);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x18
                     (leaf 0)
                     (fun (x19 : T) (_ : List T) => x19);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x18
                     ([] : List T)
                     (fun (_ : T) (x21 : List T) => x21);
                   let x21 : T := x13;
                   let x22 : List T := Const.children x21;
                   let x23 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x22
                     (leaf 0)
                     (fun (x23 : T) (_ : List T) => x23);
                   let x24 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x22
                     ([] : List T)
                     (fun (_ : T) (x25 : List T) => x25);
                   let x25 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x24
                     (leaf 0)
                     (fun (x25 : T) (_ : List T) => x25);
                   let x26 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x24
                     ([] : List T)
                     (fun (_ : T) (x27 : List T) => x27);
                   let x27 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x26
                     (leaf 0)
                     (fun (x27 : T) (_ : List T) => x27);
                   let x28 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x26
                     ([] : List T)
                     (fun (_ : T) (x29 : List T) => x29);
                   let x29 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x28
                     (leaf 0)
                     (fun (x29 : T) (_ : List T) => x29);
                   let x30 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x28
                     ([] : List T)
                     (fun (_ : T) (x31 : List T) => x31);
                   let x31 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x30
                     (leaf 0)
                     (fun (x31 : T) (_ : List T) => x31);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x30
                     ([] : List T)
                     (fun (_ : T) (x33 : List T) => x33);
                   let x33 : T := x31;
                   let x34 : List T := Const.children x33;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x34
                     (leaf 0)
                     (fun (x35 : T) (_ : List T) => x35);
                   let x36 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x34
                     ([] : List T)
                     (fun (_ : T) (x37 : List T) => x37);
                   let x37 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x36
                     (leaf 0)
                     (fun (x37 : T) (_ : List T) => x37);
                   let x38 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x36
                     ([] : List T)
                     (fun (_ : T) (x39 : List T) => x39);
                   let x39 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x38
                     (leaf 0)
                     (fun (x39 : T) (_ : List T) => x39);
                   let x40 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x38
                     ([] : List T)
                     (fun (_ : T) (x41 : List T) => x41);
                   let x41 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x40
                     (leaf 0)
                     (fun (x41 : T) (_ : List T) => x41);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x40
                     ([] : List T)
                     (fun (_ : T) (x43 : List T) => x43);
                   let x43 : T := x37;
                   let x44 : List T := Const.children x43;
                   let x45 : List T := x44;
                   let x46 : T := x39;
                   let x47 : List T := Const.children x46;
                   let x48 : List T := x47;
                   «Formula.prove»
                     («Authoring.connectivesAt» x6)
                     ((«Authoring.readScript»
                       x17
                       x4
                       x5
                       x6
                       (Const.children x23)
                       x7
                       x15
                       x0
                       ([] : List T)
                       (Const.children x25)
                       (Const.children x27)
                       (Const.children x29)).2
                       x1
                       x2
                       x3)
                     x45
                     x48
                     x41);
    x9

def «Authoring.companion» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := x6;
                   let x8 : List T := Const.children x7;
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let x12 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let x13 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x12
                     (leaf 0)
                     (fun (x13 : T) (_ : List T) => x13);
                   let x14 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   let x15 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   let x17 : T := x11;
                   let x18 : List T := Const.children x17;
                   let x19 : List T := x18;
                   let x20 : T := x13;
                   let x21 : List T := Const.children x20;
                   let x22 : List T := x21;
                   let x23 : T := (let x23 : T := «Derivation.eqParts» x15;
                                   if (Const.eq (Const.label x23) (leaf 1)).label ≠ 0 then
                                     let x24 : List T := Const.children x23;
                                     let x25 : T := Const.lcase
                                       (α := T)
                                       (β := T)
                                       x24
                                       (leaf 0)
                                       (fun (x25 : T) (_ : List T) => x25);
                                     let _ : List
                                       T := Const.lcase
                                       (α := T)
                                       (β := List T)
                                       x24
                                       ([] : List T)
                                       (fun (_ : T) (x27 : List T) => x27);
                                     x25
                                   else
                                     let _ : List T := Const.children x23;
                                     «Language.pr» x15 («Tactics.ttL» x3));
                   let x24 : T := «Language.mEq» («Language.p1» x23) («Language.p2» x23);
                   let x25 : T := «Prover.dNode»
                     (leaf 27)
                     («Theory.l3»
                       x5
                       (Const.node (leaf 0) («Base.mapT» «Theory.x» («Base.range» x9)))
                       (Const.node
                         (leaf 0)
                         («Base.mapT» «Language.var» («Base.range» («Prelude.length» x19)))))
                     («Base.mapT»
                       (fun (x25 : T) =>
                         «Prover.dNode» (leaf 21) («Prelude.single» x25) ([] : List T))
                       («Base.range» («Prelude.length» x22)));
                   let x26 : T := (let x26 : T := «Derivation.eqParts» x15;
                                   if (Const.eq (Const.label x26) (leaf 1)).label ≠ 0 then
                                     let x27 : List T := Const.children x26;
                                     let _ : T := Const.lcase
                                       (α := T)
                                       (β := T)
                                       x27
                                       (leaf 0)
                                       (fun (x28 : T) (_ : List T) => x28);
                                     let _ : List
                                       T := Const.lcase
                                       (α := T)
                                       (β := List T)
                                       x27
                                       ([] : List T)
                                       (fun (_ : T) (x30 : List T) => x30);
                                     x25
                                   else
                                     let _ : List T := Const.children x26;
                                     «Prover.dNode»
                                       (leaf 25)
                                       ([] : List T)
                                       («Theory.l2» «Tactics.trueI» x25));
                   «Prover.bindNT»
                     («Prover.eval» x0 x1 x9 x2 (leaf 4096) x4 x19 x22 («Language.p1» x23))
                     (fun (x27 : T) =>
                       «Prover.bindNT»
                         («Prover.eval» x0 x1 x9 x2 (leaf 4096) x4 x19 x22 («Language.p2» x23))
                         (fun (x28 : T) =>
                           «Prelude.some»
                             (Const.node
                               (leaf 0)
                               («Theory.l3»
                                 («Prover.nfTerm» x27)
                                 («Prover.nfTerm» x28)
                                 («Prover.dNode»
                                   (leaf 24)
                                   («Prelude.single» x24)
                                   («Theory.l2»
                                     («Prover.dNode»
                                       (leaf 2)
                                       ([] : List T)
                                       («Theory.l2»
                                         («Prover.mDeriv» («Prover.nfMarked» x27))
                                         («Prover.mDeriv» («Prover.nfMarked» x28))))
                                     x26)))))));
    x7

def «Authoring.withSides» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x0;
                   let x4 : List T := Const.children x3;
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   «Derivation.mkThm» x5 x7 x9 («Language.mEq» x1 x2));
    x3

def «Authoring.sourceNames» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      x1
    else
      let x2 : List T := «Prelude.drop» («Authoring.entryBase» x0) x1;
      «Base.mapT»
        (fun (x3 : T) => «Prelude.at» x2 (Const.mul (leaf 2) x3))
        («Base.range» (Const.div («Prelude.length» x2) (leaf 2))));
    x2

def «Authoring.noNode» := Const.node (leaf 0) ([] : List T)

def «Authoring.cacheItem» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := Const.node
      (leaf 0)
      ((«Authoring.requestName» x0) ::
        ((«Authoring.requestThm» x0) ::
          ((«Authoring.requestScript» x0) ::
            ((«Authoring.requestSpec» x0) ::
              ((«Authoring.requestVersion» x0) :: («Theory.l4» x1 x2 x3 x4))))));
    x5

def «Authoring.cacheItems» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (if («Prelude.and»
      (Const.lt (leaf 1) (Const.arity x1))
      («Prelude.and»
        (Const.eq (Const.arity (Const.child x1 (leaf 0))) (leaf 0))
        (Const.eq (Const.child x1 (leaf 0)) x0))).label ≠ 0 then
      Const.children (Const.child x1 (leaf 1))
    else
      ([] : List T));
    x2

def «Authoring.sameDeclared» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.equal
      (if (Const.eq (Const.arity x0) (leaf 3)).label ≠ 0 then
        Const.child x0 (leaf 2)
      else
        «Authoring.noResults»)
      x1;
    x2

def «Authoring.declaredNames» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1;
            let x3 : T := Const.lcase
              (α := T)
              (β := T)
              x2
              (leaf 0)
              (fun (x3 : T) (_ : List T) => x3);
            let x4 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x2
              ([] : List T)
              (fun (_ : T) (x5 : List T) => x5);
            let _ : List T := x4; Const.children x3);
    x1

def «Authoring.declaredGlobals» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   let x3 : List T := Const.children x2;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x3
                     (leaf 0)
                     (fun (x4 : T) (_ : List T) => x4);
                   let x5 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x3
                     ([] : List T)
                     (fun (_ : T) (x6 : List T) => x6);
                   let x6 : List T := x5;
                   let x7 : T := «Derivation.checkDev» x0 ([] : List T) x6;
                   if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x7; x0
                   else
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := x9;
                     let x12 : List T := Const.children x11;
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let x14 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x14
                       (leaf 0)
                       (fun (x15 : T) (_ : List T) => x15);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x14
                       ([] : List T)
                       (fun (_ : T) (x17 : List T) => x17);
                     x13);
    x2

def «Authoring.certified» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x1;
                   let x4 : List T := Const.children x3;
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : List T := x6;
                   if («Base.isEmpty» (Const.children x5)).label ≠ 0 then
                     x2
                   else
                     let x8 : T := x2;
                     let x9 : List T := Const.children x8;
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let x11 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : List T := x11;
                     let x13 : T := «Authoring.entryBase» x0;
                     «Authoring.results»
                       (Const.node
                         (leaf 0)
                         («Prelude.append»
                           («Base.take» x13 (Const.children x10))
                           («Prelude.append»
                             (Const.children x5)
                             («Prelude.drop» x13 (Const.children x10)))))
                       («Authoring/Decls.append»
                         («Authoring/EachDecl.take» x13 x12)
                         («Authoring/Decls.append» x7 («Authoring/Decls.drop» x13 x12))));
    x3

def «Authoring.withItem» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node
      (leaf 0)
      («Prelude.append» (Const.children x0) («Prelude.single» x1));
    x2

def «Authoring.sameRequest» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.equal
      (Const.child x0 (leaf 0))
      («Authoring.requestName» x1)).label ≠ 0 then
      «Prelude.and»
        (Const.equal (Const.child x0 (leaf 1)) («Authoring.requestThm» x1))
        («Prelude.and»
          (Const.equal (Const.child x0 (leaf 2)) («Authoring.requestScript» x1))
          («Prelude.and»
            (Const.equal (Const.child x0 (leaf 3)) («Authoring.requestSpec» x1))
            (Const.eq (Const.child x0 (leaf 4)) («Authoring.requestVersion» x1))))
    else
      leaf 0);
    x2

def «Authoring.itemProved» :=
  fun (x0 : T) =>
    let x1 : T := Const.eq (Const.child x0 (leaf 6)) (leaf 1); x1

def «Authoring.findItem» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if («Prelude.and»
          («Authoring.sameRequest» x2 x1)
          («Authoring.itemProved» x2)).label ≠ 0 then
          «Prelude.some» x2
        else
          x3)
      «Prelude.none»
      x0;
    x2

def «Authoring.keptAligned» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Prelude.and»
      x0
      («Prelude.and»
        (Const.equal (Const.child x1 (leaf 0)) («Authoring.requestName» x2))
        («Prelude.and»
          (Const.equal (Const.child x1 (leaf 1)) («Authoring.requestThm» x2))
          (Const.equal (Const.child x1 (leaf 5)) x3)));
    x4

def «Authoring.recite» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.child x2 (leaf 0);
        Const.node
          (Const.label x2)
          ((if («Prelude.or»
            (Const.eq (Const.label x2) (leaf 16))
            (Const.eq (Const.label x2) (leaf 27))).label ≠ 0 then
            Const.node
              (leaf 0)
              ((x0 (Const.child x4 (leaf 0))) ::
                («Prelude.tail» (Const.children x4)))
          else
            x4) ::
            («Prelude.tail» x3)))
      x1;
    x2

def «Authoring.entryMap» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Authoring.entryBase» x0;
                   if («Prelude.or»
                     (Const.eq x0 (leaf 0))
                     (Const.lt x3 x4)).label ≠ 0 then
                     x3
                   else
                     let x5 : T := «Reader.indexOf»
                       («Prelude.at» x1 (Const.div (Const.sub x3 x4) (leaf 2)))
                       x2;
                     if («Prelude.isSome» x5).label ≠ 0 then
                       Const.add
                         x4
                         (Const.add
                           (Const.mul (leaf 2) («Prelude.get» x5))
                           (Const.mod (Const.sub x3 x4) (leaf 2)))
                     else
                       x3);
    x4

def «Authoring.placesOf» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := (let x2 : T := Const.add
                     («Prelude.length» x1)
                     («Authoring/LD.length» («Logic.connectives» (leaf 0)));
                   Const.node
                     (leaf 0)
                     («Base.mapT»
                       (fun (x3 : T) => «Base.getD» («Reader.indexOf» x3 x1) x2)
                       x0));
    x2

def «Authoring.placeOf» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := (if (Const.lt x3 x0).label ≠ 0 then
      x3
    else
      let x4 : T := Const.sub x3 x0;
      if (Const.lt x4 (Const.arity x1)).label ≠ 0 then
        Const.add x0 (Const.child x1 x4)
      else
        Const.add (Const.add x0 x2) (Const.sub x4 (Const.arity x1)));
    x4

def «Authoring.transportTerm» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.child x2 (leaf 0);
        Const.node
          (Const.label x2)
          ((if (Const.eq (Const.label x2) (leaf 11)).label ≠ 0 then
            Const.node
              (leaf 0)
              ((x0 (Const.child x4 (leaf 0))) ::
                («Prelude.tail» (Const.children x4)))
          else
            x4) ::
            («Prelude.tail» x3)))
      x1;
    x2

def «Authoring.datumAt» :=
  fun (x0 : T → T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := «Prelude.append»
      («Base.take» x1 x2)
      ((x0 («Prelude.at» x2 x1)) ::
        («Prelude.drop» (Const.add x1 (leaf 1)) x2));
    x3

def «Authoring.transportData» :=
  fun (x0 : T → T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := (if («Prelude.or»
      (Const.eq x1 (leaf 16))
      (Const.eq x1 (leaf 27))).label ≠ 0 then
      «Authoring.datumAt»
        (fun (x3 : T) =>
          Const.node
            (leaf 0)
            («Base.mapT» («Authoring.transportTerm» x0) (Const.children x3)))
        (leaf 2)
        x2
    else
      if («Prelude.or»
        (Const.eq x1 (leaf 19))
        (Const.eq x1 (leaf 20))).label ≠ 0 then
        «Authoring.datumAt» («Authoring.transportTerm» x0) (leaf 2) x2
      else
        if (Const.eq x1 (leaf 32)).label ≠ 0 then
          «Authoring.datumAt» («Authoring.transportTerm» x0) (leaf 3) x2
        else
          if («Prelude.or»
            (Const.eq x1 (leaf 22))
            (Const.eq x1 (leaf 24))).label ≠ 0 then
            «Authoring.datumAt» («Authoring.transportTerm» x0) (leaf 0) x2
          else
            x2);
    x3

def «Authoring.transportDeriv» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.arity x1) (leaf 0)).label ≠ 0 then
      x1
    else
      Const.para
        (α := T)
        (fun (x2 : T) (x3 : List T) =>
          Const.node
            (Const.label x2)
            ((Const.node
              (leaf 0)
              («Authoring.transportData»
                x0
                (Const.label x2)
                (Const.children (Const.child x2 (leaf 0))))) ::
              («Prelude.tail» x3)))
        x1);
    x2

def «Authoring.transportThm» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := Const.node
      (Const.label x1)
      («Theory.l4»
        (Const.child x1 (leaf 0))
        (Const.child x1 (leaf 1))
        (Const.node
          (leaf 0)
          («Base.mapT»
            («Authoring.transportTerm» x0)
            (Const.children (Const.child x1 (leaf 2)))))
        («Authoring.transportTerm» x0 (Const.child x1 (leaf 3))));
    x2

def «Authoring.transportDefinition» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := Const.node
      (Const.label x1)
      («Theory.l4»
        (Const.child x1 (leaf 0))
        (Const.child x1 (leaf 1))
        (Const.child x1 (leaf 2))
        («Authoring.transportTerm» x0 (Const.child x1 (leaf 3))));
    x2

def «Authoring.transportItem» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : List T := Const.children x1;
                   Const.node
                     (leaf 0)
                     ((«Prelude.at» x2 (leaf 0)) ::
                       ((«Authoring.transportThm» x0 («Prelude.at» x2 (leaf 1))) ::
                         ((«Prelude.at» x2 (leaf 2)) ::
                           ((«Prelude.at» x2 (leaf 3)) ::
                             ((«Prelude.at» x2 (leaf 4)) ::
                               ((Const.node
                                 (leaf 0)
                                 («Base.mapT»
                                   («Authoring.transportTerm» x0)
                                   (Const.children («Prelude.at» x2 (leaf 5))))) ::
                                 («Theory.l3»
                                   («Prelude.at» x2 (leaf 6))
                                   («Authoring.transportDeriv» x0 («Prelude.at» x2 (leaf 7)))
                                   («Authoring.transportDeriv»
                                     x0
                                     («Prelude.at» x2 (leaf 8)))))))))));
    x2

def «Authoring.itemsFor» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : List T) (x4 : T) =>
    let x5 : List
      T := (let x5 : List T := «Authoring.cacheItems» x0 x1;
            if (x4).label ≠ 0 then
              x5
            else
              let x6 : T := «Authoring.placesOf» x2 x3;
              «Base.mapT»
                («Authoring.transportItem»
                  («Authoring.placeOf»
                    («Authoring/LD.length» «Translation.lib»)
                    x6
                    («Prelude.length» x3)))
                x5);
    x5

def «Authoring.begin» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : List T := «Authoring.rulesFor» x1 x2 (leaf 0);
                   let x5 : T := «Derivation.checkDev» x0 ([] : List T) x4;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x5;
                     «Authoring.stuck»
                       (leaf 6)
                       «Authoring.unnamed»
                       «Authoring.noNode»
                       «Authoring.noNode»
                       «Authoring.noNode»
                   else
                     let x6 : List T := Const.children x5;
                     let x7 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     let x9 : T := x7;
                     let x10 : List T := Const.children x9;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     «Authoring.proving»
                       («Authoring.results»
                         (Const.node
                           (leaf 0)
                           («Base.mapT»
                             (fun (_ : T) => «Authoring.unnamed»)
                             («Base.range» («Authoring/Decls.length» x4))))
                         x4)
                       x13
                       «Authoring.noNode»
                       x3
                       «Authoring.noNode»
                       «Authoring.noNode»);
    x4

def «Authoring.accompany» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : List T)
    (x6 : T)
    (x7 : List T)
    (x8 : T)
    (x9 : T)
    (x10 : T)
    (x11 : T)
    (x12 : T)
    (x13 : T)
    (x14 : T)
    (x15 : T) =>
    let x16 : T := (let x16 : T := x9;
                    let x17 : List T := Const.children x16;
                    let x18 : List T := x17;
                    let x19 : T := Const.lt x11 (leaf 3);
                    let x20 : List
                      T := «Authoring/Decls.append»
                      x7
                      («Authoring/Decls.single»
                        («Derivation.declLang» («Authoring.requestThm» x4) x8));
                    let x21 : T := «Authoring.withItem» x15 x11;
                    if (Const.eq x3 (leaf 0)).label ≠ 0 then
                      «Authoring.proving»
                        («Authoring.results»
                          (Const.node
                            (leaf 0)
                            («Prelude.append»
                              (Const.children x6)
                              («Prelude.single» («Authoring.requestName» x4))))
                          x20)
                        x9
                        x10
                        («Authoring.keptAligned» x13 x12 x4 (leaf 0))
                        («Authoring.withItem»
                          x14
                          («Authoring.cacheItem»
                            x4
                            (leaf 0)
                            x19
                            (if (x19).label ≠ 0 then x8 else «Prelude.none»)
                            «Prelude.none»))
                        x21
                    else
                      let x22 : T := «Authoring.companion»
                        x0
                        x18
                        («Authoring.rulesIn»
                          x18
                          («Authoring.normalRules» («Authoring.entryBase» x3) x2 x5 x4)
                          x1)
                        («Authoring.connectivesAt» x2)
                        («Authoring.normalDepth» x4)
                        («Authoring/Decls.length» x7)
                        («Authoring.requestThm» x4);
                      if («Prelude.isSome» x22).label ≠ 0 then
                        let x23 : List T := Const.children («Prelude.get» x22);
                        let x24 : T := Const.node
                          (leaf 0)
                          («Theory.l2» («Prelude.at» x23 (leaf 0)) («Prelude.at» x23 (leaf 1)));
                        let x25 : T := «Derivation.declLang»
                          («Authoring.withSides»
                            («Authoring.requestThm» x4)
                            («Prelude.at» x23 (leaf 0))
                            («Prelude.at» x23 (leaf 1)))
                          («Prelude.at» x23 (leaf 2));
                        let x26 : T := «Authoring.admit» x0 x18 x25;
                        if (Const.eq (Const.label x26) (leaf 0)).label ≠ 0 then
                          let _ : List T := Const.children x26;
                          «Authoring.stuck» (leaf 6) («Authoring.requestName» x4) x10 x14 x15
                        else
                          let x27 : List T := Const.children x26;
                          let x28 : T := Const.lcase
                            (α := T)
                            (β := T)
                            x27
                            (leaf 0)
                            (fun (x28 : T) (_ : List T) => x28);
                          let _ : List
                            T := Const.lcase
                            (α := T)
                            (β := List T)
                            x27
                            ([] : List T)
                            (fun (_ : T) (x30 : List T) => x30);
                          «Authoring.proving»
                            («Authoring.results»
                              (Const.node
                                (leaf 0)
                                («Prelude.append»
                                  (Const.children x6)
                                  («Theory.l2»
                                    («Authoring.requestName» x4)
                                    («Authoring.requestName» x4))))
                              («Authoring/Decls.append» x20 («Authoring/Decls.single» x25)))
                            x28
                            x10
                            («Authoring.keptAligned» x13 x12 x4 x24)
                            («Authoring.withItem»
                              x14
                              («Authoring.cacheItem»
                                x4
                                x24
                                x19
                                (if (x19).label ≠ 0 then x8 else «Prelude.none»)
                                (if (x19).label ≠ 0 then
                                  «Prelude.at» x23 (leaf 2)
                                else
                                  «Prelude.none»)))
                            x21
                      else
                        «Authoring.stuck» (leaf 5) («Authoring.requestName» x4) x10 x14 x15);
    x16

def «Authoring.taken» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := (let x9 : List
                     T := «Authoring/Decls.append»
                     x3
                     («Authoring/Decls.single»
                       («Derivation.declLang»
                         («Authoring.requestThm» x1)
                         (Const.child x6 (leaf 7))));
                   let x10 : List
                     T := «Derivation.push»
                     x4
                     («Derivation.entLang» («Authoring.requestThm» x1));
                   if (Const.eq x0 (leaf 0)).label ≠ 0 then
                     «Authoring.proving»
                       («Authoring.results»
                         (Const.node
                           (leaf 0)
                           («Prelude.append»
                             (Const.children x2)
                             («Prelude.single» («Authoring.requestName» x1))))
                         x9)
                       («Derivation.entries» x10)
                       x5
                       (leaf 1)
                       («Authoring.withItem» x7 x6)
                       («Authoring.withItem» x8 (leaf 2))
                   else
                     let x11 : T := «Authoring.withSides»
                       («Authoring.requestThm» x1)
                       (Const.child (Const.child x6 (leaf 5)) (leaf 0))
                       (Const.child (Const.child x6 (leaf 5)) (leaf 1));
                     «Authoring.proving»
                       («Authoring.results»
                         (Const.node
                           (leaf 0)
                           («Prelude.append»
                             (Const.children x2)
                             («Theory.l2»
                               («Authoring.requestName» x1)
                               («Authoring.requestName» x1))))
                         («Authoring/Decls.append»
                           x9
                           («Authoring/Decls.single»
                             («Derivation.declLang» x11 (Const.child x6 (leaf 8))))))
                       («Derivation.entries»
                         («Derivation.push» x10 («Derivation.entLang» x11)))
                       x5
                       (leaf 1)
                       («Authoring.withItem» x7 x6)
                       («Authoring.withItem» x8 (leaf 2)));
    x9

def «Authoring.search» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : T)
    (x7 : List T)
    (x8 : T)
    (x9 : List T)
    (x10 : List T)
    (x11 : T)
    (x12 : T)
    (x13 : T)
    (x14 : T)
    (x15 : T) =>
    let x16 : T := (let x16 : T := «Authoring.derive»
                      (leaf 0)
                      x0
                      x10
                      x1
                      («Authoring.entryBase» x5)
                      x2
                      x3
                      x7
                      x6;
                    let x17 : List
                      T := (if («Prelude.and»
                      («Prelude.isSome» x16)
                      («Authoring.holed» («Authoring.requestScript» x6))).label ≠ 0 then
                      «Authoring.obligationsOf» («Prelude.get» x16)
                    else
                      ([] : List T));
                    if («Prelude.and»
                      («Prelude.isSome» x16)
                      («Base.isEmpty» x17)).label ≠ 0 then
                      let x18 : T := «Authoring.admit»
                        x0
                        x10
                        («Derivation.declLang»
                          («Authoring.requestThm» x6)
                          («Prelude.get» x16));
                      if (Const.eq (Const.label x18) (leaf 0)).label ≠ 0 then
                        let _ : List T := Const.children x18;
                        «Authoring.stuck» (leaf 6) («Authoring.requestName» x6) x11 x14 x15
                      else
                        let x19 : List T := Const.children x18;
                        let x20 : T := Const.lcase
                          (α := T)
                          (β := T)
                          x19
                          (leaf 0)
                          (fun (x20 : T) (_ : List T) => x20);
                        let _ : List
                          T := Const.lcase
                          (α := T)
                          (β := List T)
                          x19
                          ([] : List T)
                          (fun (_ : T) (x22 : List T) => x22);
                        «Authoring.accompany»
                          x0
                          x1
                          x3
                          x5
                          x6
                          x7
                          x8
                          x9
                          («Prelude.get» x16)
                          x20
                          x11
                          (leaf 0)
                          x12
                          x13
                          x14
                          x15
                    else
                      «Authoring.accompany»
                        x0
                        x1
                        x3
                        x5
                        x6
                        x7
                        x8
                        x9
                        «Prelude.none»
                        («Derivation.entries»
                          («Derivation.push»
                            x10
                            («Derivation.entLang» («Authoring.requestThm» x6))))
                        (Const.node
                          (leaf 0)
                          («Prelude.append»
                            (Const.children x11)
                            («Prelude.single»
                              («Authoring.failed»
                                (if («Prelude.isSome» x16).label ≠ 0 then leaf 7 else leaf 4)
                                («Authoring.requestName» x6)
                                («Base.mapT»
                                  («Authoring.reportOf»
                                    («Authoring.requestVersion» x6)
                                    x0
                                    x10
                                    x3
                                    x4
                                    («Authoring.requestObjects» x6))
                                  (if («Prelude.isSome» x16).label ≠ 0 then
                                    x17
                                  else
                                    «Authoring.obligationsOf»
                                      («Base.getD»
                                        («Authoring.derive»
                                          (leaf 1)
                                          x0
                                          x10
                                          x1
                                          («Authoring.entryBase» x5)
                                          x2
                                          x3
                                          x7
                                          x6)
                                        «Prelude.none»)))))))
                        (leaf 3)
                        x12
                        x13
                        x14
                        x15);
    x16

def «Authoring.advance» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := (let x9 : T := x8;
                   if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
                     let x10 : List T := Const.children x9;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let x14 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x14
                       (leaf 0)
                       (fun (x15 : T) (_ : List T) => x15);
                     let x16 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x14
                       ([] : List T)
                       (fun (_ : T) (x17 : List T) => x17);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x16
                       (leaf 0)
                       (fun (x17 : T) (_ : List T) => x17);
                     let x18 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x16
                       ([] : List T)
                       (fun (_ : T) (x19 : List T) => x19);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x18
                       (leaf 0)
                       (fun (x19 : T) (_ : List T) => x19);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x18
                       ([] : List T)
                       (fun (_ : T) (x21 : List T) => x21);
                     x8
                   else
                     let x10 : List T := Const.children x9;
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let x14 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let x15 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x14
                       (leaf 0)
                       (fun (x15 : T) (_ : List T) => x15);
                     let x16 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x14
                       ([] : List T)
                       (fun (_ : T) (x17 : List T) => x17);
                     let x17 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x16
                       (leaf 0)
                       (fun (x17 : T) (_ : List T) => x17);
                     let x18 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x16
                       ([] : List T)
                       (fun (_ : T) (x19 : List T) => x19);
                     let x19 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x18
                       (leaf 0)
                       (fun (x19 : T) (_ : List T) => x19);
                     let x20 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x18
                       ([] : List T)
                       (fun (_ : T) (x21 : List T) => x21);
                     let x21 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x20
                       (leaf 0)
                       (fun (x21 : T) (_ : List T) => x21);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x20
                       ([] : List T)
                       (fun (_ : T) (x23 : List T) => x23);
                     let x23 : T := x11;
                     let x24 : List T := Const.children x23;
                     let x25 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x24
                       (leaf 0)
                       (fun (x25 : T) (_ : List T) => x25);
                     let x26 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x24
                       ([] : List T)
                       (fun (_ : T) (x27 : List T) => x27);
                     let x27 : List T := x26;
                     let x28 : T := x13;
                     let x29 : List T := Const.children x28;
                     let x30 : List T := x29;
                     let x31 : List T := «Authoring.sourceNames» x5 (Const.children x25);
                     let x32 : T := «Prelude.at» x6 («Prelude.length» x31);
                     if («Prelude.and»
                       x17
                       («Prelude.and»
                         («Authoring.sameRequest» x32 x7)
                         («Authoring.itemProved» x32))).label ≠ 0 then
                       «Authoring.taken» x5 x7 x25 x27 x30 x15 x32 x19 x21
                     else
                       let x33 : T := «Authoring.findItem» x6 x7;
                       let x34 : T := (if («Prelude.isSome» x33).label ≠ 0 then
                         «Authoring.recite»
                           («Authoring.entryMap»
                             x5
                             («Base.mapT» (fun (x34 : T) => Const.child x34 (leaf 0)) x6)
                             x31)
                           (Const.child («Prelude.get» x33) (leaf 7))
                       else
                         «Prelude.none»);
                       let x35 : T := (if («Prelude.isSome» x33).label ≠ 0 then
                         «Authoring.admit»
                           x0
                           x30
                           («Derivation.declLang» («Authoring.requestThm» x7) x34)
                       else
                         «Authoring/OEntries.nothing»);
                       if (Const.eq (Const.label x35) (leaf 1)).label ≠ 0 then
                         let x36 : List T := Const.children x35;
                         let x37 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x36
                           (leaf 0)
                           (fun (x37 : T) (_ : List T) => x37);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x36
                           ([] : List T)
                           (fun (_ : T) (x39 : List T) => x39);
                         «Authoring.accompany»
                           x0
                           x1
                           x3
                           x5
                           x7
                           x31
                           x25
                           x27
                           x34
                           x37
                           x15
                           (leaf 1)
                           x32
                           x17
                           x19
                           x21
                       else
                         let _ : List T := Const.children x35;
                         «Authoring.search»
                           x0
                           x1
                           x2
                           x3
                           x4
                           x5
                           x7
                           x31
                           x25
                           x27
                           x30
                           x15
                           x32
                           x17
                           x19
                           x21);
    x9

def «Authoring.resumeWith» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := «Authoring.readSources» x0 x1 x2 x3;
                   if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let x10 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     Const.node
                       (leaf 0)
                       («Theory.l3» («Authoring.failure» x9 x11) x4 «Authoring.noNode»)
                   else
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := x9;
                     let x12 : List T := Const.children x11;
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let x14 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let x15 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x14
                       (leaf 0)
                       (fun (x15 : T) (_ : List T) => x15);
                     let x16 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x14
                       ([] : List T)
                       (fun (_ : T) (x17 : List T) => x17);
                     let x17 : List T := x16;
                     let x18 : T := «Authoring.declaredGlobals»
                       («Authoring.globalsFor» x13 x2)
                       x15;
                     let x19 : T := Const.add
                       («Authoring/LD.length» «Translation.lib»)
                       («Authoring/LD.length» x2);
                     let x20 : List T := «Authoring.rulesOf» x13 x19;
                     let x21 : List T := «Authoring.itemsFor» x13 x4 x5 x1 x6;
                     let x22 : List T := «Authoring.declaredNames» x15;
                     let x23 : T := Const.foldr
                       (α := T)
                       (β := T → T)
                       (fun (x23 : T) (x24 : T → T) (x25 : T) =>
                         x24 («Authoring.advance» x18 x20 x0 x1 x22 x13 x21 x23 x25))
                       (fun (x23 : T) => x23)
                       x17
                       («Authoring.begin»
                         x18
                         x13
                         x19
                         («Prelude.and» x6 («Authoring.sameDeclared» x4 x15)));
                     if (Const.eq (Const.label x23) (leaf 1)).label ≠ 0 then
                       let x24 : List T := Const.children x23;
                       let x25 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x24
                         (leaf 0)
                         (fun (x25 : T) (_ : List T) => x25);
                       let x26 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x24
                         ([] : List T)
                         (fun (_ : T) (x27 : List T) => x27);
                       let x27 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x26
                         (leaf 0)
                         (fun (x27 : T) (_ : List T) => x27);
                       let x28 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x26
                         ([] : List T)
                         (fun (_ : T) (x29 : List T) => x29);
                       let x29 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x28
                         (leaf 0)
                         (fun (x29 : T) (_ : List T) => x29);
                       let x30 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x28
                         ([] : List T)
                         (fun (_ : T) (x31 : List T) => x31);
                       let x31 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x30
                         (leaf 0)
                         (fun (x31 : T) (_ : List T) => x31);
                       let x32 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x30
                         ([] : List T)
                         (fun (_ : T) (x33 : List T) => x33);
                       let x33 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x32
                         (leaf 0)
                         (fun (x33 : T) (_ : List T) => x33);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x32
                         ([] : List T)
                         (fun (_ : T) (x35 : List T) => x35);
                       Const.node
                         (leaf 0)
                         («Theory.l3»
                           (Const.node
                             (leaf 2)
                             («Prelude.append»
                               (Const.children x29)
                               («Prelude.single» («Authoring.failed» x25 x27 ([] : List T)))))
                           (Const.node (leaf 0) («Theory.l3» x13 x31 x15))
                           x33)
                     else
                       let x24 : List T := Const.children x23;
                       let x25 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x24
                         (leaf 0)
                         (fun (x25 : T) (_ : List T) => x25);
                       let x26 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x24
                         ([] : List T)
                         (fun (_ : T) (x27 : List T) => x27);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x26
                         (leaf 0)
                         (fun (x27 : T) (_ : List T) => x27);
                       let x28 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x26
                         ([] : List T)
                         (fun (_ : T) (x29 : List T) => x29);
                       let x29 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x28
                         (leaf 0)
                         (fun (x29 : T) (_ : List T) => x29);
                       let x30 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x28
                         ([] : List T)
                         (fun (_ : T) (x31 : List T) => x31);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x30
                         (leaf 0)
                         (fun (x31 : T) (_ : List T) => x31);
                       let x32 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x30
                         ([] : List T)
                         (fun (_ : T) (x33 : List T) => x33);
                       let x33 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x32
                         (leaf 0)
                         (fun (x33 : T) (_ : List T) => x33);
                       let x34 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x32
                         ([] : List T)
                         (fun (_ : T) (x35 : List T) => x35);
                       let x35 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x34
                         (leaf 0)
                         (fun (x35 : T) (_ : List T) => x35);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x34
                         ([] : List T)
                         (fun (_ : T) (x37 : List T) => x37);
                       Const.node
                         (leaf 0)
                         («Theory.l3»
                           (if («Base.isEmpty» (Const.children x29)).label ≠ 0 then
                             «Prelude.some» («Authoring.certified» x13 x15 x25)
                           else
                             Const.node (leaf 2) (Const.children x29))
                           (Const.node (leaf 0) («Theory.l3» x13 x33 x15))
                           x35));
    x7

def «Authoring.resume» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x4;
                     Const.node (leaf 0) («Theory.l3» «Prelude.none» x2 «Authoring.noNode»)
                   else
                     let x5 : List T := Const.children x4;
                     let x6 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     let x8 : T := x6;
                     let x9 : List T := Const.children x8;
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let x11 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x11
                       (leaf 0)
                       (fun (x12 : T) (_ : List T) => x12);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x11
                       ([] : List T)
                       (fun (_ : T) (x14 : List T) => x14);
                     let x14 : T := x10;
                     let x15 : List T := Const.children x14;
                     let x16 : List T := x15;
                     let x17 : T := x12;
                     let x18 : List T := Const.children x17;
                     let x19 : List T := x18;
                     «Authoring.resumeWith»
                       x16
                       (Const.children (Const.child x0 (leaf 1)))
                       x19
                       (Const.children x1)
                       x2
                       (Const.children (Const.child x3 (leaf 1)))
                       (Const.equal x3 x0));
    x4

def «Authoring.prove» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.child
      («Authoring.resume» x0 x1 «Prelude.none» «Prelude.none»)
      (leaf 0);
    x2

def «Authoring.transport» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : List T := Const.children (Const.child x0 (leaf 1));
                   let x4 : T := «Authoring.placesOf»
                     (Const.children (Const.child x1 (leaf 1)))
                     x3;
                   let x5 : T →
                     T := «Authoring.placeOf»
                     («Authoring/LD.length» «Translation.lib»)
                     x4
                     («Prelude.length» x3);
                   Const.node
                     (Const.label x2)
                     ((Const.child x2 (leaf 0)) ::
                       («Base.mapT»
                         (fun (x6 : T) =>
                           if («Prelude.and»
                             (Const.eq (Const.label x6) (leaf 0))
                             (Const.eq (Const.arity x6) (leaf 2))).label ≠ 0 then
                             Const.node
                               (leaf 0)
                               («Theory.l2»
                                 («Authoring.transportThm» x5 (Const.child x6 (leaf 0)))
                                 («Authoring.transportDeriv» x5 (Const.child x6 (leaf 1))))
                           else
                             if («Prelude.and»
                               (Const.eq (Const.label x6) (leaf 2))
                               (Const.eq (Const.arity x6) (leaf 1))).label ≠ 0 then
                               Const.node
                                 (leaf 2)
                                 («Prelude.single»
                                   («Authoring.transportDefinition» x5 (Const.child x6 (leaf 0))))
                             else
                               x6)
                         («Prelude.tail» (Const.children x2)))));
    x3

def «Authoring.stated» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let x3 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let x4 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x4
                       (leaf 0)
                       (fun (x5 : T) (_ : List T) => x5);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x4
                       ([] : List T)
                       (fun (_ : T) (x7 : List T) => x7);
                     «Prelude.some» x3
                   else
                     «Prelude.none»);
    x1

def «Authoring.matches» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prelude.and»
      (Const.eq
        (Const.mul
          (if (Const.eq x0 (leaf 0)).label ≠ 0 then leaf 1 else leaf 2)
          («Authoring/Requests.length» x1))
        («Authoring/Decls.length» x2))
      («Prelude.and»
        (Const.eq («Authoring/Decls.length» x2) («Prelude.length» x3))
        (Const.foldr
          (α := T)
          (β := List T → List T → T)
          (fun (x4 : T) (x5 : List T → List T → T) (x6 : List T) (x7 : List T) =>
            Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x8 : T) (x9 : List T) =>
                «Prelude.and»
                  (Const.equal
                    («Authoring.stated» x8)
                    («Prelude.some» («Authoring.requestThm» x4)))
                  («Prelude.and»
                    (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 0)))
                    (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                      x5 x9 («Prelude.drop» (leaf 1) x7)
                    else
                      Const.lcase
                        (α := T)
                        (β := T)
                        x9
                        (leaf 0)
                        (fun (x10 : T) (x11 : List T) =>
                          «Prelude.and»
                            («Prelude.isSome» («Authoring.stated» x10))
                            («Prelude.and»
                              (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 1)))
                              (x5 x11 («Prelude.drop» (leaf 2) x7))))))))
          (fun (_ : List T) (_ : List T) => leaf 1)
          x1
          x2
          x3));
    x4

def «Authoring.replayWith» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := (let x5 : T := «Authoring.readSources» x0 x1 x2 x3;
                   if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                     let x6 : List T := Const.children x5;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let x8 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     leaf 0
                   else
                     let x6 : List T := Const.children x5;
                     let x7 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     let x9 : T := x7;
                     let x10 : List T := Const.children x9;
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let x14 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let x15 : List T := x14;
                     let x16 : T := x4;
                     if («Authoring.Results.member» x16).label ≠ 0 then
                       let x17 : T := x16;
                       let x18 : T := x17;
                       let x19 : List T := Const.children x18;
                       let x20 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x19
                         (leaf 0)
                         (fun (x20 : T) (_ : List T) => x20);
                       let x21 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x19
                         ([] : List T)
                         (fun (_ : T) (x22 : List T) => x22);
                       let x22 : List T := x21;
                       let x23 : T := «Authoring.entryBase» x11;
                       let x24 : List T := «Authoring.declaredNames» x13;
                       let x25 : T := «Prelude.length» x24;
                       if («Prelude.and»
                         («Base.equalTs»
                           («Base.take» x25 («Prelude.drop» x23 (Const.children x20)))
                           x24)
                         («Prelude.and»
                           («Base.equalTs»
                             («Base.take»
                               x25
                               («Prelude.drop» (Const.add x23 (leaf 1)) (Const.children x4)))
                             («Prelude.tail» (Const.children x13)))
                           («Authoring.matches»
                             x11
                             x15
                             («Authoring/Decls.drop» (Const.add x23 x25) x22)
                             («Prelude.drop»
                               (Const.add x23 x25)
                               (Const.children x20))))).label ≠ 0 then
                         let x26 : T := «Derivation.checkDev»
                           («Authoring.globalsFor» x11 x2)
                           ([] : List T)
                           x22;
                         if (Const.eq (Const.label x26) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x26; leaf 0
                         else
                           let x27 : List T := Const.children x26;
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x27
                             (leaf 0)
                             (fun (x28 : T) (_ : List T) => x28);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x27
                             ([] : List T)
                             (fun (_ : T) (x30 : List T) => x30);
                           leaf 1
                       else
                         leaf 0
                     else
                       leaf 0);
    x5

def «Authoring.replay» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; leaf 0
                   else
                     let x4 : List T := Const.children x3;
                     let x5 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x4
                       (leaf 0)
                       (fun (x5 : T) (_ : List T) => x5);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x4
                       ([] : List T)
                       (fun (_ : T) (x7 : List T) => x7);
                     let x7 : T := x5;
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let x10 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := x9;
                     let x14 : List T := Const.children x13;
                     let x15 : List T := x14;
                     let x16 : T := x11;
                     let x17 : List T := Const.children x16;
                     let x18 : List T := x17;
                     «Authoring.replayWith»
                       x15
                       (Const.children (Const.child x0 (leaf 1)))
                       x18
                       (Const.children x1)
                       x2);
    x3

def «Authoring.version» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x2; «Prelude.none»
                   else
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let x6 : T := x4;
                     let x7 : List T := Const.children x6;
                     let x8 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x7
                       (leaf 0)
                       (fun (x8 : T) (_ : List T) => x8);
                     let x9 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x7
                       ([] : List T)
                       (fun (_ : T) (x10 : List T) => x10);
                     let x10 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x9
                       (leaf 0)
                       (fun (x10 : T) (_ : List T) => x10);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := x8;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     let x15 : T := x10;
                     let x16 : List T := Const.children x15;
                     let x17 : List T := x16;
                     let x18 : T := «Authoring.readSources»
                       x14
                       (Const.children (Const.child x0 (leaf 1)))
                       x17
                       (Const.children x1);
                     if (Const.eq (Const.label x18) (leaf 1)).label ≠ 0 then
                       let x19 : List T := Const.children x18;
                       let x20 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x19
                         (leaf 0)
                         (fun (x20 : T) (_ : List T) => x20);
                       let x21 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x19
                         ([] : List T)
                         (fun (_ : T) (x22 : List T) => x22);
                       let x22 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x21
                         (leaf 0)
                         (fun (x22 : T) (_ : List T) => x22);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x21
                         ([] : List T)
                         (fun (_ : T) (x24 : List T) => x24);
                       «Authoring.failure» x20 x22
                     else
                       let x19 : List T := Const.children x18;
                       let x20 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x19
                         (leaf 0)
                         (fun (x20 : T) (_ : List T) => x20);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x19
                         ([] : List T)
                         (fun (_ : T) (x22 : List T) => x22);
                       let x22 : T := x20;
                       let x23 : List T := Const.children x22;
                       let x24 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x23
                         (leaf 0)
                         (fun (x24 : T) (_ : List T) => x24);
                       let x25 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x23
                         ([] : List T)
                         (fun (_ : T) (x26 : List T) => x26);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x25
                         (leaf 0)
                         (fun (x26 : T) (_ : List T) => x26);
                       let x27 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x25
                         ([] : List T)
                         (fun (_ : T) (x28 : List T) => x28);
                       let _ : List T := x27; «Prelude.some» x24);
    x2

end GebMirror.Metalogic

end
