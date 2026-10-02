module

public import GebMirror.Metalogic.Prover

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «ttL» :=
  fun (x0 : T) =>
    let x1 : T := «mDefn» x0 ([] : List T) ([] : List T); x1

def «impL» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mDefn»
      (Const.add x0 (leaf 2))
      ([] : List T)
      («l2» x2 x1);
    x3

def «trueI» :=
  «dNode»
    (leaf 23)
    ([] : List T)
    («l2»
      («dNode» (leaf 8) ([] : List T) ([] : List T))
      («dNode»
        (leaf 18)
        ([] : List T)
        («l2»
          («dNode» (leaf 0) ([] : List T) ([] : List T))
          («dNode» (leaf 0) ([] : List T) ([] : List T)))))

def «impI» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «dNode»
      (leaf 23)
      ([] : List T)
      («l2»
        («dNode» (leaf 8) ([] : List T) ([] : List T))
        («dNode»
          (leaf 25)
          ([] : List T)
          («l2»
            («dNode»
              (leaf 27)
              («l3»
                (Const.add x0 (leaf 2))
                (Const.node (leaf 0) ([] : List T))
                (Const.node (leaf 0) («l2» x3 x2)))
              («single» («dNode» (leaf 21) («single» x1) ([] : List T))))
            («dNode»
              (leaf 27)
              («l3»
                (Const.add x0 (leaf 1))
                (Const.node (leaf 0) ([] : List T))
                (Const.node (leaf 0) («l2» x3 x2)))
              («l2» («dNode» (leaf 21) («single» x1) ([] : List T)) x4)))));
    x5

def «mApps» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T → T)
      (fun (x2 : T) (x3 : T → T) (x4 : T) => x3 («mApp» x4 x2))
      (fun (x2 : T) => x2)
      x1
      x0;
    x2

def «byMode» :=
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
      «joinBy» («eval» x1 x2 x3 x4 (leaf 4096) x0) x5 x6 x7 x8);
    x5

def «byWeak» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T))) =>
    let x4 : List T → List T → T → T → T := «byMode» (leaf 1) x0 x1 x2 x3;
    x4

def «byNF» :=
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
      «bindO»
        («eval» x0 x1 x2 x3 (leaf 4096) x4 x6 x7 x8)
        (fun (x10 : T) =>
          «bindO»
            («eval» x0 x1 x2 x3 (leaf 4096) x4 x6 x7 x9)
            (fun (x11 : T) =>
              «mapO»
                (fun (x12 : T) =>
                  «dNode»
                    (leaf 23)
                    ([] : List T)
                    («l2»
                      («dNode»
                        (leaf 2)
                        ([] : List T)
                        («l2» («p1» («p2» x10)) («p1» («p2» x11))))
                      x12))
                (x5 x6 x7 («p1» x10) («p1» x11)))));
    x6

def «appendNR» :=
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

def «hypRule» :=
  fun (x0 : T) =>
    let x1 : T ×
      (T →
        T → List T → T) := (Const.node (leaf 6) («single» x0), «noMatch»);
    x1

def «hypRules» :=
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
        ((«hypRule» x1) :: x2))
      ([] : List (T × (T → T → List T → T)))
      («range» x0);
    x1

def «normH» :=
  fun (x0 : T) (x1 : List T) (x2 : List (T × (T → T → List T → T))) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «byNormW»
        x0
        x1
        (leaf 0)
        («appendNR» («hypRules» («length» x4)) x2)
        (leaf 1024)
        x3
        x4
        x5
        x6);
    x3

def «funExts» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := Const.iter
      (α := List T → List T → T → T → T)
      (fun (x3 : List T → List T → T → T → T) => «byFunExt» x1 (leaf 0) x3)
      x2
      x0;
    x3

def «byListIndWeak» :=
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
        «none»
        (fun (x9 : T) (x10 : List T) =>
          «bindO»
            («listPart» x9)
            (fun (x11 : T) =>
              «bindO»
                («lowerHyps» x0 x2 x10 x6)
                (fun (x12 : T) =>
                  let x13 : List T := Const.children x12;
                  let x14 : List T := (x9 :: (x11 :: x10));
                  let x15 : List T := «mapT» «weaken2» x13;
                  «bindO»
                    («byWeak»
                      x0
                      x1
                      x2
                      x4
                      x10
                      x13
                      («instAt» (leaf 0) («single» x11) x7)
                      («instAt» (leaf 0) («single» x11) x8))
                    (fun (x16 : T) =>
                      «bindO»
                        («byWeak»
                          x0
                          x1
                          x2
                          x4
                          x14
                          x15
                          («listConsAt» (leaf 1) x11 x7)
                          («subst» x3 («atVar0» («weakenElem» x7))))
                        (fun (x17 : T) =>
                          «mapO»
                            (fun (x18 : T) =>
                              «dNode» (leaf 20) («l3» (leaf 0) (leaf 1) x3) («l3» x16 x17 x18))
                            («byWeak»
                              x0
                              x1
                              x2
                              x4
                              x14
                              x15
                              («listConsAt» (leaf 1) x11 x8)
                              («subst» x3 («atVar0» («weakenElem» x8))))))))));
    x5

def «byRoseIndWith» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (_ : List T) (x6 : T) (x7 : T) =>
      if (Const.eq («length» x4) (leaf 1)).label ≠ 0 then
        let x8 : T := «at» x4 (leaf 0);
        «bindO»
          («roseLabel» x8)
          (fun (x9 : T) =>
            «bindO»
              («mTypeIn» x0 x1 x4 x6)
              (fun (x10 : T) =>
                let x11 : List T := «l2» («list» x8) x9;
                «bindO»
                  (x3
                    x11
                    ([] : List T)
                    («roseNodeAt» (leaf 2) x8 x9 x6)
                    («subst» x2 («atVar0» («roseMapAt» (leaf 0) (leaf 1) x10 x6))))
                  (fun (x12 : T) =>
                    «mapO»
                      (fun (x13 : T) =>
                        «dNode» (leaf 32) («l4» (leaf 2) (leaf 0) (leaf 1) x2) («l2» x12 x13))
                      (x3
                        x11
                        ([] : List T)
                        («roseNodeAt» (leaf 2) x8 x9 x7)
                        («subst» x2 («atVar0» («roseMapAt» (leaf 0) (leaf 1) x10 x7)))))))
      else
        «none»);
    x4

def «applyAbs» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «dNode»
      (leaf 22)
      («single» («mEq» x2 x3))
      («l2»
        x4
        («dNode»
          (leaf 24)
          («single» («mEq» («mApp» x2 x0) («mApp» x3 x0)))
          («l2»
            («dNode»
              (leaf 2)
              ([] : List T)
              («l2»
                («dNode» (leaf 3) ([] : List T) ([] : List T))
                («dNode» (leaf 3) ([] : List T) ([] : List T))))
            («dNode»
              (leaf 18)
              ([] : List T)
              («l2»
                («dNode»
                  (leaf 2)
                  ([] : List T)
                  («l2»
                    («dNode» (leaf 17) («l2» x1 (leaf 0)) ([] : List T))
                    («dNode» (leaf 0) ([] : List T) ([] : List T))))
                («dNode» (leaf 0) ([] : List T) ([] : List T)))))));
    x5

def «byListSplit» :=
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
      «bindO»
        («nth» x5 x2)
        (fun (x9 : T) =>
          let x10 : T := «abstractVar» x2 x9 x7;
          let x11 : T := «abstractVar» x2 x9 x8;
          «mapO»
            (fun (x12 : T) =>
              «applyAbs»
                («mVar» x2)
                («length» x6)
                x10
                x11
                («dNode» (leaf 26) ([] : List T) («single» x12)))
            («byListIndWith»
              x0
              x1
              (leaf 0)
              (leaf 1)
              x3
              x4
              (x9 :: x5)
              («mapT» «weaken1» x6)
              («mApp» («weaken1» x10) («mVar» (leaf 0)))
              («mApp» («weaken1» x11) («mVar» (leaf 0))))));
    x5

def «bySplit2» :=
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
      «bindO»
        («nth» x5 x2)
        (fun (x9 : T) =>
          «bindO»
            («coprodParts» x9)
            (fun (x10 : T) =>
              let x11 : T := «p1» x10;
              let x12 : T := «p2» x10;
              let x13 : T := «abstractVar» x2 x9 x7;
              let x14 : T := «abstractVar» x2 x9 x8;
              let x15 : T →
                T →
                  T := (fun (x15 : T) (x16 : T) =>
                «mApp» («weaken1» x16) («mArr» x15 («l2» x11 x12) («mVar» (leaf 0))));
              «bindO»
                (x3 (x11 :: x5) («mapT» «weaken1» x6) (x15 x0 x13) (x15 x0 x14))
                (fun (x16 : T) =>
                  «mapO»
                    (fun (x17 : T) =>
                      «applyAbs»
                        («mVar» x2)
                        («length» x6)
                        x13
                        x14
                        («dNode»
                          (leaf 26)
                          ([] : List T)
                          («single» («dNode» (leaf 34) («l2» x0 x1) («l2» x16 x17)))))
                    (x4 (x12 :: x5) («mapT» «weaken1» x6) (x15 x1 x13) (x15 x1 x14))))));
    x5

def «byListCases» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T → T → T → T := «byListIndWith» x0 x1 (leaf 0) (leaf 1) x2 x2;
    x3

def «bitsInd» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T → T)
    (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «byListIndWith»
      x0
      x1
      (leaf 0)
      (leaf 1)
      x2
      («bySplit» (leaf 3) (leaf 4) (leaf 1) x3);
    x4

def «bitsCases» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T → List T → T → T → T := «bitsInd» x0 x1 x2 x2; x3

def «byBits» :=
  fun (x0 : T) (x1 : List T → List T → T → T → T) (x2 : T) =>
    let x3 : T →
      List T →
        List T →
          T →
            T →
              T := Const.iter
      (α := T → List T → List T → T → T → T)
      (fun (x3 : T → List T → List T → T → T → T) (x4 : T) =>
        «byListSplit»
          x0
          (leaf 0)
          x4
          x1
          («bySplit2» (leaf 3) (leaf 4) (leaf 1) (x3 (leaf 1)) (x3 (leaf 1))))
      (fun (_ : T) => x1)
      x2;
    x3

def «byLength3» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → List T → T → T → T)
    (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «byListSplit»
      x0
      (leaf 0)
      x1
      x3
      («byListSplit»
        x0
        (leaf 0)
        (leaf 0)
        x3
        («byListSplit»
          x0
          (leaf 0)
          (leaf 0)
          x3
          («byListSplit» x0 (leaf 0) (leaf 0) x2 x3)));
    x4

def «withWeakHyps» :=
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
          «bindO»
            («bindO» («nth» x13 x11) «eqParts»)
            (fun (x15 : T) =>
              «bindO»
                («eval» x0 x1 x2 x3 (leaf 4096) x6 x7 x13 («p1» x15))
                (fun (x16 : T) =>
                  «bindO»
                    («eval» x0 x1 x2 x3 (leaf 4096) x6 x7 x13 («p2» x15))
                    (fun (x17 : T) =>
                      let x18 : T := «mEq» («p1» x16) («p1» x17);
                      «mapO»
                        (fun (x19 : T) =>
                          «dNode»
                            (leaf 22)
                            («single» x18)
                            («l2»
                              («dNode»
                                (leaf 24)
                                («single» («mEq» («p1» x15) («p2» x15)))
                                («l2»
                                  («dNode»
                                    (leaf 2)
                                    ([] : List T)
                                    («l2» («p1» («p2» x16)) («p1» («p2» x17))))
                                  («dNode» (leaf 21) («single» x11) ([] : List T))))
                              x19))
                        (x12
                          («append» x13 («single» x18))
                          («appendNR»
                            x14
                            ((«hypRule» («length» x13)) ::
                              ([] : List (T × (T → T → List T → T))))))))))
        (fun (x11 : List T) (x12 : List (T × (T → T → List T → T))) =>
          x5 x12 x7 x11 x9 x10)
        x4
        x8
        ([] : List (T × (T → T → List T → T))));
    x7

def «byListIndHypWeak» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T))) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «byListIndWith»
      x0
      x2
      (leaf 0)
      (leaf 1)
      («byWeak» x0 x1 x2 x3)
      (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
        «withWeakHyps»
          x0
          x1
          x2
          x3
          («single» (Const.sub («length» x5) (leaf 1)))
          (fun (x8 : List (T × (T → T → List T → T))) =>
            «byWeak» x0 x1 x2 («appendNR» x8 x3))
          (leaf 1)
          x4
          x5
          x6
          x7);
    x4

def «byBitsIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List (T × (T → T → List T → T)))
    (x3 : T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := «byListIndWith»
      x0
      (leaf 0)
      (leaf 0)
      (leaf 1)
      («byMode» x3 x0 x1 (leaf 0) x2)
      («bySplit»
        (leaf 3)
        (leaf 4)
        (leaf 1)
        (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
          «withWeakHyps»
            x0
            x1
            (leaf 0)
            x2
            («single» (Const.sub («length» x5) (leaf 1)))
            (fun (x8 : List (T × (T → T → List T → T))) =>
              «byMode» x3 x0 x1 (leaf 0) («appendNR» x8 x2))
            x3
            x4
            x5
            x6
            x7));
    x4

def «rwFun» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.iter
      (α := T)
      (fun (x2 : T) =>
        «dNode»
          (leaf 2)
          ([] : List T)
          («l2» x2 («dNode» (leaf 0) ([] : List T) ([] : List T))))
      («dNode» (leaf 17) («l2» x0 (leaf 0)) ([] : List T))
      x1;
    x2

def «instEqs» :=
  fun (x0 : T) (x1 : T) (x2 : List (List T)) =>
    let x3 : List
      T := Const.foldr
      (α := List T)
      (β := List T)
      (fun (x3 : List T) (x4 : List T) =>
        ((«mEq» («mApps» x0 x3) («mApps» x1 x3)) :: x4))
      ([] : List T)
      x2;
    x3

def «cutInsts» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (List T)) (x4 : T) =>
    let x5 : T := Const.foldr
      (α := List T)
      (β := T)
      (fun (x5 : List T) (x6 : T) =>
        «dNode»
          (leaf 22)
          («single» («mEq» («mApps» x0 x5) («mApps» x1 x5)))
          («l2»
            («dNode»
              (leaf 18)
              ([] : List T)
              («l2»
                («rwFun» x2 («length» x5))
                («dNode» (leaf 0) ([] : List T) ([] : List T))))
            x6))
      x4
      x3;
    x5

def «withInsts» :=
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
      «bindO»
        («bindO» («nth» x9 x4) «eqParts»)
        (fun (x12 : T) =>
          let x13 : List T := «instEqs» («p1» x12) («p2» x12) x5;
          «mapO»
            (fun (x14 : T) => «cutInsts» («p1» x12) («p2» x12) x4 x5 x14)
            («withWeakHyps»
              x0
              x1
              x2
              x3
              («mapT»
                (fun (x14 : T) => Const.add («length» x9) x14)
                («range» («length» x13)))
              x6
              x7
              x8
              («append» x9 x13)
              x10
              x11)));
    x8

def «nthOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «call»
      (leaf 8)
      («single» «omega»)
      («l2»
        («mEq» «mStar» «mStar»)
        (Const.iter
          (α := T)
          (fun (x2 : T) => «call» (leaf 7) («single» «omega») («single» x2))
          x0
          x1));
    x2

def «withChildHyps» :=
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
      «bindO»
        («bindO» («nth» x9 x4) «eqParts»)
        (fun (x12 : T) =>
          Const.foldr
            (α := T)
            (β := List T → List T → T)
            (fun (x13 : T)
               (x14 : List T → List T → T)
               (x15 : List T)
               (x16 : List T) =>
              let x17 : T := «nthOf» («p1» x12) x13;
              let x18 : T := «nthOf» («p2» x12) x13;
              «bindO»
                («eval» x0 x1 x2 x3 (leaf 4096) (leaf 1) x8 x15 x17)
                (fun (x19 : T) =>
                  «bindO»
                    («eval» x0 x1 x2 x3 (leaf 4096) (leaf 1) x8 x15 x18)
                    (fun (x20 : T) =>
                      «bindO»
                        («eval»
                          x0
                          x1
                          x2
                          ((«hypRule» x4) :: ([] : List (T × (T → T → List T → T))))
                          (leaf 4096)
                          (leaf 1)
                          x8
                          x15
                          x17)
                        (fun (x21 : T) =>
                          «bindO»
                            («eqParts» («p1» x19))
                            (fun (x22 : T) =>
                              let x23 : T := «length» x15;
                              let x24 : T := Const.add x23 (leaf 1);
                              let x25 : List (List T) := x6 x13;
                              let x26 : List T := «instEqs» («p1» x22) («p2» x22) x25;
                              «mapO»
                                (fun (x27 : T) =>
                                  «dNode»
                                    (leaf 22)
                                    («single» («mEq» («p1» x19) («p1» x20)))
                                    («l2»
                                      («dNode»
                                        (leaf 24)
                                        («single» («mEq» x17 x18))
                                        («l2»
                                          («dNode»
                                            (leaf 2)
                                            ([] : List T)
                                            («l2» («p1» («p2» x19)) («p1» («p2» x20))))
                                          («dNode»
                                            (leaf 18)
                                            ([] : List T)
                                            («l2»
                                              («p1» («p2» x21))
                                              («dNode» (leaf 0) ([] : List T) ([] : List T))))))
                                      («dNode»
                                        (leaf 22)
                                        («single» («p1» x19))
                                        («l2»
                                          («dNode»
                                            (leaf 23)
                                            ([] : List T)
                                            («l2»
                                              («dNode» (leaf 17) («l2» x23 (leaf 0)) ([] : List T))
                                              («dNode»
                                                (leaf 18)
                                                ([] : List T)
                                                («l2»
                                                  («dNode» (leaf 0) ([] : List T) ([] : List T))
                                                  («dNode» (leaf 0) ([] : List T) ([] : List T))))))
                                          («cutInsts» («p1» x22) («p2» x22) x24 x25 x27)))))
                                (x14
                                  («append»
                                    («append» x15 («l2» («mEq» («p1» x19) («p1» x20)) («p1» x19)))
                                    x26)
                                  («append»
                                    x16
                                    («mapT»
                                      (fun (x27 : T) => Const.add (Const.add x24 (leaf 1)) x27)
                                      («range» («length» x26))))))))))
            (fun (x13 : List T) (x14 : List T) => x7 x14 x8 x13 x10 x11)
            x5
            x9
            ([] : List T)));
    x8

def «subVar» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «subst»
      («weaken1» x1)
      (fun (x2 : T) =>
        if (Const.eq x2 (Const.add x0 (leaf 1))).label ≠ 0 then
          «mVar» (leaf 0)
        else
          «mVar» x2);
    x2

def «revertCase» :=
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
      «bindO»
        («nth» x8 x4)
        (fun (x12 : T) =>
          «bindO»
            («listPart» x12)
            (fun (x13 : T) =>
              «bindO»
                («nth» x9 x5)
                (fun (x14 : T) =>
                  let x15 : T := «mEq» x10 x11;
                  let x16 : T := «ttL» x2;
                  let x17 : T := «abstractVar» x4 x12 («impL» x2 x14 x15);
                  let x18 : T → T := (fun (x18 : T) => «subVar» x4 x18);
                  let x19 : T := x18 x14;
                  let x20 : T := x18 x15;
                  «bindO»
                    («lowerHyps» x0 x1 x8 («append» («mapT» «weaken1» x9) («single» x16)))
                    (fun (x21 : T) =>
                      let x22 : List T := Const.children x21;
                      let x23 : T := «instAt» (leaf 0) («single» x13) x19;
                      let x24 : T := «instAt» (leaf 0) («single» x13) x20;
                      «bindO»
                        («eqParts» x24)
                        (fun (x25 : T) =>
                          «bindO»
                            (x6 x8 («append» x22 («single» x23)) («p1» x25) («p2» x25))
                            (fun (x26 : T) =>
                              let x27 : List
                                T := «append»
                                («mapT» «weaken2» x22)
                                («single» («weakenElem» («impL» x2 x19 x20)));
                              let x28 : T := «listConsAt» (leaf 1) x13 x19;
                              let x29 : T := «listConsAt» (leaf 1) x13 x20;
                              «bindO»
                                («eqParts» x29)
                                (fun (x30 : T) =>
                                  «mapO»
                                    (fun (x31 : T) =>
                                      let x32 : T := «dNode»
                                        (leaf 29)
                                        («l2» (leaf 0) (leaf 1))
                                        («l2»
                                          («impI» x3 («length» x22) x23 x24 x26)
                                          («impI» x3 («length» x27) x28 x29 x31));
                                      let x33 : T := «dNode»
                                        (leaf 26)
                                        ([] : List T)
                                        («single»
                                          («dNode»
                                            (leaf 23)
                                            ([] : List T)
                                            («l2»
                                              («dNode»
                                                (leaf 2)
                                                ([] : List T)
                                                («l2»
                                                  («dNode» (leaf 3) ([] : List T) ([] : List T))
                                                  («dNode» (leaf 3) ([] : List T) ([] : List T))))
                                              («dNode»
                                                (leaf 25)
                                                ([] : List T)
                                                («l2» «trueI» x32)))));
                                      let x34 : T := «dNode»
                                        (leaf 22)
                                        («single» («mEq» x17 («mLam» x12 x16)))
                                        («l2»
                                          x33
                                          («dNode»
                                            (leaf 24)
                                            («single» («mApp» x17 («mVar» x4)))
                                            («l2»
                                              («dNode» (leaf 3) ([] : List T) ([] : List T))
                                              («dNode»
                                                (leaf 23)
                                                ([] : List T)
                                                («l2»
                                                  («dNode»
                                                    (leaf 1)
                                                    ([] : List T)
                                                    («l2»
                                                      («dNode»
                                                        (leaf 2)
                                                        ([] : List T)
                                                        («l2»
                                                          («dNode»
                                                            (leaf 17)
                                                            («l2» («length» x9) (leaf 0))
                                                            ([] : List T))
                                                          («dNode»
                                                            (leaf 0)
                                                            ([] : List T)
                                                            ([] : List T))))
                                                      («dNode»
                                                        (leaf 3)
                                                        ([] : List T)
                                                        ([] : List T))))
                                                  «trueI»)))));
                                      «dNode»
                                        (leaf 27)
                                        («l3»
                                          (Const.add x3 (leaf 4))
                                          (Const.node (leaf 0) ([] : List T))
                                          (Const.node (leaf 0) («l2» x15 x14)))
                                        («l2» x34 («dNode» (leaf 21) («single» x5) ([] : List T))))
                                    (x7
                                      (x12 :: (x13 :: x8))
                                      («append» x27 («single» x28))
                                      («p1» x30)
                                      («p2» x30))))))))));
    x8

def «betaRule» :=
  ((Const.node
    (leaf 0)
    («l2» (leaf 3) (Const.node (leaf 0) ([] : List T))),
    «noMatch») ::
    ([] : List (T × (T → T → List T → T))))

def «byImpI» :=
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
      «bindO»
        («eval» x0 x1 (leaf 0) «betaRule» (leaf 4096) (leaf 0) x5 x6 x7)
        (fun (x9 : T) =>
          «bindO»
            («eval» x0 x1 (leaf 0) «betaRule» (leaf 4096) (leaf 0) x5 x6 x8)
            (fun (x10 : T) =>
              let x11 : T := «p1» x9;
              let x12 : T := «p1» x10;
              if («and»
                («mIs» (leaf 11) (leaf 2) x11)
                (Const.eq (Const.label x12) (leaf 11))).label ≠ 0 then
                if («and»
                  (Const.eq («mD» x11 (leaf 0)) (Const.add x2 (leaf 2)))
                  (Const.eq («mD» x12 (leaf 0)) x2)).label ≠ 0 then
                  let x13 : T := «mArg» x11 (leaf 0);
                  let x14 : T := «mArg» x11 (leaf 1);
                  «bindO»
                    («eqParts» x13)
                    (fun (x15 : T) =>
                      «mapO»
                        (fun (x16 : T) =>
                          «dNode»
                            (leaf 23)
                            ([] : List T)
                            («l2»
                              («dNode»
                                (leaf 2)
                                ([] : List T)
                                («l2» («p1» («p2» x9)) («p1» («p2» x10))))
                              («dNode»
                                (leaf 25)
                                ([] : List T)
                                («l2»
                                  «trueI»
                                  («impI» x3 (Const.add («length» x6) (leaf 1)) x14 x13 x16)))))
                        (x4 x5 («append» x6 («l2» («ttL» x2) x14)) («p1» x15) («p2» x15)))
                else
                  «none»
              else
                «none»)));
    x5

def «withImpElim» :=
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
          «bindO»
            («bindO» («nth» x11 x9) «eqParts»)
            (fun (x13 : T) =>
              let x14 : T := «p1» x13;
              if («mIs» (leaf 11) (leaf 2) x14).label ≠ 0 then
                if (Const.eq
                  («mD» x14 (leaf 0))
                  (Const.add x0 (leaf 2))).label ≠ 0 then
                  let x15 : T := «mArg» x14 (leaf 0);
                  let x16 : T := «mArg» x14 (leaf 1);
                  «mapO»
                    (fun (x17 : T) =>
                      «dNode»
                        (leaf 22)
                        («single» x15)
                        («l2»
                          («dNode»
                            (leaf 27)
                            («l3»
                              (Const.add x1 (leaf 4))
                              (Const.node (leaf 0) ([] : List T))
                              (Const.node (leaf 0) («l2» x15 x16)))
                            («l2»
                              («dNode»
                                (leaf 23)
                                ([] : List T)
                                («l2» («dNode» (leaf 17) («l2» x9 (leaf 0)) ([] : List T)) «trueI»))
                              («dNode» (leaf 21) («single» x2) ([] : List T))))
                          x17))
                    (x10
                      («append» x11 («single» x15))
                      («appendNR»
                        x12
                        ((«hypRule» («length» x11)) ::
                          ([] : List (T × (T → T → List T → T))))))
                else
                  «none»
              else
                «none»))
        (fun (x9 : List T) (x10 : List (T × (T → T → List T → T))) =>
          x4 x10 x5 x9 x7 x8)
        x3
        x6
        ([] : List (T × (T → T → List T → T))));
    x5

def «hypIndex» :=
  fun (x0 : T × (T → T → List T → T)) =>
    let x1 : T := (let x1 : T := (x0).1;
                   if (Const.eq (Const.label x1) (leaf 6)).label ≠ 0 then
                     «some» (Const.child x1 (leaf 0))
                   else
                     «none»);
    x1

def «succPredRw» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if («mIs» (leaf 6) (leaf 2) x2).label ≠ 0 then
      let x3 : List T := «l2» («mVar» (leaf 1)) («mVar» (leaf 0));
      «some»
        («pr»
          («mApp» («mArg» x2 (leaf 0)) («instTerm» ([] : List T) x3 x1))
          («dNode»
            (leaf 2)
            ([] : List T)
            («l2»
              («dNode» (leaf 0) ([] : List T) ([] : List T))
              («dNode»
                (leaf 16)
                («l4»
                  x0
                  (Const.node (leaf 0) ([] : List T))
                  (Const.node (leaf 0) x3)
                  (leaf 1))
                ([] : List T)))))
    else
      «none»);
    x3

def «bySuccPred» :=
  fun (x0 : List T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «bindO»
        («bindO» («nth» x0 x1) «entryLanguage»)
        (fun (x7 : T) =>
          «bindO»
            («eqParts» («thConcl» x7))
            (fun (x8 : T) =>
              «bindO»
                («succPredRw» x1 («p1» x8) x5)
                (fun (x9 : T) =>
                  «bindO»
                    («succPredRw» x1 («p1» x8) x6)
                    (fun (x10 : T) =>
                      «mapO»
                        (fun (x11 : T) =>
                          «dNode»
                            (leaf 23)
                            ([] : List T)
                            («l2»
                              («dNode» (leaf 2) ([] : List T) («l2» («p2» x9) («p2» x10)))
                              x11))
                        (x2 x3 x4 («p1» x9) («p1» x10)))))));
    x3

def «tailTss» :=
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

def «concatTss» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      T := Const.foldr
      (α := List T)
      (β := List T)
      (fun (x1 : List T) (x2 : List T) => «append» x1 x2)
      ([] : List T)
      x0;
    x1

def «subtermsStep» :=
  fun (x0 : T) (x1 : List (List T)) =>
    let x2 : List
      T := (let x2 : T := Const.label x0;
            (x0 ::
              (if (Const.eq x2 (leaf 5)).label ≠ 0 then
                ([] : List T)
              else
                if («or» (Const.eq x2 (leaf 8)) (Const.eq x2 (leaf 9))).label ≠ 0 then
                  «concatTss» (Const.iter (α := List (List T)) «tailTss» x1 (leaf 3))
                else
                  if (Const.eq x2 (leaf 10)).label ≠ 0 then
                    «concatTss» (Const.iter (α := List (List T)) «tailTss» x1 (leaf 2))
                  else
                    «concatTss» («tailTss» x1))));
    x2

def «openSubterms» :=
  fun (x0 : T) =>
    let x1 : List T := Const.para (α := List T) «subtermsStep» x0; x1

def «findSomeT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x0 x2; if («isSome» x4).label ≠ 0 then x4 else x3)
      «none»
      x1;
    x2

def «varUnless» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
      let x2 : T := «mD» x1 (leaf 0);
      if (x0 x2).label ≠ 0 then «none» else «some» x2
    else
      «none»);
    x2

def «scrutVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («mIs» (leaf 6) (leaf 2) x1).label ≠ 0 then
      let x2 : T := «mArg» x1 (leaf 0);
      if («and»
        (Const.eq (Const.label x2) (leaf 7))
        (Const.eq («mD» x2 (leaf 0)) (leaf 5))).label ≠ 0 then
        «varUnless» x0 («mArg» x1 (leaf 1))
      else
        «none»
    else
      «none»);
    x2

def «datumVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («or»
      («mIs» (leaf 8) (leaf 3) x1)
      («mIs» (leaf 9) (leaf 3) x1)).label ≠ 0 then
      «varUnless» x0 («mArg» x1 (leaf 2))
    else
      if («mIs» (leaf 10) (leaf 2) x1).label ≠ 0 then
        «varUnless» x0 («mArg» x1 (leaf 1))
      else
        «none»);
    x2

def «stuckVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «openSubterms» x1;
                   let x3 : T := «findSomeT» («scrutVar» x0) x2;
                   if («isSome» x3).label ≠ 0 then
                     x3
                   else
                     «findSomeT» («datumVar» x0) x2);
    x2

def «mentions» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.lt (leaf 0) («uses» x0 x1); x2

def «eraseDupsTss» :=
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
          (fun (x4 : List T) (x5 : T) => «or» («equalTs» x4 x1) x5)
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

def «matchesWith» :=
  fun (x0 : T → T → List T → T) (x1 : T) (x2 : T) =>
    let x3 : List
      (List
        T) := (let x3 : List
                 T := «mapT»
                 (fun (x3 : T) =>
                   if (Const.lt x3 x1).label ≠ 0 then
                     «none»
                   else
                     «some» («mVar» (Const.sub x3 x1)))
                 («range» (Const.add x1 (leaf 64)));
               «eraseDupsTss»
                 (Const.foldr
                   (α := T)
                   (β := List (List T))
                   (fun (x4 : T) (x5 : List (List T)) =>
                     let x6 : T := «bindO»
                       (x0 (leaf 0) x4 x3)
                       (fun (x6 : T) => «allSomeT» («take» x1 (Const.children x6)));
                     if («isSome» x6).label ≠ 0 then
                       ((«reverse» (Const.children («get» x6))) :: x5)
                     else
                       x5)
                   ([] : List (List T))
                   («openSubterms» x2)));
    x3

def «matchesOf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List (List T) := «matchesWith» («matchTerm» x0) x1 x2; x3

def «appendTss» :=
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

def «instArgs» :=
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
        T) := (let x10 : T := «bindO» («nth» x6 x9) «eqParts»;
               if («isSome» x10).label ≠ 0 then
                 let x11 : T := «p1» («get» x10);
                 if («mIs» (leaf 5) (leaf 1) x11).label ≠ 0 then
                   let x12 : T := «eval»
                     x1
                     x2
                     x3
                     x4
                     (leaf 4096)
                     x0
                     ((«mD» x11 (leaf 0)) :: x5)
                     («mapT» «weaken1» x6)
                     («mArg» x11 (leaf 0));
                   if («isSome» x12).label ≠ 0 then
                     let x13 : T := «p1» («get» x12);
                     «eraseDupsTss»
                       («appendTss»
                         («matchesOf» x13 (leaf 1) x7)
                         («matchesOf» x13 (leaf 1) x8))
                   else
                     ([] : List (List T))
                 else
                   ([] : List (List T))
               else
                 ([] : List (List T)));
    x10

def «byInstsOnce» :=
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
      «bindO»
        («eval» x1 x2 x3 x4 (leaf 4096) x0 x7 x8 x9)
        (fun (x11 : T) =>
          «bindO»
            («eval» x1 x2 x3 x4 (leaf 4096) x0 x7 x8 x10)
            (fun (x12 : T) =>
              let x13 : T := «p1» x11;
              let x14 : T := «p1» x12;
              if (Const.equal x13 x14).label ≠ 0 then
                «byMode» x0 x1 x2 x3 x4 x7 x8 x9 x10
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
                      (List T) := «instArgs» x0 x1 x2 x3 x4 x7 x8 x13 x14 x15;
                    Const.lcase
                      (α := List T)
                      (β := List (T × List (List T)))
                      x17
                      x16
                      (fun (_ : List T) (_ : List (List T)) => ((x15, x17) :: x16)))
                  ([] : List (T × List (List T)))
                  («range»
                    (if (Const.lt x5 («length» x8)).label ≠ 0 then x5 else «length» x8));
                Const.lcase
                  (α := T × List (List T))
                  (β := T)
                  x15
                  «none»
                  (fun (_ : T × List (List T)) (_ : List (T × List (List T))) =>
                    Const.foldr
                      (α := T × List (List T))
                      (β := List (T × (T → T → List T → T)) → List T → List T → T → T → T)
                      (fun (x18 : T × List (List T))
                         (x19 : List (T × (T → T → List T → T)) → List T → List T → T → T → T)
                         (x20 : List (T × (T → T → List T → T))) =>
                        «withInsts»
                          x1
                          x2
                          x3
                          x4
                          (x18).1
                          (x18).2
                          (fun (x21 : List (T × (T → T → List T → T))) =>
                            x19 («appendNR» x20 x21))
                          x0)
                      x6
                      x15
                      ([] : List (T × (T → T → List T → T)))
                      x7
                      x8
                      x9
                      x10))));
    x7

def «instsLast» :=
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
      «byMode» x0 x1 x2 x3 («appendNR» x5 x4));
    x5

def «instsRound» :=
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
      let x12 : T := «byMode» x0 x1 x2 x3 («appendNR» x7 x4) x8 x9 x10 x11;
      if («isSome» x12).label ≠ 0 then
        x12
      else
        «byInstsOnce»
          x0
          x1
          x2
          x3
          («appendNR» x7 x4)
          x5
          (fun (x13 : List (T × (T → T → List T → T))) =>
            x6 («appendNR» x7 x13))
          x8
          x9
          x10
          x11);
    x7

def «byInsts» :=
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
            T := «instsRound»
      x0
      x1
      x2
      x3
      x4
      x5
      («instsRound»
        x0
        x1
        x2
        x3
        x4
        x5
        («instsRound» x0 x1 x2 x3 x4 x5 («instsLast» x0 x1 x2 x3 x4)))
      ([] : List (T × (T → T → List T → T)));
    x6

def «orO» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («isSome» x0).label ≠ 0 then x0 else x1); x2

def «byAuto» :=
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
      let x10 : T := «length» x7;
      Const.iter
        (α := List T → List T → T → T → T)
        (fun (x11 : List T → List T → T → T → T)
           (x12 : List T)
           (x13 : List T)
           (x14 : T)
           (x15 : T) =>
          «orO»
            («byInsts» x5 x0 x1 x2 x3 x10 x12 x13 x14 x15)
            («bindO»
              («eval» x0 x1 x2 x3 (leaf 4096) x5 x12 x13 x14)
              (fun (x16 : T) =>
                «bindO»
                  («eval» x0 x1 x2 x3 (leaf 4096) x5 x12 x13 x15)
                  (fun (x17 : T) =>
                    let x18 : T →
                      T := (fun (x18 : T) =>
                      «anyT» (fun (x19 : T) => «mentions» x19 x18) («take» x10 x13));
                    let x19 : T → T := (fun (_ : T) => leaf 0);
                    «bindO»
                      («orO»
                        («orO» («stuckVar» x18 («p1» x16)) («stuckVar» x18 («p1» x17)))
                        («orO» («stuckVar» x19 («p1» x16)) («stuckVar» x19 («p1» x17))))
                      (fun (x20 : T) =>
                        «bindO»
                          («nth» x12 x20)
                          (fun (x21 : T) =>
                            if («isSome» («listPart» x21)).label ≠ 0 then
                              «byListSplit» x0 x2 x20 x11 x11 x12 x13 x14 x15
                            else
                              if («isSome» («coprodParts» x21)).label ≠ 0 then
                                «bySplit2» (leaf 3) (leaf 4) x20 x11 x11 x12 x13 x14 x15
                              else
                                «none»))))))
        («byInsts» x5 x0 x1 x2 x3 x10)
        x4
        x6
        x7
        x8
        x9);
    x6

def «condParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («and»
      («mIs» (leaf 11) (leaf 3) x0)
      («and»
        (Const.eq («mD» x0 (leaf 0)) (leaf 6))
        (Const.eq
          («length» (Const.children («mD» x0 (leaf 1))))
          (leaf 1)))).label ≠ 0 then
      «some»
        (Const.node
          (leaf 0)
          («l4»
            («at» (Const.children («mD» x0 (leaf 1))) (leaf 0))
            («mArg» x0 (leaf 2))
            («mArg» x0 (leaf 1))
            («mArg» x0 (leaf 0))))
    else
      «none»);
    x1

def «condVar» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «bindO»
      («condParts» x1)
      (fun (x2 : T) => «varUnless» x0 («at» (Const.children x2) (leaf 1)));
    x2

def «stuckVarC» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «orO»
      («findSomeT» («condVar» x0) («openSubterms» x1))
      («stuckVar» x0 x1);
    x2

def «isApps2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «and»
      («mIs» (leaf 6) (leaf 2) x1)
      (let x2 : T := «mArg» x1 (leaf 0);
       «and»
         («mIs» (leaf 6) (leaf 2) x2)
         (let x3 : T := «mArg» x2 (leaf 0);
          «and»
            (Const.eq (Const.label x3) (leaf 11))
            («and»
              (Const.eq («mD» x3 (leaf 0)) x0)
              (Const.equal
                («mD» x3 (leaf 1))
                (Const.node (leaf 0) ([] : List T))))));
    x2

def «appsOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («isApps2» x0 x2).label ≠ 0 then (x2 :: x3) else x3)
      ([] : List T)
      («openSubterms» x1);
    x2

def «unnodeTy» := «prod» «bitsTy» («list» «treeTy»)

def «unnodeStep» :=
  let x0 : T := «nth» «lib» (leaf 4);
  if («isSome» x0).label ≠ 0 then
    Const.lcase
      (α := T)
      (β := T)
      («mArgs» («ldBody» («get» x0)))
      «mStar»
      (fun (x1 : T) (_ : List T) => x1)
  else
    «mStar»

def «unnodeU» :=
  fun (x0 : T) =>
    let x1 : T := «mRoseRec» «unnodeTy» «unnodeStep» x0; x1

def «lenUF» :=
  fun (x0 : List (T → T)) =>
    let x1 : T := Const.foldr
      (α := T → T)
      (β := T)
      (fun (_ : T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «occStep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T)) =>
    let x4 : T →
      T := (fun (x4 : T) =>
      let x5 : T := «dNode» (leaf 0) ([] : List T) ([] : List T);
      let x6 : T := Const.add x1 x4;
      let x7 : T := Const.label x2;
      if (Const.eq x7 (leaf 0)).label ≠ 0 then
        if (Const.eq («mD» x2 (leaf 0)) x6).label ≠ 0 then
          «dNode»
            (leaf 1)
            ([] : List T)
            («l2»
              («dNode»
                (leaf 2)
                ([] : List T)
                («single» («dNode» (leaf 6) ([] : List T) ([] : List T))))
              («dNode»
                (leaf 16)
                («l4»
                  x0
                  (Const.node (leaf 0) ([] : List T))
                  (Const.node (leaf 0) («single» («mVar» x6)))
                  (leaf 0))
                ([] : List T)))
        else
          x5
      else
        if (Const.eq x7 (leaf 5)).label ≠ 0 then
          «dNode»
            (leaf 2)
            ([] : List T)
            (Const.foldr
              (α := T → T)
              (β := List T)
              (fun (x8 : T → T) (x9 : List T) =>
                ((x8 (Const.add x4 (leaf 1))) :: x9))
              ([] : List T)
              («ufTail» x3))
        else
          if («or» (Const.eq x7 (leaf 8)) (Const.eq x7 (leaf 9))).label ≠ 0 then
            «dNode»
              (leaf 2)
              ([] : List T)
              («mapT»
                (fun (x8 : T) =>
                  if (Const.eq x8 (leaf 2)).label ≠ 0 then
                    «ufAt» x3 (Const.add x8 (leaf 1)) x4
                  else
                    x5)
                («range» («lenUF» («ufTail» x3))))
          else
            if (Const.eq x7 (leaf 10)).label ≠ 0 then
              «dNode»
                (leaf 2)
                ([] : List T)
                («mapT»
                  (fun (x8 : T) =>
                    if (Const.eq x8 (leaf 1)).label ≠ 0 then
                      «ufAt» x3 (Const.add x8 (leaf 1)) x4
                    else
                      x5)
                  («range» («lenUF» («ufTail» x3))))
            else
              if («allT»
                (fun (x8 : T) => Const.eq («uses» x8 x6) (leaf 0))
                («mArgs» x2)).label ≠ 0 then
                x5
              else
                «dNode»
                  (leaf 2)
                  ([] : List T)
                  (Const.foldr
                    (α := T → T)
                    (β := List T)
                    (fun (x8 : T → T) (x9 : List T) => ((x8 x4) :: x9))
                    ([] : List T)
                    («ufTail» x3)));
    x4

def «occRewrite» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := Const.para (α := T → T) («occStep» x0 x1) x2 x3; x4

def «byTreeSplit» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «bindO»
        («nth» x3 x1)
        (fun (x7 : T) =>
          if (Const.equal x7 «treeTy»).label ≠ 0 then
            let x8 : T := «abstractVar» x1 x7 x5;
            let x9 : T := «abstractVar» x1 x7 x6;
            let x10 : T := «nodeT» («mPair» («mVar» (leaf 1)) («mVar» (leaf 0)));
            let x11 : T := «mApp» («weaken2» x8) x10;
            let x12 : T := «mApp» («weaken2» x9) x10;
            «mapO»
              (fun (x13 : T) =>
                let x14 : T := «mLam» «bitsTy» («mLam» («list» «treeTy») x11);
                let x15 : T := «mLam» «bitsTy» («mLam» («list» «treeTy») x12);
                let x16 : T := «dNode» (leaf 3) ([] : List T) ([] : List T);
                let x17 : T := «dNode» (leaf 0) ([] : List T) ([] : List T);
                let x18 : T := «dNode» (leaf 2) ([] : List T) («l2» x16 x16);
                let x19 : T := «dNode»
                  (leaf 26)
                  ([] : List T)
                  («single»
                    («dNode»
                      (leaf 23)
                      ([] : List T)
                      («l2»
                        x18
                        («dNode»
                          (leaf 26)
                          ([] : List T)
                          («single» («dNode» (leaf 23) ([] : List T) («l2» x18 x13)))))));
                let x20 : T := «unnodeU» («mVar» x1);
                let x21 : T →
                  T := (fun (x21 : T) =>
                  «mApp» («mApp» x21 («mFst» x20)) («mSnd» x20));
                let x22 : T →
                  T := (fun (x22 : T) =>
                  «dNode»
                    (leaf 1)
                    ([] : List T)
                    («l2»
                      («dNode» (leaf 2) ([] : List T) («l2» x16 x17))
                      («dNode»
                        (leaf 1)
                        ([] : List T)
                        («l2»
                          x16
                          («dNode»
                            (leaf 1)
                            ([] : List T)
                            («l2» x16 («occRewrite» x0 x1 x22 (leaf 0))))))));
                let x23 : T := «dNode»
                  (leaf 18)
                  ([] : List T)
                  («l2»
                    («dNode»
                      (leaf 2)
                      ([] : List T)
                      («l2»
                        («dNode»
                          (leaf 2)
                          ([] : List T)
                          («l2»
                            («dNode» (leaf 17) («l2» («length» x4) (leaf 0)) ([] : List T))
                            x17))
                        x17))
                    x17);
                «dNode»
                  (leaf 22)
                  («single» («mEq» x14 x15))
                  («l2»
                    x19
                    («dNode»
                      (leaf 24)
                      («single» («mEq» (x21 x14) (x21 x15)))
                      («l2»
                        («dNode» (leaf 2) ([] : List T) («l2» (x22 x5) (x22 x6)))
                        x23))))
              (x2
                ((«list» «treeTy») :: («bitsTy» :: x3))
                («mapT» «weaken2» x4)
                x11
                x12)
          else
            «none»));
    x3

def «splitStuck» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «bindO»
      («nth» x5 x3)
      (fun (x9 : T) =>
        if («isSome» («listPart» x9)).label ≠ 0 then
          «byListSplit» x0 x1 x3 x4 x4 x5 x6 x7 x8
        else
          if («isSome» («coprodParts» x9)).label ≠ 0 then
            «bySplit2» (leaf 3) (leaf 4) x3 x4 x4 x5 x6 x7 x8
          else
            if (Const.equal x9 «treeTy»).label ≠ 0 then
              «byTreeSplit» x2 x3 x4 x5 x6 x7 x8
            else
              «none»);
    x9

def «byAutoT» :=
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
      let x11 : T := «length» x8;
      let x12 : List T →
        List T →
          T →
            T →
              T := (fun (x12 : List T) (x13 : List T) (x14 : T) (x15 : T) =>
        «bindO»
          («eval» x0 x1 x2 x4 (leaf 4096) x6 x12 x13 x14)
          (fun (x16 : T) =>
            «bindO»
              («eval» x0 x1 x2 x4 (leaf 4096) x6 x12 x13 x15)
              (fun (x17 : T) =>
                if (Const.equal («p1» x16) («p1» x17)).label ≠ 0 then
                  «some»
                    («dNode»
                      (leaf 18)
                      ([] : List T)
                      («l2» («p1» («p2» x16)) («p1» («p2» x17))))
                else
                  «none»)));
      let x13 : List T →
        List T →
          T →
            T →
              T := (fun (x13 : List T) (x14 : List T) (x15 : T) (x16 : T) =>
        if (Const.eq x11 (leaf 0)).label ≠ 0 then
          «none»
        else
          «byInsts» x6 x0 x1 x2 x4 x11 x13 x14 x15 x16);
      Const.iter
        (α := List T → List T → T → T → T)
        (fun (x14 : List T → List T → T → T → T)
           (x15 : List T)
           (x16 : List T)
           (x17 : T)
           (x18 : T) =>
          «bindO»
            («eval» x0 x1 x2 x4 (leaf 4096) x6 x15 x16 x17)
            (fun (x19 : T) =>
              «bindO»
                («eval» x0 x1 x2 x4 (leaf 4096) x6 x15 x16 x18)
                (fun (x20 : T) =>
                  if (Const.equal («p1» x19) («p1» x20)).label ≠ 0 then
                    «some»
                      («dNode»
                        (leaf 18)
                        ([] : List T)
                        («l2» («p1» («p2» x19)) («p1» («p2» x20))))
                  else
                    «orO»
                      (x13 x15 x16 x17 x18)
                      (let x21 : T →
                         T := (fun (x21 : T) =>
                         «anyT» (fun (x22 : T) => «mentions» x22 x21) («take» x11 x16));
                       let x22 : T → T := (fun (_ : T) => leaf 0);
                       «bindO»
                         («orO»
                           («orO» («stuckVar» x21 («p1» x19)) («stuckVar» x21 («p1» x20)))
                           («orO» («stuckVar» x22 («p1» x19)) («stuckVar» x22 («p1» x20))))
                         (fun (x23 : T) => «splitStuck» x0 x2 x3 x23 x14 x15 x16 x17 x18)))))
        (fun (x14 : List T) (x15 : List T) (x16 : T) (x17 : T) =>
          «orO» (x12 x14 x15 x16 x17) (x13 x14 x15 x16 x17))
        x5
        x7
        x8
        x9
        x10);
    x7

def «byAutoC» :=
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
        «orO»
          («byWeak» x0 x1 x2 x4 x7 x8 x9 x10)
          («bindO»
            («eval» x0 x1 x2 x4 (leaf 4096) (leaf 1) x7 x8 x9)
            (fun (x11 : T) =>
              «bindO»
                («eval» x0 x1 x2 x4 (leaf 4096) (leaf 1) x7 x8 x10)
                (fun (x12 : T) =>
                  let x13 : T → T := (fun (_ : T) => leaf 0);
                  «bindO»
                    («orO» («stuckVarC» x13 («p1» x11)) («stuckVarC» x13 («p1» x12)))
                    (fun (x14 : T) => «splitStuck» x0 x2 x3 x14 x6 x7 x8 x9 x10)))))
      («byWeak» x0 x1 x2 x4)
      x5;
    x6

def «absStep» :=
  fun (x0 : T) (x1 : T) (x2 : List (T → T)) =>
    let x3 : T →
      T := (fun (x3 : T) =>
      if (Const.equal
        x1
        («rename» x0 (fun (x4 : T) => Const.add x4 x3))).label ≠ 0 then
        «mVar» x3
      else
        let x4 : T := Const.label x1;
        let x5 : List T := «mArgs» x1;
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
              («ufTail» x2))
        else
          if («or» (Const.eq x4 (leaf 8)) (Const.eq x4 (leaf 9))).label ≠ 0 then
            x6
              («mapT»
                (fun (x7 : T) =>
                  if (Const.eq x7 (leaf 2)).label ≠ 0 then
                    «ufAt» x2 (Const.add x7 (leaf 1)) x3
                  else
                    «at» x5 x7)
                («range» («lenUF» («ufTail» x2))))
          else
            if (Const.eq x4 (leaf 10)).label ≠ 0 then
              x6
                («mapT»
                  (fun (x7 : T) =>
                    if (Const.eq x7 (leaf 1)).label ≠ 0 then
                      «ufAt» x2 (Const.add x7 (leaf 1)) x3
                    else
                      «at» x5 x7)
                  («range» («lenUF» («ufTail» x2))))
            else
              x6
                (Const.foldr
                  (α := T → T)
                  (β := List T)
                  (fun (x7 : T → T) (x8 : List T) => ((x7 x3) :: x8))
                  ([] : List T)
                  («ufTail» x2)));
    x3

def «abstractTerm» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mLam»
      x0
      (Const.para
        (α := T → T)
        («absStep» («weaken1» x1))
        («weaken1» x2)
        (leaf 0));
    x3

def «maskRwD» :=
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
    let x10 : T := (let x10 : T := «abstractTerm» x1 x6 x9;
                    let x11 : T := «dNode» (leaf 0) ([] : List T) ([] : List T);
                    let x12 : T := «dNode» (leaf 3) ([] : List T) ([] : List T);
                    let x13 : T := «mEq»
                      («condT» x0 x4 («mApp» x10 x6) x5)
                      («condT» x0 x4 («mApp» x10 x7) x5);
                    let x14 : T := «dNode»
                      (leaf 18)
                      ([] : List T)
                      («l2»
                        («dNode»
                          (leaf 1)
                          ([] : List T)
                          («l2»
                            («dNode»
                              (leaf 16)
                              («l4»
                                x2
                                (Const.node (leaf 0) («l2» x0 x1))
                                (Const.node (leaf 0) («l5» x4 x5 x6 x8 x10))
                                (leaf 1))
                              ([] : List T))
                            («dNode»
                              (leaf 1)
                              ([] : List T)
                              («l2»
                                («dNode»
                                  (leaf 2)
                                  ([] : List T)
                                  («l3» x11 («dNode» (leaf 2) ([] : List T) («l2» x11 x3)) x11))
                                («dNode»
                                  (leaf 16)
                                  («l4»
                                    x2
                                    (Const.node (leaf 0) («l2» x0 x1))
                                    (Const.node (leaf 0) («l5» x4 x5 x7 x8 x10))
                                    (leaf 0))
                                  ([] : List T))))))
                        x11);
                    «dNode»
                      (leaf 24)
                      («single» x13)
                      («l2»
                        («dNode»
                          (leaf 2)
                          ([] : List T)
                          («l2»
                            («dNode» (leaf 2) ([] : List T) («l3» x11 x12 x11))
                            («dNode» (leaf 2) ([] : List T) («l3» x11 x12 x11))))
                        x14));
    x10

def «maskRw» :=
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
    let x12 : T := «maskRwD»
      x0
      x1
      x2
      («dNode»
        (leaf 16)
        («l4» x3 (Const.node (leaf 0) x4) (Const.node (leaf 0) x5) (leaf 0))
        ([] : List T))
      x6
      x7
      x8
      x9
      x10
      x11;
    x12

def «maskAt» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «bindO»
      («bindO» («nth» x2 x8) «eqParts»)
      (fun (x9 : T) =>
        let x10 : T := «p1» x9;
        let x11 : T := «p2» x9;
        «bindO»
          («condParts» x10)
          (fun (x12 : T) =>
            let x13 : T := «at» (Const.children x12) (leaf 0);
            let x14 : T := «at» (Const.children x12) (leaf 2);
            let x15 : T := «at» (Const.children x12) (leaf 3);
            if («not»
              (Const.equal («at» (Const.children x12) (leaf 1)) x4)).label ≠ 0 then
              «none»
            else
              «bindO»
                (let x16 : T := «condParts» x11;
                 if («isSome» x16).label ≠ 0 then
                   let x17 : T := «get» x16;
                   if («and»
                     (Const.equal («at» (Const.children x17) (leaf 1)) x4)
                     (Const.equal («at» (Const.children x17) (leaf 3)) x15)).label ≠ 0 then
                     «some»
                       («pr»
                         («at» (Const.children x17) (leaf 2))
                         («dNode» (leaf 17) («l2» x8 (leaf 0)) ([] : List T)))
                   else
                     «none»
                 else
                   if (Const.equal x11 x15).label ≠ 0 then
                     «some»
                       («pr»
                         x11
                         («dNode»
                           (leaf 1)
                           ([] : List T)
                           («l2»
                             («dNode» (leaf 17) («l2» x8 (leaf 0)) ([] : List T))
                             («dNode»
                               (leaf 16)
                               («l4»
                                 x1
                                 (Const.node (leaf 0) («single» x13))
                                 (Const.node (leaf 0) («l2» x4 x11))
                                 (leaf 1))
                               ([] : List T)))))
                   else
                     «none»)
                (fun (x16 : T) =>
                  let x17 : T := «p1» x16;
                  if (Const.equal x14 x17).label ≠ 0 then
                    «none»
                  else
                    let x18 : T := «abstractTerm» x13 x14 x5;
                    «bindO»
                      (Const.lcase
                        (α := T)
                        (β := T)
                        («mArgs» x18)
                        «none»
                        (fun (x19 : T) (_ : List T) => «some» x19))
                      (fun (x19 : T) =>
                        if (Const.eq («uses» x19 (leaf 0)) (leaf 0)).label ≠ 0 then
                          «none»
                        else
                          «some»
                            (Const.node
                              (leaf 0)
                              («l3»
                                x7
                                («condT» x3 x4 («subst» x19 («instVar» x17)) x6)
                                («maskRwD» x3 x13 x0 («p2» x16) x4 x6 x14 x17 x15 x5)))))));
    x9

def «maskSub» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := «findSomeT»
      (fun (x4 : T) =>
        «bindO»
          («condParts» x4)
          (fun (x5 : T) =>
            «findSomeT»
              («maskAt»
                x0
                x1
                x2
                («at» (Const.children x5) (leaf 0))
                («at» (Const.children x5) (leaf 1))
                («at» (Const.children x5) (leaf 2))
                («at» (Const.children x5) (leaf 3))
                x4)
              («reverse» («range» («length» x2)))))
      («openSubterms» x3);
    x4

def «byMaskSubs» :=
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
        «byNF»
          x0
          x1
          (leaf 0)
          («appendNR» x7 x4)
          (leaf 1)
          (fun (x9 : List T) (x10 : List T) (x11 : T) (x12 : T) =>
            let x13 : T := «orO»
              («maskSub» x2 x3 x10 x11)
              («maskSub» x2 x3 x10 x12);
            if («isSome» x13).label ≠ 0 then
              let x14 : T := «at» (Const.children («get» x13)) (leaf 0);
              let x15 : T := «at» (Const.children («get» x13)) (leaf 1);
              «mapO»
                (fun (x16 : T) =>
                  «dNode»
                    (leaf 22)
                    («single» («mEq» x14 x15))
                    («l2» («at» (Const.children («get» x13)) (leaf 2)) x16))
                (x6
                  ((«hypRule» («length» x10)) :: x7)
                  x8
                  x9
                  («append» x10 («single» («mEq» x14 x15)))
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

def «byGeneralize» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      let x7 : T := «abstractTerm» x0 x1 x5;
      let x8 : T := «abstractTerm» x0 x1 x6;
      «mapO»
        (fun (x9 : T) =>
          «applyAbs»
            x1
            («length» x4)
            x7
            x8
            («dNode» (leaf 26) ([] : List T) («single» x9)))
        (x2
          (x0 :: x3)
          («mapT» «weaken1» x4)
          («mApp» («weaken1» x7) («mVar» (leaf 0)))
          («mApp» («weaken1» x8) («mVar» (leaf 0)))));
    x3

end GebMirror.Metalogic

end
