module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «append» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0

def «length» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0

def «reverse» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T)

def «replicate» :=
  fun (x0 : T) (x1 : T) =>
    Const.iter
      (α := List T)
      (fun (x2 : List T) => (x1 :: x2))
      ([] : List T)
      x0

def «single» := fun (x0 : T) => (x0 :: ([] : List T))

def «some» := fun (x0 : T) => Const.node (leaf 1) («single» x0)

def «none» := leaf 0

def «isSome» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «get» := fun (x0 : T) => Const.child x0 (leaf 0)

def «and» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then x1 else leaf 0

def «or» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then leaf 1 else x1

def «at» :=
  fun (x0 : List T) (x1 : T) => Const.child (Const.node (leaf 0) x0) x1

def «nth» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.lt x1 («length» x0)).label ≠ 0 then
      «some» («at» x0 x1)
    else
      «none»

def «tail» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2)

def «drop» :=
  fun (x0 : T) (x1 : List T) => Const.iter (α := List T) «tail» x1 x0

def «digitsMsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    (Const.iter
      (α := T × List T)
      (fun (x3 : T × List T) =>
        (Const.div (x3).1 x0, ((Const.mod (x3).1 x0) :: (x3).2)))
      (x1, ([] : List T))
      x2).2

def «digitsLsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) => «reverse» («digitsMsb» x0 x1 x2)

def «getD» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («isSome» x0).label ≠ 0 then «get» x0 else x1); x2

def «mapO» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («isSome» x1).label ≠ 0 then
      «some» (x0 («get» x1))
    else
      «none»);
    x2

def «bindO» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (if («isSome» x0).label ≠ 0 then
      x1 («get» x0)
    else
      «none»);
    x2

def «not» := fun (x0 : T) => if (x0).label ≠ 0 then leaf 0 else leaf 1

def «isEmpty» := fun (x0 : List T) => Const.eq («length» x0) (leaf 0)

def «equalTs» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.equal (Const.node (leaf 0) x0) (Const.node (leaf 0) x1)

def «take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := «length» x1;
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

def «range» :=
  fun (x0 : T) =>
    let x1 : List
      T := (Const.iter
      (α := T × List T)
      (fun (x1 : T × List T) =>
        (Const.add (x1).1 (leaf 1), «append» (x1).2 («single» (x1).1)))
      (leaf 0, ([] : List T))
      x0).2;
    x1

def «mapT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «allT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «anyT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «allSomeT» :=
  fun (x0 : List T) =>
    let x1 : T := (if («allT» «isSome» x0).label ≠ 0 then
      «some» (Const.node (leaf 0) («mapT» «get» x0))
    else
      «none»);
    x1

def «phVar» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 0)
      («single» (Const.node x0 ([] : List T)));
    x1

def «phOp» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node (Const.add x0 (leaf 1)) x1; x2

def «ptTrees» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «ptValues» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0;
    x1

def «opSig» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «opArgs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «opSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «sortOf» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × T)
      (fun (x3 : T) (x4 : List (T × T)) =>
        let x5 : List T := «ptTrees» x4;
        (Const.node x3 x5,
          if (Const.eq x3 (leaf 0)).label ≠ 0 then
            if (Const.eq («length» x5) (leaf 1)).label ≠ 0 then
              let x6 : T := «at» x5 (leaf 0);
              if (Const.eq (Const.arity x6) (leaf 0)).label ≠ 0 then
                «nth» x1 (Const.label x6)
              else
                «none»
            else
              «none»
          else
            «bindO»
              («nth» x0 (Const.sub x3 (leaf 1)))
              (fun (x6 : T) =>
                if («equalTs»
                  («ptValues» x4)
                  («mapT» «some» («opArgs» x6))).label ≠ 0 then
                  «some» («opSort» x6)
                else
                  «none»)))
      x2).2;
    x3

def «scoped» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «ptTrees» x3;
        (Const.node x2 x4,
          if (Const.eq x2 (leaf 0)).label ≠ 0 then
            if (Const.eq («length» x4) (leaf 1)).label ≠ 0 then
              let x5 : T := «at» x4 (leaf 0);
              «and»
                (Const.eq (Const.arity x5) (leaf 0))
                (Const.lt (Const.label x5) x0)
            else
              leaf 0
          else
            «allT» (fun (x5 : T) => x5) («ptValues» x3)))
      x1).2;
    x2

def «phSubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «ptTrees» x3;
        (Const.node x2 x4,
          if («and»
            (Const.eq x2 (leaf 0))
            (Const.eq («length» x4) (leaf 1))).label ≠ 0 then
            let x5 : T := «at» x4 (leaf 0);
            if (Const.eq (Const.arity x5) (leaf 0)).label ≠ 0 then
              «getD» («nth» x0 (Const.label x5)) («phVar» (Const.label x5))
            else
              Const.node (leaf 0) x4
          else
            Const.node x2 («ptValues» x3)))
      x1).2;
    x2

def «eqn» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «eqLhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «eqRhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «eqSubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «eqn»
      («phSubst» x0 («eqLhs» x1))
      («phSubst» x0 («eqRhs» x1));
    x2

def «eqScoped» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «and»
      («scoped» x0 («eqLhs» x1))
      («scoped» x0 («eqRhs» x1));
    x2

def «seq» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «seqCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «seqHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x3);
    x1

def «seqConcl» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «mkSeq» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «seq»
      (Const.node (leaf 0) x0)
      (Const.node (leaf 0) x1)
      x2;
    x3

def «seqScoped» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «length» («seqCtx» x0);
                   «and»
                     («allT» («eqScoped» x1) («seqHyps» x0))
                     («eqScoped» x1 («seqConcl» x0)));
    x1

def «theory» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «thySig» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «thyAxioms» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «pcTrees» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (List T → List T → T))
      (β := List T)
      (fun (x1 : T × (List T → List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «pcResults» :=
  fun (x0 : List (T × (List T → List T → T)))
    (x1 : List T)
    (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T × (List T → List T → T))
      (β := List T)
      (fun (x3 : T × (List T → List T → T)) (x4 : List T) =>
        (((x3).2 x1 x2) :: x4))
      ([] : List T)
      x0;
    x3

def «pcTail» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          List T →
            T)) := Const.lcase
      (α := T × (List T → List T → T))
      (β := List (T × (List T → List T → T)))
      x0
      ([] : List (T × (List T → List T → T)))
      (fun (_ : T × (List T → List T → T))
         (x2 : List (T × (List T → List T → T))) =>
        x2);
    x1

def «pcPrem» :=
  fun (x0 : List (T × (List T → List T → T))) (x1 : T) =>
    let x2 : List T →
      List T →
        T := Const.lcase
      (α := T × (List T → List T → T))
      (β := List T → List T → T)
      (Const.iter (α := List (T × (List T → List T → T))) «pcTail» x0 x1)
      (fun (_ : List T) (_ : List T) => «none»)
      (fun (x2 : T × (List T → List T → T))
         (_ : List (T × (List T → List T → T))) =>
        (x2).2);
    x2

def «leafIndex» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.arity x0) (leaf 0)).label ≠ 0 then
      «some» (Const.label x0)
    else
      «none»);
    x1

def «inst» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → List T → T)))
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := (let x5 : T := «length» («seqCtx» x1);
                   let x6 : List T := «take» x5 («pcTrees» x2);
                   let x7 : List T := «pcResults» x2 x3 x4;
                   if («and»
                     («seqScoped» x1)
                     («and»
                       («equalTs» («mapT» («sortOf» x0 x3) x6) («mapT» «some» («seqCtx» x1)))
                       («and»
                         («equalTs»
                           («mapT» («mapO» «eqLhs») («take» x5 («drop» x5 x7)))
                           («mapT» «some» x6))
                         («equalTs»
                           («drop» (Const.add x5 x5) x7)
                           («mapT»
                             (fun (x8 : T) => «some» («eqSubst» x6 x8))
                             («seqHyps» x1)))))).label ≠ 0 then
                     «some» («eqSubst» x6 («seqConcl» x1))
                   else
                     «none»);
    x5

def «pShape» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «and» (Const.eq x0 x2) (Const.eq x1 x3); x4

def «pcheckStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List (T × (List T → List T → T)))
    (x5 : List T)
    (x6 : List T) =>
    let x7 : T := (let x7 : T := «length» x3;
                   let x8 : T := «at» x3 (leaf 0);
                   if («pShape» x2 x7 (leaf 0) (leaf 1)).label ≠ 0 then
                     «bindO» («leafIndex» x8) (fun (x9 : T) => «nth» x6 x9)
                   else
                     if («pShape» x2 x7 (leaf 1) (leaf 1)).label ≠ 0 then
                       «bindO»
                         («leafIndex» x8)
                         (fun (x9 : T) =>
                           if (Const.lt x9 («length» x5)).label ≠ 0 then
                             «some» («eqn» («phVar» x9) («phVar» x9))
                           else
                             «none»)
                     else
                       if («pShape» x2 x7 (leaf 2) (leaf 1)).label ≠ 0 then
                         «mapO»
                           (fun (x9 : T) => «eqn» («eqRhs» x9) («eqLhs» x9))
                           («pcPrem» x4 (leaf 0) x5 x6)
                       else
                         if («pShape» x2 x7 (leaf 3) (leaf 2)).label ≠ 0 then
                           «bindO»
                             («pcPrem» x4 (leaf 0) x5 x6)
                             (fun (x9 : T) =>
                               «bindO»
                                 («pcPrem» x4 (leaf 1) x5 x6)
                                 (fun (x10 : T) =>
                                   if (Const.equal («eqRhs» x9) («eqLhs» x10)).label ≠ 0 then
                                     «some» («eqn» («eqLhs» x9) («eqRhs» x10))
                                   else
                                     «none»))
                         else
                           if («and»
                             (Const.eq x2 (leaf 4))
                             (Const.lt (leaf 0) x7)).label ≠ 0 then
                             «bindO»
                               («pcPrem» x4 (leaf 0) x5 x6)
                               (fun (x9 : T) =>
                                 let x10 : List T := «pcResults» («pcTail» x4) x5 x6;
                                 if («and»
                                   («not» (Const.eq (Const.label («eqLhs» x9)) (leaf 0)))
                                   («equalTs»
                                     («mapT» («mapO» «eqLhs») x10)
                                     («mapT» «some» (Const.children («eqLhs» x9))))).label ≠ 0 then
                                   «mapO»
                                     (fun (x11 : T) =>
                                       «eqn»
                                         («eqLhs» x9)
                                         (Const.node
                                           (Const.label («eqLhs» x9))
                                           (Const.children x11)))
                                     («allSomeT» («mapT» («mapO» «eqRhs») x10))
                                 else
                                   «none»)
                           else
                             if («pShape» x2 x7 (leaf 5) (leaf 2)).label ≠ 0 then
                               «bindO»
                                 («leafIndex» x8)
                                 (fun (x9 : T) =>
                                   «bindO»
                                     («pcPrem» x4 (leaf 1) x5 x6)
                                     (fun (x10 : T) =>
                                       if («not»
                                         (Const.eq
                                           (Const.label («eqLhs» x10))
                                           (leaf 0))).label ≠ 0 then
                                         «mapO»
                                           (fun (x11 : T) => «eqn» x11 x11)
                                           («nth» (Const.children («eqLhs» x10)) x9)
                                       else
                                         «none»))
                             else
                               if («and»
                                 (Const.eq x2 (leaf 6))
                                 (Const.lt (leaf 0) x7)).label ≠ 0 then
                                 «bindO»
                                   («leafIndex» x8)
                                   (fun (x9 : T) =>
                                     «bindO»
                                       («nth» («thyAxioms» x0) x9)
                                       (fun (x10 : T) =>
                                         «inst» («thySig» x0) x10 («pcTail» x4) x5 x6))
                               else
                                 if («pShape» x2 x7 (leaf 7) (leaf 2)).label ≠ 0 then
                                   «bindO»
                                     («pcPrem» x4 (leaf 0) x5 x6)
                                     (fun (x9 : T) => «pcPrem» x4 (leaf 1) x5 (x9 :: x6))
                                 else
                                   if («and»
                                     (Const.eq x2 (leaf 8))
                                     (Const.lt (leaf 0) x7)).label ≠ 0 then
                                     «bindO»
                                       («leafIndex» x8)
                                       (fun (x9 : T) =>
                                         «bindO»
                                           («nth» x1 x9)
                                           (fun (x10 : T) =>
                                             «inst» («thySig» x0) x10 («pcTail» x4) x5 x6))
                                   else
                                     «none»);
    x7

def «pcheck» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : List T →
      List T →
        T := (Const.fold
      (α := T × (List T → List T → T))
      (fun (x3 : T) (x4 : List (T × (List T → List T → T))) =>
        let x5 : List T := «pcTrees» x4;
        (Const.node x3 x5,
          fun (x6 : List T) (x7 : List T) => «pcheckStep» x0 x1 x3 x5 x4 x6 x7))
      x2).2;
    x3

def «pdefn» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «pdCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «pdSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «pdBody» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «opVars» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» x0 («mapT» «phVar» («range» x1)); x2

def «pdAxioms» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : T := «opVars» x0 («length» («pdCtx» x1));
            let x3 : T := «pdBody» x1;
            ((«mkSeq» («pdCtx» x1) («single» («eqn» x3 x3)) («eqn» x2 x3)) ::
              («single»
                («mkSeq» («pdCtx» x1) («single» («eqn» x2 x2)) («eqn» x3 x3)))));
    x2

def «thyExtend» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «thySig» x0;
                   «theory»
                     (Const.node
                       (leaf 0)
                       («append»
                         x2
                         («single»
                           («opSig» (Const.node (leaf 0) («pdCtx» x1)) («pdSort» x1)))))
                     (Const.node
                       (leaf 0)
                       («append» («thyAxioms» x0) («pdAxioms» («length» x2) x1))));
    x2

def «thyExtendAll» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «thyExtend» x3 x2)
      x0
      («reverse» x1);
    x2

def «l2» :=
  fun (x0 : T) (x1 : T) => let x2 : List T := (x0 :: («single» x1)); x2

def «l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («l2» x1 x2)); x3

def «l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («l3» x1 x2 x3)); x4

def «l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («l4» x1 x2 x3 x4)); x5

def «l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («l5» x1 x2 x3 x4 x5)); x6

def «os» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «opSig» (Const.node (leaf 0) x0) x1; x2

def «sig» :=
  «append»
    («l4»
      («os» («single» (leaf 1)) (leaf 0))
      («os» («single» (leaf 1)) (leaf 0))
      («os» («single» (leaf 0)) (leaf 1))
      («os» («l2» (leaf 1) (leaf 1)) (leaf 1)))
    («append»
      («l2»
        («os» ([] : List T) (leaf 0))
        («os» («single» (leaf 0)) (leaf 1)))
      («append»
        («l4»
          («os» («l2» (leaf 0) (leaf 0)) (leaf 0))
          («os» («l2» (leaf 0) (leaf 0)) (leaf 1))
          («os» («l2» (leaf 0) (leaf 0)) (leaf 1))
          («os» («l2» (leaf 1) (leaf 1)) (leaf 1)))
        («append»
          («l3»
            («os» («l2» (leaf 1) (leaf 1)) (leaf 0))
            («os» («l2» (leaf 1) (leaf 1)) (leaf 1))
            («os» («l3» (leaf 1) (leaf 1) (leaf 1)) (leaf 1)))
          («append»
            («l2»
              («os» ([] : List T) (leaf 0))
              («os» («single» (leaf 0)) (leaf 1)))
            («append»
              («l4»
                («os» («l2» (leaf 0) (leaf 0)) (leaf 0))
                («os» («l2» (leaf 0) (leaf 0)) (leaf 1))
                («os» («l2» (leaf 0) (leaf 0)) (leaf 1))
                («os» («l2» (leaf 1) (leaf 1)) (leaf 1)))
              («append»
                («l3»
                  («os» («l2» (leaf 1) (leaf 1)) (leaf 0))
                  («os» («l2» (leaf 1) (leaf 1)) (leaf 1))
                  («os» («l3» (leaf 1) (leaf 1) (leaf 1)) (leaf 1)))
                («append»
                  («l3»
                    («os» («l2» (leaf 0) (leaf 0)) (leaf 0))
                    («os» («l2» (leaf 0) (leaf 0)) (leaf 1))
                    («os» («l3» (leaf 0) (leaf 0) (leaf 1)) (leaf 1)))
                  («append»
                    («l4»
                      («os» ([] : List T) (leaf 0))
                      («os» ([] : List T) (leaf 1))
                      («os» («single» (leaf 1)) (leaf 1))
                      («os» («single» (leaf 1)) (leaf 1)))
                    («append»
                      («l4»
                        («os» ([] : List T) (leaf 0))
                        («os» ([] : List T) (leaf 1))
                        («os» ([] : List T) (leaf 1))
                        («os» («l2» (leaf 1) (leaf 1)) (leaf 1)))
                      («append»
                        («l4»
                          («os» («single» (leaf 0)) (leaf 0))
                          («os» («single» (leaf 0)) (leaf 1))
                          («os» («single» (leaf 0)) (leaf 1))
                          («os» («l3» (leaf 0) (leaf 1) (leaf 1)) (leaf 1)))
                        («append»
                          («l3»
                            («os» ([] : List T) (leaf 0))
                            («os» ([] : List T) (leaf 1))
                            («os» («single» (leaf 1)) (leaf 1)))
                          («l3»
                            («os» («single» (leaf 0)) (leaf 0))
                            («os» («single» (leaf 0)) (leaf 1))
                            («os» («l2» (leaf 0) (leaf 1)) (leaf 1))))))))))))))

def «x» := fun (x0 : T) => let x1 : T := «phVar» x0; x1

def «dom» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 0) («single» x0); x1

def «cod» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 1) («single» x0); x1

def «idt» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 2) («single» x0); x1

def «comp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 3) («l2» x0 x1); x2

def «one» := «phOp» (leaf 4) ([] : List T)

def «bang» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 5) («single» x0); x1

def «prod» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 6) («l2» x0 x1); x2

def «cFst» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 7) («l2» x0 x1); x2

def «cSnd» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 8) («l2» x0 x1); x2

def «cPair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 9) («l2» x0 x1); x2

def «eqz» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 10) («l2» x0 x1); x2

def «eqIncl» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 11) («l2» x0 x1); x2

def «eqLift» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «phOp» (leaf 12) («l3» x0 x1 x2); x3

def «cZero» := «phOp» (leaf 13) ([] : List T)

def «absurd» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 14) («single» x0); x1

def «coprod» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 15) («l2» x0 x1); x2

def «inl» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 16) («l2» x0 x1); x2

def «inr» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 17) («l2» x0 x1); x2

def «copair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 18) («l2» x0 x1); x2

def «coeqz» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 19) («l2» x0 x1); x2

def «coeqProj» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 20) («l2» x0 x1); x2

def «coeqDesc» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «phOp» (leaf 21) («l3» x0 x1 x2); x3

def «exp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 22) («l2» x0 x1); x2

def «ev» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 23) («l2» x0 x1); x2

def «curry» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «phOp» (leaf 24) («l3» x0 x1 x2); x3

def «omega» := «phOp» (leaf 25) ([] : List T)

def «tru» := «phOp» (leaf 26) ([] : List T)

def «chi» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 27) («single» x0); x1

def «chiInv» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 28) («single» x0); x1

def «nat» := «phOp» (leaf 29) ([] : List T)

def «zeroN» := «phOp» (leaf 30) ([] : List T)

def «succ» := «phOp» (leaf 31) ([] : List T)

def «natRec» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 32) («l2» x0 x1); x2

def «list» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 33) («single» x0); x1

def «cNil» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 34) («single» x0); x1

def «cCons» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 35) («single» x0); x1

def «listRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «phOp» (leaf 36) («l3» x0 x1 x2); x3

def «rose» := «phOp» (leaf 37) ([] : List T)

def «cNode» := «phOp» (leaf 38) ([] : List T)

def «roseRec» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 39) («single» x0); x1

def «lrose» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 40) («single» x0); x1

def «lnode» :=
  fun (x0 : T) => let x1 : T := «phOp» (leaf 41) («single» x0); x1

def «lroseRec» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «phOp» (leaf 42) («l2» x0 x1); x2

def «dfd» := fun (x0 : T) => let x1 : T := «eqn» x0 x0; x1

def «prodMapLeft» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «cPair»
      («comp» x0 («cFst» («dom» x0) x1))
      («cSnd» («dom» x0) x1);
    x2

def «prodMapRight» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «cPair»
      («cFst» x0 («dom» x1))
      («comp» x1 («cSnd» x0 («dom» x1)));
    x2

def «listMap» :=
  fun (x0 : T) =>
    let x1 : T := «listRec»
      («dom» x0)
      («cNil» («cod» x0))
      («comp» («cCons» («cod» x0)) («prodMapLeft» x0 («list» («cod» x0))));
    x1

def «diag» :=
  fun (x0 : T) => let x1 : T := «cPair» («idt» x0) («idt» x0); x1

def «monoCond» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «dom» x0;
                   let x2 : T := «eqIncl»
                     («comp» x0 («cFst» x1 x1))
                     («comp» x0 («cSnd» x1 x1));
                   «eqn» («comp» («cFst» x1 x1) x2) («comp» («cSnd» x1 x1) x2));
    x1

def «truthEq» :=
  fun (x0 : T) =>
    let x1 : T := «eqz» x0 («comp» «tru» («bang» («dom» x0))); x1

def «truthIncl» :=
  fun (x0 : T) =>
    let x1 : T := «eqIncl» x0 («comp» «tru» («bang» («dom» x0))); x1

def «truthLift» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «eqLift» x0 («comp» «tru» («bang» («dom» x0))) x1; x2

def «sq» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «mkSeq» x0 x1 x2; x3

def «ctxOO» := «l2» (leaf 0) (leaf 0)

def «ctxAA» := «l2» (leaf 1) (leaf 1)

def «ctxAAA» := «l3» (leaf 1) (leaf 1) (leaf 1)

def «ctxA» := «single» (leaf 1)

def «ctxO» := «single» (leaf 0)

def «categoryAxioms» :=
  «append»
    («l6»
      («sq» «ctxA» ([] : List T) («dfd» («dom» («x» (leaf 0)))))
      («sq» «ctxA» ([] : List T) («dfd» («cod» («x» (leaf 0)))))
      («sq» «ctxO» ([] : List T) («dfd» («idt» («x» (leaf 0)))))
      («sq»
        «ctxAA»
        («single» («dfd» («comp» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («cod» («x» (leaf 1))) («dom» («x» (leaf 0)))))
      («sq»
        «ctxAA»
        («single» («eqn» («cod» («x» (leaf 1))) («dom» («x» (leaf 0)))))
        («dfd» («comp» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («comp» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («comp» («x» (leaf 0)) («x» (leaf 1))))
          («dom» («x» (leaf 1))))))
    («l6»
      («sq»
        «ctxAA»
        («single» («dfd» («comp» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («cod» («comp» («x» (leaf 0)) («x» (leaf 1))))
          («cod» («x» (leaf 0)))))
      («sq»
        «ctxAAA»
        («single»
          («dfd»
            («comp» («x» (leaf 0)) («comp» («x» (leaf 1)) («x» (leaf 2))))))
        («eqn»
          («comp» («x» (leaf 0)) («comp» («x» (leaf 1)) («x» (leaf 2))))
          («comp» («comp» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 2)))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («dom» («idt» («x» (leaf 0)))) («x» (leaf 0))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («cod» («idt» («x» (leaf 0)))) («x» (leaf 0))))
      («sq»
        «ctxA»
        ([] : List T)
        («eqn»
          («comp» («x» (leaf 0)) («idt» («dom» («x» (leaf 0)))))
          («x» (leaf 0))))
      («sq»
        «ctxA»
        ([] : List T)
        («eqn»
          («comp» («idt» («cod» («x» (leaf 0)))) («x» (leaf 0)))
          («x» (leaf 0)))))

def «terminalAxioms» :=
  «l4»
    («sq» ([] : List T) ([] : List T) («dfd» «one»))
    («sq»
      «ctxO»
      ([] : List T)
      («eqn» («dom» («bang» («x» (leaf 0)))) («x» (leaf 0))))
    («sq»
      «ctxO»
      ([] : List T)
      («eqn» («cod» («bang» («x» (leaf 0)))) «one»))
    («sq»
      «ctxA»
      («single» («eqn» («cod» («x» (leaf 0))) «one»))
      («eqn» («x» (leaf 0)) («bang» («dom» («x» (leaf 0))))))

def «productAxioms» :=
  «append»
    («l6»
      («sq»
        «ctxOO»
        ([] : List T)
        («dfd» («prod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn»
          («dom» («cFst» («x» (leaf 0)) («x» (leaf 1))))
          («prod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn» («cod» («cFst» («x» (leaf 0)) («x» (leaf 1)))) («x» (leaf 0))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn»
          («dom» («cSnd» («x» (leaf 0)) («x» (leaf 1))))
          («prod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn» («cod» («cSnd» («x» (leaf 0)) («x» (leaf 1)))) («x» (leaf 1))))
      («sq»
        «ctxAA»
        («single» («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1))))))
    («l6»
      («sq»
        «ctxAA»
        («single» («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1)))))
        («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («cPair» («x» (leaf 0)) («x» (leaf 1))))
          («dom» («x» (leaf 0)))))
      («sq»
        «ctxAA»
        («single» («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («cod» («cPair» («x» (leaf 0)) («x» (leaf 1))))
          («prod» («cod» («x» (leaf 0))) («cod» («x» (leaf 1))))))
      («sq»
        «ctxAA»
        («single» («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («comp»
            («cFst» («cod» («x» (leaf 0))) («cod» («x» (leaf 1))))
            («cPair» («x» (leaf 0)) («x» (leaf 1))))
          («x» (leaf 0))))
      («sq»
        «ctxAA»
        («single» («dfd» («cPair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («comp»
            («cSnd» («cod» («x» (leaf 0))) («cod» («x» (leaf 1))))
            («cPair» («x» (leaf 0)) («x» (leaf 1))))
          («x» (leaf 1))))
      («sq»
        («l3» (leaf 1) (leaf 0) (leaf 0))
        («single»
          («eqn» («cod» («x» (leaf 0))) («prod» («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («cPair»
            («comp» («cFst» («x» (leaf 1)) («x» (leaf 2))) («x» (leaf 0)))
            («comp» («cSnd» («x» (leaf 1)) («x» (leaf 2))) («x» (leaf 0))))
          («x» (leaf 0)))))

def «equalizerAxioms» :=
  «append»
    («l6»
      («sq»
        «ctxAA»
        («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («l2»
          («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1))))
          («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1)))))
        («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («eqIncl» («x» (leaf 0)) («x» (leaf 1)))))
        («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («dfd» («eqIncl» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («eqIncl» («x» (leaf 0)) («x» (leaf 1))))
          («eqz» («x» (leaf 0)) («x» (leaf 1))))))
    («append»
      («l6»
        («sq»
          «ctxAA»
          («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («cod» («eqIncl» («x» (leaf 0)) («x» (leaf 1))))
            («dom» («x» (leaf 0)))))
        («sq»
          «ctxAA»
          («single» («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («comp» («x» (leaf 0)) («eqIncl» («x» (leaf 0)) («x» (leaf 1))))
            («comp» («x» (leaf 1)) («eqIncl» («x» (leaf 0)) («x» (leaf 1))))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp» («x» (leaf 0)) («x» (leaf 2)))
            («comp» («x» (leaf 1)) («x» (leaf 2)))))
        («sq»
          «ctxAAA»
          («l2»
            («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1))))
            («eqn»
              («comp» («x» (leaf 0)) («x» (leaf 2)))
              («comp» («x» (leaf 1)) («x» (leaf 2)))))
          («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («dom» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («dom» («x» (leaf 2))))))
      («l3»
        («sq»
          «ctxAAA»
          («single»
            («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («cod» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («eqz» («x» (leaf 0)) («x» (leaf 1)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp»
              («eqIncl» («x» (leaf 0)) («x» (leaf 1)))
              («eqLift» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («x» (leaf 2))))
        («sq»
          «ctxAAA»
          («l2»
            («dfd» («eqz» («x» (leaf 0)) («x» (leaf 1))))
            («eqn» («cod» («x» (leaf 2))) («eqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («eqLift»
              («x» (leaf 0))
              («x» (leaf 1))
              («comp» («eqIncl» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 2))))
            («x» (leaf 2))))))

def «initialAxioms» :=
  «l4»
    («sq» ([] : List T) ([] : List T) («dfd» «cZero»))
    («sq»
      «ctxO»
      ([] : List T)
      («eqn» («dom» («absurd» («x» (leaf 0)))) «cZero»))
    («sq»
      «ctxO»
      ([] : List T)
      («eqn» («cod» («absurd» («x» (leaf 0)))) («x» (leaf 0))))
    («sq»
      «ctxA»
      («single» («eqn» («dom» («x» (leaf 0))) «cZero»))
      («eqn» («x» (leaf 0)) («absurd» («cod» («x» (leaf 0))))))

def «coproductAxioms» :=
  «append»
    («l6»
      («sq»
        «ctxOO»
        ([] : List T)
        («dfd» («coprod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn» («dom» («inl» («x» (leaf 0)) («x» (leaf 1)))) («x» (leaf 0))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn»
          («cod» («inl» («x» (leaf 0)) («x» (leaf 1))))
          («coprod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn» («dom» («inr» («x» (leaf 0)) («x» (leaf 1)))) («x» (leaf 1))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn»
          («cod» («inr» («x» (leaf 0)) («x» (leaf 1))))
          («coprod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1))))))
    («l6»
      («sq»
        «ctxAA»
        («single» («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1)))))
        («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («copair» («x» (leaf 0)) («x» (leaf 1))))
          («coprod» («dom» («x» (leaf 0))) («dom» («x» (leaf 1))))))
      («sq»
        «ctxAA»
        («single» («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («cod» («copair» («x» (leaf 0)) («x» (leaf 1))))
          («cod» («x» (leaf 0)))))
      («sq»
        «ctxAA»
        («single» («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («comp»
            («copair» («x» (leaf 0)) («x» (leaf 1)))
            («inl» («dom» («x» (leaf 0))) («dom» («x» (leaf 1)))))
          («x» (leaf 0))))
      («sq»
        «ctxAA»
        («single» («dfd» («copair» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («comp»
            («copair» («x» (leaf 0)) («x» (leaf 1)))
            («inr» («dom» («x» (leaf 0))) («dom» («x» (leaf 1)))))
          («x» (leaf 1))))
      («sq»
        («l3» (leaf 1) (leaf 0) (leaf 0))
        («single»
          («eqn»
            («dom» («x» (leaf 0)))
            («coprod» («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («copair»
            («comp» («x» (leaf 0)) («inl» («x» (leaf 1)) («x» (leaf 2))))
            («comp» («x» (leaf 0)) («inr» («x» (leaf 1)) («x» (leaf 2)))))
          («x» (leaf 0)))))

def «coequalizerAxioms» :=
  «append»
    («l6»
      («sq»
        «ctxAA»
        («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («l2»
          («eqn» («dom» («x» (leaf 0))) («dom» («x» (leaf 1))))
          («eqn» («cod» («x» (leaf 0))) («cod» («x» (leaf 1)))))
        («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («coeqProj» («x» (leaf 0)) («x» (leaf 1)))))
        («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («dfd» («coeqProj» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxAA»
        («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («coeqProj» («x» (leaf 0)) («x» (leaf 1))))
          («cod» («x» (leaf 0))))))
    («append»
      («l6»
        («sq»
          «ctxAA»
          («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («cod» («coeqProj» («x» (leaf 0)) («x» (leaf 1))))
            («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («sq»
          «ctxAA»
          («single» («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («comp» («coeqProj» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 0)))
            («comp» («coeqProj» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 1)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp» («x» (leaf 2)) («x» (leaf 0)))
            («comp» («x» (leaf 2)) («x» (leaf 1)))))
        («sq»
          «ctxAAA»
          («l2»
            («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1))))
            («eqn»
              («comp» («x» (leaf 2)) («x» (leaf 0)))
              («comp» («x» (leaf 2)) («x» (leaf 1)))))
          («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («dom» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («coeqz» («x» (leaf 0)) («x» (leaf 1))))))
      («l3»
        («sq»
          «ctxAAA»
          («single»
            («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («cod» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («cod» («x» (leaf 2)))))
        («sq»
          «ctxAAA»
          («single»
            («dfd» («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp»
              («coeqDesc» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
              («coeqProj» («x» (leaf 0)) («x» (leaf 1))))
            («x» (leaf 2))))
        («sq»
          «ctxAAA»
          («l2»
            («dfd» («coeqz» («x» (leaf 0)) («x» (leaf 1))))
            («eqn»
              («dom» («x» (leaf 2)))
              («coeqz» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («coeqDesc»
              («x» (leaf 0))
              («x» (leaf 1))
              («comp» («x» (leaf 2)) («coeqProj» («x» (leaf 0)) («x» (leaf 1)))))
            («x» (leaf 2))))))

def «ctxOOA» := «l3» (leaf 0) (leaf 0) (leaf 1)

def «exponentialAxioms» :=
  «append»
    («l6»
      («sq»
        «ctxOO»
        ([] : List T)
        («dfd» («exp» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn»
          («dom» («ev» («x» (leaf 0)) («x» (leaf 1))))
          («prod» («exp» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 0)))))
      («sq»
        «ctxOO»
        ([] : List T)
        («eqn» («cod» («ev» («x» (leaf 0)) («x» (leaf 1)))) («x» (leaf 1))))
      («sq»
        «ctxOOA»
        («single»
          («dfd» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («eqn» («dom» («x» (leaf 2))) («prod» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOOA»
        («single»
          («eqn» («dom» («x» (leaf 2))) («prod» («x» (leaf 0)) («x» (leaf 1)))))
        («dfd» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
      («sq»
        «ctxOOA»
        («single»
          («dfd» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («dom» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
          («x» (leaf 0)))))
    («l3»
      («sq»
        «ctxOOA»
        («single»
          («dfd» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («cod» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
          («exp» («x» (leaf 1)) («cod» («x» (leaf 2))))))
      («sq»
        «ctxOOA»
        («single»
          («dfd» («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («comp»
            («ev» («x» (leaf 1)) («cod» («x» (leaf 2))))
            («prodMapLeft»
              («curry» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
              («x» (leaf 1))))
          («x» (leaf 2))))
      («sq»
        («l4» (leaf 0) (leaf 0) (leaf 0) (leaf 1))
        («l2»
          («eqn» («dom» («x» (leaf 3))) («x» (leaf 0)))
          («eqn» («cod» («x» (leaf 3))) («exp» («x» (leaf 1)) («x» (leaf 2)))))
        («eqn»
          («curry»
            («x» (leaf 0))
            («x» (leaf 1))
            («comp»
              («ev» («x» (leaf 1)) («x» (leaf 2)))
              («prodMapLeft» («x» (leaf 3)) («x» (leaf 1)))))
          («x» (leaf 3)))))

def «classifierAxioms» :=
  «append»
    («l6»
      («sq» ([] : List T) ([] : List T) («dfd» «omega»))
      («sq» ([] : List T) ([] : List T) («eqn» («dom» «tru») «one»))
      («sq» ([] : List T) ([] : List T) («eqn» («cod» «tru») «omega»))
      («sq»
        «ctxA»
        («single» («dfd» («chi» («x» (leaf 0)))))
        («monoCond» («x» (leaf 0))))
      («sq»
        «ctxA»
        («single» («monoCond» («x» (leaf 0))))
        («dfd» («chi» («x» (leaf 0)))))
      («sq»
        «ctxA»
        («single» («dfd» («chi» («x» (leaf 0)))))
        («eqn» («dom» («chi» («x» (leaf 0)))) («cod» («x» (leaf 0))))))
    («append»
      («l6»
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn» («cod» («chi» («x» (leaf 0)))) «omega»))
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn»
            («comp» («chi» («x» (leaf 0))) («x» (leaf 0)))
            («comp» «tru» («bang» («dom» («x» (leaf 0)))))))
        («sq»
          «ctxA»
          («single» («dfd» («chiInv» («x» (leaf 0)))))
          («dfd» («chi» («x» (leaf 0)))))
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («dfd» («chiInv» («x» (leaf 0)))))
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn»
            («dom» («chiInv» («x» (leaf 0))))
            («truthEq» («chi» («x» (leaf 0))))))
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn» («cod» («chiInv» («x» (leaf 0)))) («dom» («x» (leaf 0))))))
      («l3»
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn»
            («comp»
              («truthLift» («chi» («x» (leaf 0))) («x» (leaf 0)))
              («chiInv» («x» (leaf 0))))
            («idt» («truthEq» («chi» («x» (leaf 0)))))))
        («sq»
          «ctxA»
          («single» («dfd» («chi» («x» (leaf 0)))))
          («eqn»
            («comp»
              («chiInv» («x» (leaf 0)))
              («truthLift» («chi» («x» (leaf 0))) («x» (leaf 0))))
            («idt» («dom» («x» (leaf 0))))))
        («sq»
          («l4» (leaf 1) (leaf 1) (leaf 1) (leaf 1))
          («l6»
            («dfd» («chi» («x» (leaf 0))))
            («eqn» («dom» («x» (leaf 1))) («cod» («x» (leaf 0))))
            («eqn» («cod» («x» (leaf 1))) «omega»)
            («eqn»
              («comp» («truthIncl» («x» (leaf 1))) («x» (leaf 2)))
              («x» (leaf 0)))
            («eqn»
              («comp» («x» (leaf 2)) («x» (leaf 3)))
              («idt» («truthEq» («x» (leaf 1)))))
            («eqn»
              («comp» («x» (leaf 3)) («x» (leaf 2)))
              («idt» («dom» («x» (leaf 0))))))
          («eqn» («x» (leaf 1)) («chi» («x» (leaf 0)))))))

def «natAxioms» :=
  «append»
    («l6»
      («sq» ([] : List T) ([] : List T) («eqn» («dom» «zeroN») «one»))
      («sq» ([] : List T) ([] : List T) («eqn» («cod» «zeroN») «nat»))
      («sq» ([] : List T) ([] : List T) («eqn» («dom» «succ») «nat»))
      («sq» ([] : List T) ([] : List T) («eqn» («cod» «succ») «nat»))
      («sq»
        «ctxAA»
        («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («dom» («x» (leaf 0))) «one»))
      («sq»
        «ctxAA»
        («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn» («cod» («x» (leaf 0))) («dom» («x» (leaf 1))))))
    («append»
      («l6»
        («sq»
          «ctxAA»
          («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn» («dom» («x» (leaf 1))) («cod» («x» (leaf 1)))))
        («sq»
          «ctxAA»
          («l3»
            («eqn» («dom» («x» (leaf 0))) «one»)
            («eqn» («cod» («x» (leaf 0))) («dom» («x» (leaf 1))))
            («eqn» («dom» («x» (leaf 1))) («cod» («x» (leaf 1)))))
          («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
        («sq»
          «ctxAA»
          («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn» («dom» («natRec» («x» (leaf 0)) («x» (leaf 1)))) «nat»))
        («sq»
          «ctxAA»
          («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («cod» («natRec» («x» (leaf 0)) («x» (leaf 1))))
            («cod» («x» (leaf 0)))))
        («sq»
          «ctxAA»
          («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («comp» («natRec» («x» (leaf 0)) («x» (leaf 1))) «zeroN»)
            («x» (leaf 0))))
        («sq»
          «ctxAA»
          («single» («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1)))))
          («eqn»
            («comp» («natRec» («x» (leaf 0)) («x» (leaf 1))) «succ»)
            («comp» («x» (leaf 1)) («natRec» («x» (leaf 0)) («x» (leaf 1)))))))
      («single»
        («sq»
          «ctxAAA»
          («l4»
            («dfd» («natRec» («x» (leaf 0)) («x» (leaf 1))))
            («eqn» («dom» («x» (leaf 2))) «nat»)
            («eqn» («comp» («x» (leaf 2)) «zeroN») («x» (leaf 0)))
            («eqn»
              («comp» («x» (leaf 2)) «succ»)
              («comp» («x» (leaf 1)) («x» (leaf 2)))))
          («eqn» («x» (leaf 2)) («natRec» («x» (leaf 0)) («x» (leaf 1)))))))

def «ctxOAA» := «l3» (leaf 0) (leaf 1) (leaf 1)

def «listAxioms» :=
  «append»
    («l6»
      («sq» «ctxO» ([] : List T) («dfd» («list» («x» (leaf 0)))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («dom» («cNil» («x» (leaf 0)))) «one»))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («cod» («cNil» («x» (leaf 0)))) («list» («x» (leaf 0)))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn»
          («dom» («cCons» («x» (leaf 0))))
          («prod» («x» (leaf 0)) («list» («x» (leaf 0))))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («cod» («cCons» («x» (leaf 0)))) («list» («x» (leaf 0)))))
      («sq»
        «ctxOAA»
        («single»
          («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («eqn» («dom» («x» (leaf 1))) «one»)))
    («append»
      («l6»
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn» («cod» («x» (leaf 1))) («cod» («x» (leaf 2)))))
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («dom» («x» (leaf 2)))
            («prod» («x» (leaf 0)) («cod» («x» (leaf 2))))))
        («sq»
          «ctxOAA»
          («l3»
            («eqn» («dom» («x» (leaf 1))) «one»)
            («eqn» («cod» («x» (leaf 1))) («cod» («x» (leaf 2))))
            («eqn»
              («dom» («x» (leaf 2)))
              («prod» («x» (leaf 0)) («cod» («x» (leaf 2))))))
          («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («dom» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («list» («x» (leaf 0)))))
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («cod» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («cod» («x» (leaf 1)))))
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp»
              («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
              («cNil» («x» (leaf 0))))
            («x» (leaf 1)))))
      («l2»
        («sq»
          «ctxOAA»
          («single»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))
          («eqn»
            («comp»
              («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
              («cCons» («x» (leaf 0))))
            («comp»
              («x» (leaf 2))
              («prodMapRight»
                («x» (leaf 0))
                («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))))
        («sq»
          («l4» (leaf 0) (leaf 1) (leaf 1) (leaf 1))
          («l4»
            («dfd» («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2))))
            («eqn» («dom» («x» (leaf 3))) («list» («x» (leaf 0))))
            («eqn» («comp» («x» (leaf 3)) («cNil» («x» (leaf 0)))) («x» (leaf 1)))
            («eqn»
              («comp» («x» (leaf 3)) («cCons» («x» (leaf 0))))
              («comp»
                («x» (leaf 2))
                («prodMapRight» («x» (leaf 0)) («x» (leaf 3))))))
          («eqn»
            («x» (leaf 3))
            («listRec» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))))))

def «roseAxioms» :=
  «append»
    («l6»
      («sq»
        ([] : List T)
        ([] : List T)
        («eqn» («dom» «cNode») («prod» «nat» («list» «rose»))))
      («sq» ([] : List T) ([] : List T) («eqn» («cod» «cNode») «rose»))
      («sq»
        «ctxA»
        («single» («dfd» («roseRec» («x» (leaf 0)))))
        («eqn»
          («dom» («x» (leaf 0)))
          («prod» «nat» («list» («cod» («x» (leaf 0)))))))
      («sq»
        «ctxA»
        («single»
          («eqn»
            («dom» («x» (leaf 0)))
            («prod» «nat» («list» («cod» («x» (leaf 0)))))))
        («dfd» («roseRec» («x» (leaf 0)))))
      («sq»
        «ctxA»
        («single» («dfd» («roseRec» («x» (leaf 0)))))
        («eqn» («dom» («roseRec» («x» (leaf 0)))) «rose»))
      («sq»
        «ctxA»
        («single» («dfd» («roseRec» («x» (leaf 0)))))
        («eqn» («cod» («roseRec» («x» (leaf 0)))) («cod» («x» (leaf 0))))))
    («l2»
      («sq»
        «ctxA»
        («single» («dfd» («roseRec» («x» (leaf 0)))))
        («eqn»
          («comp» («roseRec» («x» (leaf 0))) «cNode»)
          («comp»
            («x» (leaf 0))
            («prodMapRight» «nat» («listMap» («roseRec» («x» (leaf 0))))))))
      («sq»
        «ctxAA»
        («l3»
          («dfd» («roseRec» («x» (leaf 0))))
          («eqn» («dom» («x» (leaf 1))) «rose»)
          («eqn»
            («comp» («x» (leaf 1)) «cNode»)
            («comp»
              («x» (leaf 0))
              («prodMapRight» «nat» («listMap» («x» (leaf 1)))))))
        («eqn» («x» (leaf 1)) («roseRec» («x» (leaf 0))))))

def «ctxOA» := «l2» (leaf 0) (leaf 1)

def «lroseAxioms» :=
  «append»
    («l6»
      («sq» «ctxO» ([] : List T) («dfd» («lrose» («x» (leaf 0)))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn»
          («dom» («lnode» («x» (leaf 0))))
          («prod» («x» (leaf 0)) («list» («lrose» («x» (leaf 0)))))))
      («sq»
        «ctxO»
        ([] : List T)
        («eqn» («cod» («lnode» («x» (leaf 0)))) («lrose» («x» (leaf 0)))))
      («sq»
        «ctxOA»
        («single» («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («x» (leaf 1)))
          («prod» («x» (leaf 0)) («list» («cod» («x» (leaf 1)))))))
      («sq»
        «ctxOA»
        («single»
          («eqn»
            («dom» («x» (leaf 1)))
            («prod» («x» (leaf 0)) («list» («cod» («x» (leaf 1)))))))
        («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1)))))
      («sq»
        «ctxOA»
        («single» («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («dom» («lroseRec» («x» (leaf 0)) («x» (leaf 1))))
          («lrose» («x» (leaf 0))))))
    («l3»
      («sq»
        «ctxOA»
        («single» («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («cod» («lroseRec» («x» (leaf 0)) («x» (leaf 1))))
          («cod» («x» (leaf 1)))))
      («sq»
        «ctxOA»
        («single» («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1)))))
        («eqn»
          («comp»
            («lroseRec» («x» (leaf 0)) («x» (leaf 1)))
            («lnode» («x» (leaf 0))))
          («comp»
            («x» (leaf 1))
            («prodMapRight»
              («x» (leaf 0))
              («listMap» («lroseRec» («x» (leaf 0)) («x» (leaf 1))))))))
      («sq»
        «ctxOAA»
        («l3»
          («dfd» («lroseRec» («x» (leaf 0)) («x» (leaf 1))))
          («eqn» («dom» («x» (leaf 2))) («lrose» («x» (leaf 0))))
          («eqn»
            («comp» («x» (leaf 2)) («lnode» («x» (leaf 0))))
            («comp»
              («x» (leaf 1))
              («prodMapRight» («x» (leaf 0)) («listMap» («x» (leaf 2)))))))
        («eqn» («x» (leaf 2)) («lroseRec» («x» (leaf 0)) («x» (leaf 1))))))

def «axioms» :=
  «append»
    «categoryAxioms»
    («append»
      «terminalAxioms»
      («append»
        «productAxioms»
        («append»
          «equalizerAxioms»
          («append»
            «initialAxioms»
            («append»
              «coproductAxioms»
              («append»
                «coequalizerAxioms»
                («append»
                  «exponentialAxioms»
                  («append»
                    «classifierAxioms»
                    («append»
                      «natAxioms»
                      («append» «listAxioms» («append» «roseAxioms» «lroseAxioms»)))))))))))

def «toposTheory» :=
  «theory» (Const.node (leaf 0) «sig») (Const.node (leaf 0) «axioms»)

def «direct» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «strict» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «rhsRule» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «argSorts» :=
  fun (x0 : T) =>
    let x1 : List
      T := Const.children
      («getD»
        («mapO»
          (fun (x1 : T) => Const.node (leaf 0) («opArgs» x1))
          («nth» «sig» x0))
        (Const.node (leaf 0) ([] : List T)));
    x1

def «findAxiom» :=
  fun (x0 : T → T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x1 : T) (x2 : T × T) =>
        (Const.sub (x2).1 (leaf 1),
          if (x0 x1).label ≠ 0 then
            «some» (Const.sub (x2).1 (leaf 1))
          else
            (x2).2))
      («length» «axioms», «none»)
      «axioms»).2;
    x1

def «dfdRule» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : List T := «argSorts» x0;
                   let x2 : T := «opVars» x0 («length» x1);
                   let x3 : T := «findAxiom»
                     (fun (x3 : T) =>
                       «and»
                         («equalTs» («seqCtx» x3) x1)
                         («and»
                           (Const.equal («eqLhs» («seqConcl» x3)) x2)
                           (Const.equal («eqRhs» («seqConcl» x3)) x2)));
                   if («isSome» x3).label ≠ 0 then
                     «some» («direct» («get» x3))
                   else
                     let x4 : T := «findAxiom»
                       (fun (x4 : T) =>
                         «and»
                           («equalTs» («seqCtx» x4) x1)
                           («and»
                             («isEmpty» («seqHyps» x4))
                             («and»
                               («not» (Const.eq (Const.label («eqLhs» («seqConcl» x4))) (leaf 0)))
                               («equalTs»
                                 (Const.children («eqLhs» («seqConcl» x4)))
                                 («single» x2)))));
                     if («isSome» x4).label ≠ 0 then
                       «some» («strict» («get» x4))
                     else
                       «mapO»
                         «rhsRule»
                         («findAxiom»
                           (fun (x5 : T) =>
                             «and»
                               («isEmpty» («seqCtx» x5))
                               («and»
                                 («isEmpty» («seqHyps» x5))
                                 (Const.equal («eqRhs» («seqConcl» x5)) x2)))));
    x1

def «boundRule» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «argSorts» x1;
                   let x3 : T := «opVars» x1 («length» x2);
                   «findAxiom»
                     (fun (x4 : T) =>
                       «and»
                         («equalTs» («seqCtx» x4) x2)
                         («and»
                           (Const.equal («eqLhs» («seqConcl» x4)) («phOp» x0 («single» x3)))
                           («allT»
                             (fun (x5 : T) => Const.equal («eqLhs» x5) («eqRhs» x5))
                             («seqHyps» x4)))));
    x2

def «dfdRules» := «mapT» «dfdRule» («range» («length» «sig»))

def «domRules» :=
  «mapT» («boundRule» (leaf 0)) («range» («length» «sig»))

def «codRules» :=
  «mapT» («boundRule» (leaf 1)) («range» («length» «sig»))

def «defAxIdx» :=
  fun (x0 : T) =>
    let x1 : T := Const.add («length» «axioms») (Const.mul (leaf 2) x0);
    x1

def «ann» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «annSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x2);
    x1

def «annLo» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «annHi» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «typed» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «tyTerm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «tyAnn» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «ext» :=
  fun (x0 : List T) => let x1 : T := «thyExtendAll» «toposTheory» x0; x1

def «extEnv» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «envDefs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x2);
    x1

def «envAxs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x3);
    x1

def «envSg» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x4);
    x1

def «envDfds» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let x5 : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x5);
    x1

def «envDoms» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let x6 : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x6);
    x1

def «envCods» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let x7 : T := Const.child x1 (leaf 5); Const.children x7);
    x1

def «envOfDefs» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T := «ext» x0;
                   «extEnv»
                     (Const.node (leaf 0) x0)
                     (Const.node (leaf 0) («thyAxioms» x1))
                     (Const.node (leaf 0) («thySig» x1))
                     (Const.node (leaf 0) «dfdRules»)
                     (Const.node (leaf 0) «domRules»)
                     (Const.node (leaf 0) «codRules»));
    x1

def «argSortsOf» :=
  fun (x0 : List T) =>
    let x1 : List T := «mapT» (fun (x1 : T) => «annSort» («tyAnn» x1)) x0;
    x1

def «hypOk» :=
  fun (x0 : List T → T → T) (x1 : List T) (x2 : T) =>
    let x3 : T := (if (Const.equal
      («eqLhs» x2)
      («eqRhs» x2)).label ≠ 0 then
      «isSome» (x0 x1 («eqLhs» x2))
    else
      let x3 : T := x0 x1 («eqLhs» x2);
      let x4 : T := x0 x1 («eqRhs» x2);
      if («and» («isSome» x3) («isSome» x4)).label ≠ 0 then
        let x5 : T := «tyAnn» («get» x3);
        let x6 : T := «tyAnn» («get» x4);
        «and»
          (Const.eq («annSort» x5) (leaf 0))
          («and»
            (Const.eq («annSort» x6) (leaf 0))
            (Const.equal («annLo» x5) («annLo» x6)))
      else
        leaf 0);
    x3

def «bound» :=
  fun (x0 : T)
    (x1 : List T → T → T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T) =>
    let x6 : T := «bindO»
      («nth» («envAxs» x0) x5)
      (fun (x6 : T) =>
        let x7 : T := «opVars» x4 («length» x2);
        if («and»
          («seqScoped» x6)
          («and»
            («equalTs» («seqCtx» x6) («argSortsOf» x2))
            («and»
              (Const.equal («eqLhs» («seqConcl» x6)) («phOp» x3 («single» x7)))
              («allT»
                (fun (x8 : T) =>
                  «and»
                    (Const.equal («eqLhs» x8) («eqRhs» x8))
                    («or» (Const.equal («eqLhs» x8) x7) («isSome» (x1 x2 («eqLhs» x8)))))
                («seqHyps» x6))))).label ≠ 0 then
          «bindO»
            (x1 x2 («eqRhs» («seqConcl» x6)))
            (fun (x8 : T) =>
              if (Const.eq («annSort» («tyAnn» x8)) (leaf 0)).label ≠ 0 then
                «some» («annLo» («tyAnn» x8))
              else
                «none»)
        else
          «none»);
    x6

def «dfdOk» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : List T := «argSortsOf» x2;
                   let x5 : T := «opVars» x3 («length» x2);
                   let x6 : T := «nth» («envDfds» x0) x3;
                   if («and» («isSome» x6) («isSome» («get» x6))).label ≠ 0 then
                     let x7 : T := «get» («get» x6);
                     let x8 : T := x7;
                     if (Const.eq (Const.label x8) (leaf 0)).label ≠ 0 then
                       let x9 : T := Const.child x8 (leaf 0);
                       let x10 : T := «nth» («envAxs» x0) x9;
                       if («isSome» x10).label ≠ 0 then
                         let x11 : T := «get» x10;
                         «and»
                           («seqScoped» x11)
                           («and»
                             («equalTs» («seqCtx» x11) x4)
                             («and»
                               (Const.equal («eqLhs» («seqConcl» x11)) x5)
                               («and»
                                 (Const.equal («eqRhs» («seqConcl» x11)) x5)
                                 («allT» («hypOk» x1 x2) («seqHyps» x11)))))
                       else
                         leaf 0
                     else
                       if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                         let x9 : T := Const.child x8 (leaf 0);
                         let x10 : T := «nth» («envAxs» x0) x9;
                         if («isSome» x10).label ≠ 0 then
                           let x11 : T := «get» x10;
                           «and»
                             («equalTs» («seqCtx» x11) x4)
                             («and»
                               («isEmpty» («seqHyps» x11))
                               («and»
                                 («not»
                                   (Const.eq (Const.label («eqLhs» («seqConcl» x11))) (leaf 0)))
                                 («equalTs»
                                   (Const.children («eqLhs» («seqConcl» x11)))
                                   («single» x5))))
                         else
                           leaf 0
                       else
                         let x9 : T := Const.child x8 (leaf 0);
                         let x10 : T := «nth» («envAxs» x0) x9;
                         if («isSome» x10).label ≠ 0 then
                           let x11 : T := «get» x10;
                           «and»
                             («isEmpty» («seqCtx» x11))
                             («and»
                               («isEmpty» («seqHyps» x11))
                               («and» («isEmpty» x2) (Const.equal («eqRhs» («seqConcl» x11)) x5)))
                         else
                           leaf 0
                   else
                     leaf 0);
    x4

def «inferObj» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := «tyAnn» («at» x1 (leaf 0));
                   if («and»
                     (Const.eq x0 (leaf 0))
                     (Const.eq («length» x1) (leaf 1))).label ≠ 0 then
                     if (Const.eq («annSort» x2) (leaf 1)).label ≠ 0 then
                       «some» («ann» (leaf 0) («annLo» x2) («annLo» x2))
                     else
                       «none»
                   else
                     if («and»
                       (Const.eq x0 (leaf 1))
                       (Const.eq («length» x1) (leaf 1))).label ≠ 0 then
                       if (Const.eq («annSort» x2) (leaf 1)).label ≠ 0 then
                         «some» («ann» (leaf 0) («annHi» x2) («annHi» x2))
                       else
                         «none»
                     else
                       let x3 : T := «phOp»
                         x0
                         («mapT»
                           (fun (x3 : T) =>
                             if (Const.eq («annSort» («tyAnn» x3)) (leaf 0)).label ≠ 0 then
                               «annLo» («tyAnn» x3)
                             else
                               «tyTerm» x3)
                           x1);
                       «some» («ann» (leaf 0) x3 x3));
    x2

def «inferArr» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «bindO»
                     («bindO» («nth» («envDoms» x0) x2) (fun (x4 : T) => x4))
                     («bound» x0 x1 x3 (leaf 0) x2);
                   let x5 : T := «bindO»
                     («bindO» («nth» («envCods» x0) x2) (fun (x5 : T) => x5))
                     («bound» x0 x1 x3 (leaf 1) x2);
                   if («and» («isSome» x4) («isSome» x5)).label ≠ 0 then
                     «some» («ann» (leaf 1) («get» x4) («get» x5))
                   else
                     «none»);
    x4

def «inferDef» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := (let x4 : T := Const.sub x2 («length» «sig»);
                   let x5 : T := «nth» («envDefs» x0) x4;
                   let x6 : T := «nth» («envAxs» x0) («defAxIdx» x4);
                   if («and» («isSome» x5) («isSome» x6)).label ≠ 0 then
                     let x7 : T := «pdBody» («get» x5);
                     let x8 : T := «get» x6;
                     if («and»
                       («seqScoped» x8)
                       («and»
                         («equalTs» («seqCtx» x8) («argSortsOf» x3))
                         («and»
                           («equalTs» («seqHyps» x8) («single» («eqn» x7 x7)))
                           (Const.equal
                             («seqConcl» x8)
                             («eqn» («opVars» x2 («length» x3)) x7))))).label ≠ 0 then
                       «mapO» «tyAnn» (x1 x3 x7)
                     else
                       «none»
                   else
                     «none»);
    x4

def «inferOp» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := «bindO»
      («nth» («envSg» x0) x2)
      (fun (x4 : T) =>
        if («equalTs» («argSortsOf» x3) («opArgs» x4)).label ≠ 0 then
          if (Const.lt x2 («length» «sig»)).label ≠ 0 then
            if («dfdOk» x0 x1 x3 x2).label ≠ 0 then
              if (Const.eq («opSort» x4) (leaf 0)).label ≠ 0 then
                «inferObj» x2 x3
              else
                if (Const.eq («opSort» x4) (leaf 1)).label ≠ 0 then
                  «inferArr» x0 x1 x2 x3
                else
                  «none»
            else
              «none»
          else
            «inferDef» x0 x1 x2 x3
        else
          «none»);
    x4

def «inferSide» :=
  fun (x0 : T) (x1 : List T) (x2 : T → T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «bindO»
                     («nth» («envAxs» x0) x4)
                     (fun (x5 : T) =>
                       «some»
                         («and»
                           («equalTs» («seqCtx» x5) («single» (leaf 1)))
                           («and»
                             («isEmpty» («seqHyps» x5))
                             (Const.equal
                               («seqConcl» x5)
                               («dfd» («phOp» x4 («single» («x» (leaf 0)))))))));
                   if («and» («isSome» x5) («get» x5)).label ≠ 0 then
                     let x6 : T := Const.foldr
                       (α := T)
                       (β := T)
                       (fun (x6 : T) (x7 : T) =>
                         if (Const.equal
                           («eqLhs» x6)
                           («phOp» x4 («single» («phVar» x3)))).label ≠ 0 then
                           «some» x6
                         else
                           x7)
                       «none»
                       x1;
                     if («isSome» x6).label ≠ 0 then
                       «bindO»
                         (x2 («eqRhs» («get» x6)))
                         (fun (x7 : T) =>
                           if (Const.eq («annSort» x7) (leaf 0)).label ≠ 0 then
                             «some» («annLo» x7)
                           else
                             «none»)
                     else
                       «some» («phOp» x4 («single» («phVar» x3)))
                   else
                     «none»);
    x5

def «inferVar» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T → T) (x4 : T) =>
    let x5 : T := «bindO»
      («nth» x1 x4)
      (fun (x5 : T) =>
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          «some» («ann» (leaf 0) («phVar» x4) («phVar» x4))
        else
          if (Const.eq x5 (leaf 1)).label ≠ 0 then
            «bindO»
              («inferSide» x0 x2 x3 x4 (leaf 0))
              (fun (x6 : T) =>
                «mapO»
                  (fun (x7 : T) => «ann» (leaf 1) x6 x7)
                  («inferSide» x0 x2 x3 x4 (leaf 1)))
          else
            «none»);
    x5

def «poTrees» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «poValues» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0;
    x1

def «patInfer» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : List T) (x3 : T) =>
    let x4 : T := (Const.fold
      (α := T × T)
      (fun (x4 : T) (x5 : List (T × T)) =>
        let x6 : List T := «poTrees» x5;
        (Const.node x4 x6,
          if (Const.eq x4 (leaf 0)).label ≠ 0 then
            if (Const.eq («length» x6) (leaf 1)).label ≠ 0 then
              let x7 : T := «at» x6 (leaf 0);
              if (Const.eq (Const.arity x7) (leaf 0)).label ≠ 0 then
                «nth» x2 (Const.label x7)
              else
                «none»
            else
              «none»
          else
            «bindO»
              («allSomeT» («poValues» x5))
              (fun (x7 : T) =>
                let x8 : List T := Const.children x7;
                «mapO»
                  (fun (x9 : T) =>
                    «typed» («phOp» (Const.sub x4 (leaf 1)) («mapT» «tyTerm» x8)) x9)
                  («inferOp» x0 x1 (Const.sub x4 (leaf 1)) x8))))
      x3).2;
    x4

def «treeInfer» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T → T → T)
    (x4 : T → T)
    (x5 : T) =>
    let x6 : T := (Const.fold
      (α := T × T)
      (fun (x6 : T) (x7 : List (T × T)) =>
        let x8 : List T := «poTrees» x7;
        (Const.node x6 x8,
          if (Const.eq x6 (leaf 0)).label ≠ 0 then
            if (Const.eq («length» x8) (leaf 1)).label ≠ 0 then
              let x9 : T := «at» x8 (leaf 0);
              if (Const.eq (Const.arity x9) (leaf 0)).label ≠ 0 then
                «inferVar» x0 x1 x2 x4 (Const.label x9)
              else
                «none»
            else
              «none»
          else
            «bindO»
              («allSomeT» («poValues» x7))
              (fun (x9 : T) =>
                «inferOp»
                  x0
                  x3
                  (Const.sub x6 (leaf 1))
                  (Const.foldr
                    (α := T)
                    (β := List T × List T)
                    (fun (x10 : T) (x11 : List T × List T) =>
                      («tail» (x11).1, ((«typed» x10 («at» (x11).1 (leaf 0))) :: (x11).2)))
                    («reverse» (Const.children x9), ([] : List T))
                    x8).2)))
      x5).2;
    x6

def «infers» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : (List T → T → T) ×
      (T →
        T) := Const.iter
      (α := (List T → T → T) × (T → T))
      (fun (x4 : (List T → T → T) × (T → T)) =>
        (fun (x5 : List T) (x6 : T) => «patInfer» x0 (x4).1 x5 x6,
          fun (x5 : T) => «treeInfer» x0 x1 x2 (x4).1 (x4).2 x5))
      (fun (_ : List T) (_ : T) => «none», fun (_ : T) => «none»)
      x3;
    x4

def «inferFuel» := leaf 8

def «pr» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 0) («l2» x0 x1); x2

def «p1» := fun (x0 : T) => let x1 : T := Const.child x0 (leaf 0); x1

def «p2» := fun (x0 : T) => let x1 : T := Const.child x0 (leaf 1); x1

def «mNode» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := Const.node x0 ((Const.node (leaf 0) x1) :: x2); x3

def «mVar» :=
  fun (x0 : T) =>
    let x1 : T := «mNode» (leaf 0) («single» x0) ([] : List T); x1

def «mStar» := «mNode» (leaf 1) ([] : List T) ([] : List T)

def «mPair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mNode» (leaf 2) ([] : List T) («l2» x0 x1); x2

def «mFst» :=
  fun (x0 : T) =>
    let x1 : T := «mNode» (leaf 3) ([] : List T) («single» x0); x1

def «mSnd» :=
  fun (x0 : T) =>
    let x1 : T := «mNode» (leaf 4) ([] : List T) («single» x0); x1

def «mLam» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mNode» (leaf 5) («single» x0) («single» x1); x2

def «mApp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mNode» (leaf 6) ([] : List T) («l2» x0 x1); x2

def «mArr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «mNode»
      (leaf 7)
      («l2» x0 (Const.node (leaf 0) x1))
      («single» x2);
    x3

def «mNatRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mNode» (leaf 8) ([] : List T) («l3» x0 x1 x2); x3

def «mListRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mNode» (leaf 9) ([] : List T) («l3» x0 x1 x2); x3

def «mRoseRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mNode» (leaf 10) («single» x0) («l2» x1 x2); x3

def «mDefn» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «mNode» (leaf 11) («l2» x0 (Const.node (leaf 0) x1)) x2;
    x3

def «mEq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «mNode» (leaf 12) ([] : List T) («l2» x0 x1); x2

def «mData» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children (Const.child x0 (leaf 0)); x1

def «mArgs» :=
  fun (x0 : T) => let x1 : List T := «tail» (Const.children x0); x1

def «mIs» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «and»
      (Const.eq (Const.label x2) x0)
      (Const.eq («length» («mArgs» x2)) x1);
    x3

def «mArg» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «at» («mArgs» x0) x1; x2

def «mD» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «at» («mData» x0) x1; x2

def «rpTrees» :=
  fun (x0 : List (T × ((T → T) → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × ((T → T) → T))
      (β := List T)
      (fun (x1 : T × ((T → T) → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «rpTail» :=
  fun (x0 : List (T × ((T → T) → T))) =>
    let x1 : List
      (T ×
        ((T → T) →
          T)) := Const.lcase
      (α := T × ((T → T) → T))
      (β := List (T × ((T → T) → T)))
      x0
      ([] : List (T × ((T → T) → T)))
      (fun (_ : T × ((T → T) → T)) (x2 : List (T × ((T → T) → T))) => x2);
    x1

def «rpAll» :=
  fun (x0 : List (T × ((T → T) → T))) (x1 : T → T) =>
    let x2 : List
      T := Const.foldr
      (α := T × ((T → T) → T))
      (β := List T)
      (fun (x2 : T × ((T → T) → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0;
    x2

def «rpAt» :=
  fun (x0 : List (T × ((T → T) → T))) (x1 : T) (x2 : T → T) =>
    let x3 : T := Const.lcase
      (α := T × ((T → T) → T))
      (β := T)
      (Const.iter (α := List (T × ((T → T) → T))) «rpTail» x0 x1)
      (leaf 0)
      (fun (x3 : T × ((T → T) → T)) (_ : List (T × ((T → T) → T))) =>
        (x3).2 x2);
    x3

def «travStep» :=
  fun (x0 : (T → T) → T → T)
    (x1 : T → T)
    (x2 : T)
    (x3 : List (T × ((T → T) → T)))
    (x4 : T → T) =>
    let x5 : T := (let x5 : T := «at» («rpTrees» x3) (leaf 0);
                   let x6 : List (T × ((T → T) → T)) := «rpTail» x3;
                   let x7 : List T := «rpTrees» x6;
                   let x8 : T := «length» x7;
                   if (Const.eq x2 (leaf 0)).label ≠ 0 then
                     x1 (x4 («at» (Const.children x5) (leaf 0)))
                   else
                     if («and»
                       (Const.eq x2 (leaf 5))
                       (Const.eq x8 (leaf 1))).label ≠ 0 then
                       Const.node x2 (x5 :: («single» («rpAt» x6 (leaf 0) (x0 x4))))
                     else
                       if («and»
                         («or» (Const.eq x2 (leaf 8)) (Const.eq x2 (leaf 9)))
                         (Const.eq x8 (leaf 3))).label ≠ 0 then
                         Const.node
                           x2
                           (x5 ::
                             («l3» («at» x7 (leaf 0)) («at» x7 (leaf 1)) («rpAt» x6 (leaf 2) x4)))
                       else
                         if («and»
                           (Const.eq x2 (leaf 10))
                           (Const.eq x8 (leaf 2))).label ≠ 0 then
                           Const.node
                             x2
                             (x5 :: («l2» («at» x7 (leaf 0)) («rpAt» x6 (leaf 1) x4)))
                         else
                           Const.node x2 (x5 :: («rpAll» x6 x4)));
    x5

def «trav» :=
  fun (x0 : (T → T) → T → T) (x1 : T → T) (x2 : T) =>
    let x3 : (T → T) →
      T := (Const.fold
      (α := T × ((T → T) → T))
      (fun (x3 : T) (x4 : List (T × ((T → T) → T))) =>
        (Const.node x3 («rpTrees» x4),
          fun (x5 : T → T) => «travStep» x0 x1 x3 x4 x5))
      x2).2;
    x3

def «liftR» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      leaf 0
    else
      Const.add (x0 (Const.sub x1 (leaf 1))) (leaf 1));
    x2

def «rename» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := «trav» «liftR» «mVar» x0 x1; x2

def «liftS» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      «mVar» (leaf 0)
    else
      «rename»
        (x0 (Const.sub x1 (leaf 1)))
        (fun (x2 : T) => Const.add x2 (leaf 1)));
    x2

def «subst» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := «trav» «liftS» (fun (x2 : T) => x2) x0 x1; x2

def «substList» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «getD» («nth» x0 x1) («mVar» x1); x2

def «dataOsubst» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := (if («or»
      (Const.eq x1 (leaf 5))
      (Const.eq x1 (leaf 10))).label ≠ 0 then
      «mapT» («phSubst» x0) x2
    else
      if («or»
        (Const.eq x1 (leaf 7))
        (Const.eq x1 (leaf 11))).label ≠ 0 then
        «l2»
          («at» x2 (leaf 0))
          (Const.node
            (leaf 0)
            («mapT» («phSubst» x0) (Const.children («at» x2 (leaf 1)))))
      else
        x2);
    x3

def «osubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «ptTrees» x3;
        (Const.node x2 x4,
          Const.node
            x2
            ((Const.node
              (leaf 0)
              («dataOsubst» x0 x2 (Const.children («at» x4 (leaf 0))))) ::
              («tail» («ptValues» x3)))))
      x1).2;
    x2

def «tyOps» :=
  ((«pr» (leaf 4) (leaf 0)) ::
    ((«pr» (leaf 6) (leaf 2)) ::
      ((«pr» (leaf 13) (leaf 0)) ::
        ((«pr» (leaf 15) (leaf 2)) ::
          ((«pr» (leaf 22) (leaf 2)) ::
            ((«pr» (leaf 25) (leaf 0)) ::
              ((«pr» (leaf 29) (leaf 0)) ::
                ((«pr» (leaf 33) (leaf 1)) ::
                  ((«pr» (leaf 37) (leaf 0)) ::
                    («single» («pr» (leaf 40) (leaf 1))))))))))))

def «binParts» :=
  fun (x0 : T → T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
      let x2 : T := Const.child x1 (leaf 0);
      let x3 : T := Const.child x1 (leaf 1);
      if (Const.equal x1 (x0 x2 x3)).label ≠ 0 then
        «some» («pr» x2 x3)
      else
        «none»
    else
      «none»);
    x2

def «prodParts» :=
  fun (x0 : T) => let x1 : T := «binParts» «prod» x0; x1

def «coprodParts» :=
  fun (x0 : T) => let x1 : T := «binParts» «coprod» x0; x1

def «expParts» :=
  fun (x0 : T) => let x1 : T := «binParts» «exp» x0; x1

def «listPart» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.arity x0) (leaf 1)).label ≠ 0 then
      let x1 : T := Const.child x0 (leaf 0);
      if (Const.equal x0 («list» x1)).label ≠ 0 then «some» x1 else «none»
    else
      «none»);
    x1

def «roseLabel» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.equal x0 «rose»).label ≠ 0 then
      «some» «nat»
    else
      if (Const.eq (Const.arity x0) (leaf 1)).label ≠ 0 then
        let x1 : T := Const.child x0 (leaf 0);
        if (Const.equal x0 («lrose» x1)).label ≠ 0 then «some» x1 else «none»
      else
        «none»);
    x1

def «roseFold» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.equal x0 «rose»).label ≠ 0 then
      «roseRec» x1
    else
      «lroseRec» (Const.child x0 (leaf 0)) x1);
    x2

def «ctxObj» :=
  fun (x0 : List T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x1 : T) (x2 : T × T) =>
        (if ((x2).2).label ≠ 0 then «prod» (x2).1 x1 else x1, leaf 1))
      («one», leaf 0)
      x0).1;
    x1

def «extendEnv» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := ((«pr» («cSnd» x0 x1) x1) ::
      («mapT»
        (fun (x3 : T) => «pr» («comp» («p1» x3) («cFst» x0 x1)) («p2» x3))
        x2));
    x3

def «stdEnv» :=
  fun (x0 : List T) =>
    let x1 : List
      T := (Const.foldr
      (α := T)
      (β := List T × List T)
      (fun (x1 : T) (x2 : List T × List T) =>
        (if («isEmpty» (x2).2).label ≠ 0 then
          «single» («pr» («idt» x1) x1)
        else
          «extendEnv» («ctxObj» (x2).2) x1 (x2).1,
          (x1 :: (x2).2)))
      (([] : List T), ([] : List T))
      x0).1;
    x1

def «tuple» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x2 : T) (x3 : T × T) =>
        (if ((x3).2).label ≠ 0 then «cPair» (x3).1 x2 else x2, leaf 1))
      («bang» x0, leaf 0)
      x1).1;
    x2

def «ldefn» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «ldArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «ldParams» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x3);
    x1

def «ldType» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x4);
    x1

def «ldBody» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «primitive» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «prArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «prArrow» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x3);
    x1

def «prDom» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x4);
    x1

def «prCod» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «defLang» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «defObj» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «defLanguage» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); «some» x2
                   else
                     let _ : T := Const.child x1 (leaf 0);
                     let _ : T := Const.child x1 (leaf 1); «none»);
    x1

def «globals» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «gPrims» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «gDefs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x3);
    x1

def «gBase» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «isTyOp» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «or»
      («anyT» (fun (x3 : T) => Const.equal x3 («pr» x1 x2)) «tyOps»)
      («and»
        («not» (Const.lt x1 («gBase» x0)))
        (let x3 : T := «nth» («gDefs» x0) (Const.sub x1 («gBase» x0));
         if («isSome» x3).label ≠ 0 then
           let x4 : T := «get» x3;
           if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
             let _ : T := Const.child x4 (leaf 0); leaf 0
           else
             let x5 : T := Const.child x4 (leaf 0);
             let _ : T := Const.child x4 (leaf 1); Const.eq x5 x2
         else
           leaf 0));
    x3

def «mIsTy» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × T)
      (fun (x3 : T) (x4 : List (T × T)) =>
        let x5 : List T := «ptTrees» x4;
        (Const.node x3 x5,
          if (Const.eq x3 (leaf 0)).label ≠ 0 then
            if (Const.eq («length» x5) (leaf 1)).label ≠ 0 then
              let x6 : T := «at» x5 (leaf 0);
              «and»
                (Const.eq (Const.arity x6) (leaf 0))
                (Const.lt (Const.label x6) x1)
            else
              leaf 0
          else
            «and»
              («isTyOp» x0 (Const.sub x3 (leaf 1)) («length» x5))
              («allT» (fun (x6 : T) => x6) («ptValues» x4))))
      x2).2;
    x3

def «cpTrees» :=
  fun (x0 : List (T × (T → List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (T → List T → T))
      (β := List T)
      (fun (x1 : T × (T → List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «cpTail» :=
  fun (x0 : List (T × (T → List T → T))) =>
    let x1 : List
      (T ×
        (T →
          List T →
            T)) := Const.lcase
      (α := T × (T → List T → T))
      (β := List (T × (T → List T → T)))
      x0
      ([] : List (T × (T → List T → T)))
      (fun (_ : T × (T → List T → T)) (x2 : List (T × (T → List T → T))) =>
        x2);
    x1

def «cpAt» :=
  fun (x0 : List (T × (T → List T → T))) (x1 : T) =>
    let x2 : T →
      List T →
        T := Const.lcase
      (α := T × (T → List T → T))
      (β := T → List T → T)
      (Const.iter (α := List (T × (T → List T → T))) «cpTail» x0 x1)
      (fun (_ : T) (_ : List T) => «none»)
      (fun (x2 : T × (T → List T → T)) (_ : List (T × (T → List T → T))) =>
        (x2).2);
    x2

def «cpAll» :=
  fun (x0 : List (T × (T → List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T × (T → List T → T))
      (β := List T)
      (fun (x3 : T × (T → List T → T)) (x4 : List T) =>
        (((x3).2 x1 x2) :: x4))
      ([] : List T)
      x0;
    x3

def «compileStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List (T × (T → List T → T)))
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := (let x6 : List T := Const.children («at» («cpTrees» x3) (leaf 0));
                   let x7 : List (T × (T → List T → T)) := «cpTail» x3;
                   let x8 : T := «length» («cpTrees» x7);
                   let x9 : T → List T → T := «cpAt» x7 (leaf 0);
                   let x10 : T → List T → T := «cpAt» x7 (leaf 1);
                   let x11 : T → List T → T := «cpAt» x7 (leaf 2);
                   if («and»
                     (Const.eq x2 (leaf 0))
                     (Const.eq x8 (leaf 0))).label ≠ 0 then
                     «nth» x5 («at» x6 (leaf 0))
                   else
                     if («and»
                       (Const.eq x2 (leaf 1))
                       (Const.eq x8 (leaf 0))).label ≠ 0 then
                       «some» («pr» («bang» x4) «one»)
                     else
                       if («and»
                         (Const.eq x2 (leaf 2))
                         (Const.eq x8 (leaf 2))).label ≠ 0 then
                         «bindO»
                           (x9 x4 x5)
                           (fun (x12 : T) =>
                             «bindO»
                               (x10 x4 x5)
                               (fun (x13 : T) =>
                                 «some»
                                   («pr»
                                     («cPair» («p1» x12) («p1» x13))
                                     («prod» («p2» x12) («p2» x13)))))
                       else
                         if («and»
                           («or» (Const.eq x2 (leaf 3)) (Const.eq x2 (leaf 4)))
                           (Const.eq x8 (leaf 1))).label ≠ 0 then
                           «bindO»
                             (x9 x4 x5)
                             (fun (x12 : T) =>
                               «bindO»
                                 («prodParts» («p2» x12))
                                 (fun (x13 : T) =>
                                   if (Const.eq x2 (leaf 3)).label ≠ 0 then
                                     «some»
                                       («pr»
                                         («comp» («cFst» («p1» x13) («p2» x13)) («p1» x12))
                                         («p1» x13))
                                   else
                                     «some»
                                       («pr»
                                         («comp» («cSnd» («p1» x13) («p2» x13)) («p1» x12))
                                         («p2» x13))))
                         else
                           if («and»
                             (Const.eq x2 (leaf 5))
                             (Const.eq x8 (leaf 1))).label ≠ 0 then
                             let x12 : T := «at» x6 (leaf 0);
                             if («mIsTy» x0 x1 x12).label ≠ 0 then
                               «bindO»
                                 (x9 («prod» x4 x12) («extendEnv» x4 x12 x5))
                                 (fun (x13 : T) =>
                                   «some» («pr» («curry» x4 x12 («p1» x13)) («exp» x12 («p2» x13))))
                             else
                               «none»
                           else
                             if («and»
                               (Const.eq x2 (leaf 6))
                               (Const.eq x8 (leaf 2))).label ≠ 0 then
                               «bindO»
                                 (x9 x4 x5)
                                 (fun (x12 : T) =>
                                   «bindO»
                                     («expParts» («p2» x12))
                                     (fun (x13 : T) =>
                                       «bindO»
                                         (x10 x4 x5)
                                         (fun (x14 : T) =>
                                           if (Const.equal («p2» x14) («p1» x13)).label ≠ 0 then
                                             «some»
                                               («pr»
                                                 («comp»
                                                   («ev» («p1» x13) («p2» x13))
                                                   («cPair» («p1» x12) («p1» x14)))
                                                 («p2» x13))
                                           else
                                             «none»)))
                             else
                               if («and»
                                 (Const.eq x2 (leaf 7))
                                 (Const.eq x8 (leaf 1))).label ≠ 0 then
                                 let x12 : List T := Const.children («at» x6 (leaf 1));
                                 «bindO»
                                   («nth» («gPrims» x0) («at» x6 (leaf 0)))
                                   (fun (x13 : T) =>
                                     «bindO»
                                       (x9 x4 x5)
                                       (fun (x14 : T) =>
                                         if («and»
                                           (Const.eq («length» x12) («prArity» x13))
                                           («and»
                                             («allT» («mIsTy» x0 x1) x12)
                                             (Const.equal
                                               («p2» x14)
                                               («phSubst» x12 («prDom» x13))))).label ≠ 0 then
                                           «some»
                                             («pr»
                                               («comp» («phSubst» x12 («prArrow» x13)) («p1» x14))
                                               («phSubst» x12 («prCod» x13)))
                                         else
                                           «none»))
                               else
                                 if («and»
                                   (Const.eq x2 (leaf 8))
                                   (Const.eq x8 (leaf 3))).label ≠ 0 then
                                   «bindO»
                                     (x9 «one» ([] : List T))
                                     (fun (x12 : T) =>
                                       let x13 : T := «p2» x12;
                                       «bindO»
                                         (x10 x13 («single» («pr» («idt» x13) x13)))
                                         (fun (x14 : T) =>
                                           «bindO»
                                             (x11 x4 x5)
                                             (fun (x15 : T) =>
                                               if («and»
                                                 (Const.equal («p2» x14) x13)
                                                 (Const.equal («p2» x15) «nat»)).label ≠ 0 then
                                                 «some»
                                                   («pr»
                                                     («comp»
                                                       («natRec» («p1» x12) («p1» x14))
                                                       («p1» x15))
                                                     x13)
                                               else
                                                 «none»)))
                                 else
                                   if («and»
                                     (Const.eq x2 (leaf 9))
                                     (Const.eq x8 (leaf 3))).label ≠ 0 then
                                     «bindO»
                                       (x11 x4 x5)
                                       (fun (x12 : T) =>
                                         «bindO»
                                           («listPart» («p2» x12))
                                           (fun (x13 : T) =>
                                             «bindO»
                                               (x9 «one» ([] : List T))
                                               (fun (x14 : T) =>
                                                 let x15 : T := «p2» x14;
                                                 «bindO»
                                                   (x10
                                                     («prod» x13 x15)
                                                     («l2»
                                                       («pr» («cSnd» x13 x15) x15)
                                                       («pr» («cFst» x13 x15) x13)))
                                                   (fun (x16 : T) =>
                                                     if (Const.equal («p2» x16) x15).label ≠ 0 then
                                                       «some»
                                                         («pr»
                                                           («comp»
                                                             («listRec» x13 («p1» x14) («p1» x16))
                                                             («p1» x12))
                                                           x15)
                                                     else
                                                       «none»))))
                                   else
                                     if («and»
                                       (Const.eq x2 (leaf 10))
                                       (Const.eq x8 (leaf 2))).label ≠ 0 then
                                       let x12 : T := «at» x6 (leaf 0);
                                       if («mIsTy» x0 x1 x12).label ≠ 0 then
                                         «bindO»
                                           (x10 x4 x5)
                                           (fun (x13 : T) =>
                                             «bindO»
                                               («roseLabel» («p2» x13))
                                               (fun (x14 : T) =>
                                                 let x15 : T := «prod» x14 («list» x12);
                                                 «bindO»
                                                   (x9 x15 («single» («pr» («idt» x15) x15)))
                                                   (fun (x16 : T) =>
                                                     if (Const.equal («p2» x16) x12).label ≠ 0 then
                                                       «some»
                                                         («pr»
                                                           («comp»
                                                             («roseFold» («p2» x13) («p1» x16))
                                                             («p1» x13))
                                                           x12)
                                                     else
                                                       «none»)))
                                       else
                                         «none»
                                     else
                                       if («and»
                                         (Const.eq x2 (leaf 12))
                                         (Const.eq x8 (leaf 2))).label ≠ 0 then
                                         «bindO»
                                           (x9 x4 x5)
                                           (fun (x12 : T) =>
                                             «bindO»
                                               (x10 x4 x5)
                                               (fun (x13 : T) =>
                                                 if (Const.equal
                                                   («p2» x12)
                                                   («p2» x13)).label ≠ 0 then
                                                   «some»
                                                     («pr»
                                                       («comp»
                                                         («chi» («diag» («p2» x12)))
                                                         («cPair» («p1» x12) («p1» x13)))
                                                       «omega»)
                                                 else
                                                   «none»))
                                       else
                                         if (Const.eq x2 (leaf 11)).label ≠ 0 then
                                           let x12 : List T := Const.children («at» x6 (leaf 1));
                                           «bindO»
                                             («bindO»
                                               («nth» («gDefs» x0) («at» x6 (leaf 0)))
                                               «defLanguage»)
                                             (fun (x13 : T) =>
                                               «bindO»
                                                 («allSomeT» («cpAll» x7 x4 x5))
                                                 (fun (x14 : T) =>
                                                   let x15 : List T := Const.children x14;
                                                   if («and»
                                                     (Const.eq («length» x12) («ldArity» x13))
                                                     («and»
                                                       («allT» («mIsTy» x0 x1) x12)
                                                       («equalTs»
                                                         («mapT» «p2» x15)
                                                         («mapT»
                                                           («phSubst» x12)
                                                           («ldParams» x13))))).label ≠ 0 then
                                                     «some»
                                                       («pr»
                                                         («comp»
                                                           («phOp»
                                                             (Const.add
                                                               («gBase» x0)
                                                               («at» x6 (leaf 0)))
                                                             x12)
                                                           («tuple» x4 («mapT» «p1» x15)))
                                                         («phSubst» x12 («ldType» x13)))
                                                   else
                                                     «none»))
                                         else
                                           «none»);
    x6

def «compile» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T →
      List T →
        T := (Const.fold
      (α := T × (T → List T → T))
      (fun (x3 : T) (x4 : List (T × (T → List T → T))) =>
        (Const.node x3 («cpTrees» x4),
          fun (x5 : T) (x6 : List T) => «compileStep» x0 x1 x3 x4 x5 x6))
      x2).2;
    x3

def «ldCompile» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «bindO»
      («compile»
        x0
        («ldArity» x1)
        («ldBody» x1)
        («ctxObj» («ldParams» x1))
        («stdEnv» («ldParams» x1)))
      (fun (x2 : T) =>
        if («and»
          («allT» («mIsTy» x0 («ldArity» x1)) («ldParams» x1))
          (Const.equal («p2» x2) («ldType» x1))).label ≠ 0 then
          «some»
            («pdefn»
              (Const.node (leaf 0) («replicate» («ldArity» x1) (leaf 0)))
              (leaf 1)
              («p1» x2))
        else
          «none»);
    x2

def «defCompile» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «ldCompile» x0 x3
                   else
                     let x3 : T := Const.child x2 (leaf 0);
                     let x4 : T := Const.child x2 (leaf 1);
                     «some»
                       («pdefn»
                         (Const.node (leaf 0) («replicate» x3 (leaf 0)))
                         (leaf 0)
                         x4));
    x2

def «compileDefs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : List T := «gDefs» x0;
                   «allSomeT»
                     («mapT»
                       (fun (x2 : T) =>
                         «defCompile»
                           («globals»
                             (Const.node (leaf 0) («gPrims» x0))
                             (Const.node (leaf 0) («take» x2 x1))
                             («gBase» x0))
                           («at» x1 x2))
                       («range» («length» x1))));
    x1

def «compileEq» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := «bindO»
      («compile» x0 x1 x3 («ctxObj» x2) («stdEnv» x2))
      (fun (x5 : T) =>
        «bindO»
          («compile» x0 x1 x4 («ctxObj» x2) («stdEnv» x2))
          (fun (x6 : T) =>
            if («and»
              («allT» («mIsTy» x0 x1) x2)
              (Const.equal («p2» x5) («p2» x6))).label ≠ 0 then
              «some»
                («mkSeq»
                  («replicate» x1 (leaf 0))
                  ([] : List T)
                  («eqn» («p1» x5) («p1» x6)))
            else
              «none»));
    x5

def «primWf» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «prArity» x2;
                   «and»
                     («scoped» x3 («prArrow» x2))
                     («and»
                       («mIsTy» x0 x3 («prDom» x2))
                       («and»
                         («mIsTy» x0 x3 («prCod» x2))
                         (Const.equal
                           («sortOf» x1 («replicate» x3 (leaf 0)) («prArrow» x2))
                           («some» (leaf 1))))));
    x3

def «primOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «and»
      («primWf» x0 («envSg» x1) x2)
      (let x3 : T →
         T := («infers»
         x1
         («replicate» («prArity» x2) (leaf 0))
         ([] : List T)
         «inferFuel»).2;
       let x4 : T := x3 («prArrow» x2);
       let x5 : T := x3 («prDom» x2);
       let x6 : T := x3 («prCod» x2);
       if («and»
         («isSome» x4)
         («and» («isSome» x5) («isSome» x6))).label ≠ 0 then
         let x7 : T := «get» x4;
         let x8 : T := «get» x5;
         let x9 : T := «get» x6;
         «and»
           (Const.eq («annSort» x7) (leaf 1))
           («and»
             (Const.eq («annSort» x8) (leaf 0))
             («and»
               (Const.eq («annSort» x9) (leaf 0))
               («and»
                 (Const.equal («annLo» x7) («annLo» x8))
                 (Const.equal («annHi» x7) («annLo» x9)))))
       else
         leaf 0);
    x3

def «objOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «and»
      (Const.equal
        («sortOf» («envSg» x0) («replicate» x1 (leaf 0)) x2)
        («some» (leaf 0)))
      («isSome»
        ((«infers» x0 («replicate» x1 (leaf 0)) ([] : List T) «inferFuel»).2
          x2));
    x3

def «copairIn» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «comp»
      («ev» x0 x3)
      («cPair»
        («comp»
          («copair»
            («curry» x1 x0 («comp» x4 («cPair» («cSnd» x1 x0) («cFst» x1 x0))))
            («curry» x2 x0 («comp» x5 («cPair» («cSnd» x2 x0) («cFst» x2 x0)))))
          («cSnd» x0 («coprod» x1 x2)))
        («cFst» x0 («coprod» x1 x2)));
    x6

def «caseArr» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «prod» («exp» x0 x2) («exp» x1 x2);
                   «curry»
                     x3
                     («coprod» x0 x1)
                     («copairIn»
                       x3
                       x0
                       x1
                       x2
                       («comp»
                         («ev» x0 x2)
                         («cPair»
                           («comp» («cFst» («exp» x0 x2) («exp» x1 x2)) («cFst» x3 x0))
                           («cSnd» x3 x0)))
                       («comp»
                         («ev» x1 x2)
                         («cPair»
                           («comp» («cSnd» («exp» x0 x2) («exp» x1 x2)) («cFst» x3 x1))
                           («cSnd» x3 x1)))));
    x3

def «zeroPrim» := «primitive» (leaf 0) «zeroN» «one» «nat»

def «succPrim» := «primitive» (leaf 0) «succ» «nat» «nat»

def «nilPrim» :=
  «primitive»
    (leaf 1)
    («cNil» («x» (leaf 0)))
    «one»
    («list» («x» (leaf 0)))

def «consPrim» :=
  «primitive»
    (leaf 1)
    («cCons» («x» (leaf 0)))
    («prod» («x» (leaf 0)) («list» («x» (leaf 0))))
    («list» («x» (leaf 0)))

def «nodePrim» :=
  «primitive» (leaf 0) «cNode» («prod» «nat» («list» «rose»)) «rose»

def «lnodePrim» :=
  «primitive»
    (leaf 1)
    («lnode» («x» (leaf 0)))
    («prod» («x» (leaf 0)) («list» («lrose» («x» (leaf 0)))))
    («lrose» («x» (leaf 0)))

def «inlPrim» :=
  «primitive»
    (leaf 2)
    («inl» («x» (leaf 0)) («x» (leaf 1)))
    («x» (leaf 0))
    («coprod» («x» (leaf 0)) («x» (leaf 1)))

def «inrPrim» :=
  «primitive»
    (leaf 2)
    («inr» («x» (leaf 0)) («x» (leaf 1)))
    («x» (leaf 1))
    («coprod» («x» (leaf 0)) («x» (leaf 1)))

def «casePrim» :=
  «primitive»
    (leaf 3)
    («caseArr» («x» (leaf 0)) («x» (leaf 1)) («x» (leaf 2)))
    («prod»
      («exp» («x» (leaf 0)) («x» (leaf 2)))
      («exp» («x» (leaf 1)) («x» (leaf 2))))
    («exp» («coprod» («x» (leaf 0)) («x» (leaf 1))) («x» (leaf 2)))

def «primIs» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := Const.equal («nth» («gPrims» x0) x1) («some» x2); x3

def «objVars» :=
  fun (x0 : T) => let x1 : List T := «mapT» «x» («range» x0); x1

def «isCoeqProj» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «prArrow» x0;
                   if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     let x3 : T := Const.child x1 (leaf 1);
                     if («and»
                       (Const.eq (Const.arity x2) (leaf 2))
                       (Const.eq (Const.arity x3) (leaf 2))).label ≠ 0 then
                       «and»
                         (Const.equal x1 («coeqProj» x2 x3))
                         («and»
                           (Const.equal
                             x2
                             («comp» (Const.child x2 (leaf 0)) (Const.child x2 (leaf 1))))
                           (Const.equal
                             x3
                             («comp» (Const.child x3 (leaf 0)) (Const.child x3 (leaf 1)))))
                     else
                       leaf 0
                   else
                     leaf 0);
    x1

def «relL» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «comp» («cFst» x0 x0) («truthIncl» x1); x2

def «relR» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «comp» («cSnd» x0 x0) («truthIncl» x1); x2

def «primRel» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «prArrow» x0;
                   if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
                       let x3 : T := Const.child x2 (leaf 1);
                       if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                         let x4 : T := Const.child x3 (leaf 0);
                         if (Const.equal
                           x1
                           («coeqProj»
                             («relL» («prDom» x0) x4)
                             («relR» («prDom» x0) x4))).label ≠ 0 then
                           «some» x4
                         else
                           «none»
                       else
                         «none»
                     else
                       «none»
                   else
                     «none»);
    x1

def «instVar» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      x0
    else
      «mVar» (Const.sub x1 (leaf 1)));
    x2

def «atVar0» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      x0
    else
      «mVar» x1);
    x2

def «natSuccAt» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «subst»
      x1
      («atVar0» («mArr» x0 ([] : List T) («mVar» (leaf 0))));
    x2

def «listConsAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «subst»
      x2
      (fun (x3 : T) =>
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          «mArr» x0 («single» x1) («mPair» («mVar» (leaf 1)) («mVar» (leaf 0)))
        else
          «mVar» (Const.add x3 (leaf 1)));
    x3

def «roseNodeAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «subst»
      x3
      («instVar»
        («mArr»
          x0
          (if (Const.equal x1 «rose»).label ≠ 0 then
            ([] : List T)
          else
            «single» x2)
          («mPair» («mVar» (leaf 1)) («mVar» (leaf 0)))));
    x4

def «weakenElem» :=
  fun (x0 : T) =>
    let x1 : T := «rename»
      x0
      (fun (x1 : T) =>
        if (Const.eq x1 (leaf 0)).label ≠ 0 then
          leaf 0
        else
          Const.add x1 (leaf 1));
    x1

def «weaken1» :=
  fun (x0 : T) =>
    let x1 : T := «rename» x0 (fun (x1 : T) => Const.add x1 (leaf 1)); x1

def «weaken2» :=
  fun (x0 : T) =>
    let x1 : T := «rename» x0 (fun (x1 : T) => Const.add x1 (leaf 2)); x1

def «lower1» :=
  fun (x0 : T) =>
    let x1 : T := «rename» x0 (fun (x1 : T) => Const.sub x1 (leaf 1)); x1

def «roseMapAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «mListRec»
      («mArr» x0 («single» x2) «mStar»)
      («mArr» x1 («single» x2) («mPair» («weaken1» x3) («mVar» (leaf 0))))
      («mVar» (leaf 0));
    x4

def «roseHyp» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mEq»
      («roseMapAt» x0 x1 «omega» x2)
      («roseMapAt» x0 x1 «omega» («mEq» «mStar» «mStar»));
    x3

def «eqParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («mIs» (leaf 12) (leaf 2) x0).label ≠ 0 then
      «some» («pr» («mArg» x0 (leaf 0)) («mArg» x0 (leaf 1)))
    else
      «none»);
    x1

def «instTerm» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «subst» («osubst» x0 x2) («substList» x1); x3

def «mTypeIn» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := «mapO»
      «p2»
      («compile» x0 x1 x3 («ctxObj» x2) («stdEnv» x2));
    x4

def «isFormula» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := Const.equal («mTypeIn» x0 x1 x2 x3) («some» «omega»); x4

def «lowerHyps» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «allSomeT»
      («mapT»
        (fun (x4 : T) =>
          let x5 : T := «lower1» x4;
          if («and»
            (Const.equal («weaken1» x5) x4)
            («isFormula» x0 x1 x2 x5)).label ≠ 0 then
            «some» x5
          else
            «none»)
        x3);
    x4

def «mkThm» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «thArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «thCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x3);
    x1

def «thHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x4);
    x1

def «thConcl» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «instOk» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := «and»
      (Const.eq («length» x4) («thArity» x3))
      («and»
        («allT» («mIsTy» x0 x1) x4)
        («and»
          (Const.eq («length» x5) («length» («thCtx» x3)))
          («allT»
            (fun (x6 : T) =>
              Const.equal
                («mTypeIn» x0 x1 x2 («at» x5 x6))
                («some» («phSubst» x4 («at» («thCtx» x3) x6))))
            («range» («length» x5)))));
    x6

def «truthSub» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := «comp» x2 («p2» x3);
        «pr» («truthEq» x4) («comp» («p2» x3) («truthIncl» x4)))
      («pr» x0 («idt» x0))
      («reverse» x1);
    x2

def «thmArrow» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «getD»
      («mapO»
        «p1»
        («compile»
          x0
          («thArity» x1)
          x2
          («ctxObj» («thCtx» x1))
          («stdEnv» («thCtx» x1))))
      («idt» («ctxObj» («thCtx» x1)));
    x3

def «thmSide» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if («isEmpty» («thHyps» x1)).label ≠ 0 then
      x2
    else
      «comp»
        x2
        («p2»
          («truthSub»
            («ctxObj» («thCtx» x1))
            («mapT» («thmArrow» x0 x1) («thHyps» x1)))));
    x3

def «thmSeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «eqParts» («thConcl» x1);
                   «mkSeq»
                     («replicate» («thArity» x1) (leaf 0))
                     ([] : List T)
                     (if («isSome» x2).label ≠ 0 then
                       «eqn»
                         («thmSide» x0 x1 («thmArrow» x0 x1 («p1» («get» x2))))
                         («thmSide» x0 x1 («thmArrow» x0 x1 («p2» («get» x2))))
                     else
                       «eqn»
                         («thmSide» x0 x1 («thmArrow» x0 x1 («thConcl» x1)))
                         («thmSide» x0 x1 («comp» «tru» («bang» («ctxObj» («thCtx» x1)))))));
    x2

def «entLang» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «entComb» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «entryLanguage» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); «some» x2
                   else
                     let _ : T := Const.child x1 (leaf 0); «none»);
    x1

def «entrySeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «thmSeq» x0 x3
                   else
                     let x3 : T := Const.child x2 (leaf 0); x3);
    x2

def «anyDefs» :=
  fun (x0 : T) (x1 : List T → T) =>
    let x2 : T := (let x2 : T := «compileDefs» x0;
                   if («isSome» x2).label ≠ 0 then
                     x1 (Const.children («get» x2))
                   else
                     leaf 0);
    x2

def «certifies» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := «anyDefs»
      x0
      (fun (x4 : List T) =>
        if (Const.eq («gBase» x0) («length» «sig»)).label ≠ 0 then
          Const.equal
            («pcheck»
              («ext» x4)
              («mapT» («entrySeq» x0) x1)
              x2
              («seqCtx» x3)
              («seqHyps» x3))
            («some» («seqConcl» x3))
        else
          leaf 0);
    x4

def «ctxPair» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := «pr» (Const.node (leaf 0) x0) (Const.node (leaf 0) x1);
    x2

def «childCtxs» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) (x4 : List T) =>
    let x5 : T := (let x5 : T := Const.label x2;
                   let x6 : List T := «mArgs» x2;
                   let x7 : T := «length» x6;
                   if («and»
                     (Const.eq x5 (leaf 5))
                     (Const.eq x7 (leaf 1))).label ≠ 0 then
                     «some»
                       (Const.node
                         (leaf 0)
                         («single»
                           («ctxPair» ((«mD» x2 (leaf 0)) :: x3) («mapT» «weaken1» x4))))
                   else
                     if («and»
                       (Const.eq x5 (leaf 8))
                       (Const.eq x7 (leaf 3))).label ≠ 0 then
                       «bindO»
                         («mTypeIn» x0 x1 ([] : List T) («at» x6 (leaf 0)))
                         (fun (x8 : T) =>
                           «some»
                             (Const.node
                               (leaf 0)
                               («l3»
                                 («ctxPair» ([] : List T) ([] : List T))
                                 («ctxPair» («single» x8) ([] : List T))
                                 («ctxPair» x3 x4))))
                     else
                       if («and»
                         (Const.eq x5 (leaf 9))
                         (Const.eq x7 (leaf 3))).label ≠ 0 then
                         «bindO»
                           («mTypeIn» x0 x1 ([] : List T) («at» x6 (leaf 0)))
                           (fun (x8 : T) =>
                             «bindO»
                               («bindO» («mTypeIn» x0 x1 x3 («at» x6 (leaf 2))) «listPart»)
                               (fun (x9 : T) =>
                                 «some»
                                   (Const.node
                                     (leaf 0)
                                     («l3»
                                       («ctxPair» ([] : List T) ([] : List T))
                                       («ctxPair» («l2» x8 x9) ([] : List T))
                                       («ctxPair» x3 x4)))))
                       else
                         if («and»
                           (Const.eq x5 (leaf 10))
                           (Const.eq x7 (leaf 2))).label ≠ 0 then
                           «bindO»
                             («bindO» («mTypeIn» x0 x1 x3 («at» x6 (leaf 1))) «roseLabel»)
                             (fun (x8 : T) =>
                               «some»
                                 (Const.node
                                   (leaf 0)
                                   («l2»
                                     («ctxPair»
                                       («single» («prod» x8 («list» («mD» x2 (leaf 0)))))
                                       ([] : List T))
                                     («ctxPair» x3 x4))))
                         else
                           «some»
                             (Const.node (leaf 0) («mapT» (fun (_ : T) => «ctxPair» x3 x4) x6)));
    x5

def «sameCtx» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x0 (leaf 5)).label ≠ 0 then
      leaf 0
    else
      if («or» (Const.eq x0 (leaf 8)) (Const.eq x0 (leaf 9))).label ≠ 0 then
        Const.eq x1 (leaf 2)
      else
        if (Const.eq x0 (leaf 10)).label ≠ 0 then
          Const.eq x1 (leaf 1)
        else
          leaf 1);
    x2

def «congCtxs» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := (if («allT»
      (fun (x6 : T) =>
        «or»
          («sameCtx» (Const.label x2) x6)
          (Const.eq (Const.label («at» x5 x6)) (leaf 0)))
      («range» («length» x5))).label ≠ 0 then
      «some»
        (Const.node
          (leaf 0)
          («mapT» (fun (_ : T) => «ctxPair» x3 x4) («mArgs» x2)))
    else
      «childCtxs» x0 x1 x2 x3 x4);
    x6

def «rootBeta» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «mArg» x0 (leaf 0);
                   if («and»
                     («mIs» (leaf 6) (leaf 2) x0)
                     («mIs» (leaf 5) (leaf 1) x1)).label ≠ 0 then
                     «some» («subst» («mArg» x1 (leaf 0)) («instVar» («mArg» x0 (leaf 1))))
                   else
                     «none»);
    x1

def «rootFst» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «mArg» x0 (leaf 0);
                   if («and»
                     («mIs» (leaf 3) (leaf 1) x0)
                     («mIs» (leaf 2) (leaf 2) x1)).label ≠ 0 then
                     «some» («mArg» x1 (leaf 0))
                   else
                     «none»);
    x1

def «rootSnd» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «mArg» x0 (leaf 0);
                   if («and»
                     («mIs» (leaf 4) (leaf 1) x0)
                     («mIs» (leaf 2) (leaf 2) x1)).label ≠ 0 then
                     «some» («mArg» x1 (leaf 1))
                   else
                     «none»);
    x1

def «rootPairEta» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «mArg» x0 (leaf 0);
                   let x2 : T := «mArg» x0 (leaf 1);
                   if («and»
                     («mIs» (leaf 2) (leaf 2) x0)
                     («and»
                       («mIs» (leaf 3) (leaf 1) x1)
                       («mIs» (leaf 4) (leaf 1) x2))).label ≠ 0 then
                     if (Const.equal
                       («mArg» x1 (leaf 0))
                       («mArg» x2 (leaf 0))).label ≠ 0 then
                       «some» («mArg» x1 (leaf 0))
                     else
                       «none»
                   else
                     «none»);
    x1

def «rootUnitEta» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (if (Const.equal
      («mTypeIn» x0 x1 x2 x3)
      («some» «one»)).label ≠ 0 then
      «some» «mStar»
    else
      «none»);
    x4

def «rootDelta» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.label x1) (leaf 11)).label ≠ 0 then
      «mapO»
        (fun (x2 : T) =>
          «subst»
            («osubst» (Const.children («mD» x1 (leaf 1))) («ldBody» x2))
            («substList» («mArgs» x1)))
        («bindO» («nth» («gDefs» x0) («mD» x1 (leaf 0))) «defLanguage»)
    else
      «none»);
    x2

def «rootNat» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «mArg» x3 (leaf 0);
                   let x5 : T := «mArg» x3 (leaf 1);
                   let x6 : T := «mArg» x3 (leaf 2);
                   if («and»
                     («mIs» (leaf 8) (leaf 3) x3)
                     («and»
                       («mIs» (leaf 7) (leaf 1) x6)
                       (Const.eq (Const.arity («mD» x6 (leaf 1))) (leaf 0)))).label ≠ 0 then
                     let x7 : T := «at» x2 (leaf 0);
                     if (Const.eq x1 (leaf 9)).label ≠ 0 then
                       if («and»
                         (Const.eq («mD» x6 (leaf 0)) x7)
                         («and»
                           («primIs» x0 x7 «zeroPrim»)
                           (Const.equal («mArg» x6 (leaf 0)) «mStar»))).label ≠ 0 then
                         «some» x4
                       else
                         «none»
                     else
                       if («and»
                         (Const.eq («mD» x6 (leaf 0)) x7)
                         («primIs» x0 x7 «succPrim»)).label ≠ 0 then
                         «some» («subst» x5 («instVar» («mNatRec» x4 x5 («mArg» x6 (leaf 0)))))
                       else
                         «none»
                   else
                     «none»);
    x4

def «rootListNil» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «mArg» x2 (leaf 2);
                   if («and»
                     («mIs» (leaf 9) (leaf 3) x2)
                     («and»
                       («mIs» (leaf 7) (leaf 1) x3)
                       (Const.eq (Const.arity («mD» x3 (leaf 1))) (leaf 1)))).label ≠ 0 then
                     let x4 : T := «at» x1 (leaf 0);
                     if («and»
                       (Const.eq («mD» x3 (leaf 0)) x4)
                       («and»
                         («primIs» x0 x4 «nilPrim»)
                         (Const.equal («mArg» x3 (leaf 0)) «mStar»))).label ≠ 0 then
                       «some» («mArg» x2 (leaf 0))
                     else
                       «none»
                   else
                     «none»);
    x3

def «rootListCons» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «mArg» x2 (leaf 2);
                   if («and»
                     («mIs» (leaf 9) (leaf 3) x2)
                     («and»
                       («mIs» (leaf 7) (leaf 1) x3)
                       (Const.eq (Const.arity («mD» x3 (leaf 1))) (leaf 1)))).label ≠ 0 then
                     let x4 : T := «mArg» x3 (leaf 0);
                     let x5 : T := «at» x1 (leaf 0);
                     if («and»
                       («mIs» (leaf 2) (leaf 2) x4)
                       («and»
                         (Const.eq («mD» x3 (leaf 0)) x5)
                         («primIs» x0 x5 «consPrim»))).label ≠ 0 then
                       «some»
                         («subst»
                           («mArg» x2 (leaf 1))
                           («substList»
                             («l2»
                               («mListRec»
                                 («mArg» x2 (leaf 0))
                                 («mArg» x2 (leaf 1))
                                 («mArg» x4 (leaf 1)))
                               («mArg» x4 (leaf 0)))))
                     else
                       «none»
                   else
                     «none»);
    x3

def «rootRoseNode» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «mArg» x2 (leaf 0);
                   let x4 : T := «mArg» x2 (leaf 1);
                   if («and»
                     («mIs» (leaf 10) (leaf 2) x2)
                     («mIs» (leaf 7) (leaf 1) x4)).label ≠ 0 then
                     let x5 : T := «mArg» x4 (leaf 0);
                     let x6 : T := «at» x1 (leaf 0);
                     let x7 : T := «at» x1 (leaf 1);
                     let x8 : T := «at» x1 (leaf 2);
                     let x9 : T := «mD» x2 (leaf 0);
                     if («and»
                       («mIs» (leaf 2) (leaf 2) x5)
                       («and»
                         (Const.eq («mD» x4 (leaf 0)) x6)
                         («and»
                           («or» («primIs» x0 x6 «nodePrim») («primIs» x0 x6 «lnodePrim»))
                           («and»
                             («primIs» x0 x7 «nilPrim»)
                             («primIs» x0 x8 «consPrim»))))).label ≠ 0 then
                       «some»
                         («subst»
                           x3
                           («instVar»
                             («mPair»
                               («mArg» x5 (leaf 0))
                               («mListRec»
                                 («mArr» x7 («single» x9) «mStar»)
                                 («mArr»
                                   x8
                                   («single» x9)
                                   («mPair» («mRoseRec» x9 x3 («mVar» (leaf 1))) («mVar» (leaf 0))))
                                 («mArg» x5 (leaf 1))))))
                     else
                       «none»
                   else
                     «none»);
    x3

def «rootCase» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : T := (let x5 : T := «mArg» x4 (leaf 0);
                   let x6 : T := «mArg» x4 (leaf 1);
                   if («and»
                     («mIs» (leaf 6) (leaf 2) x4)
                     («and»
                       («mIs» (leaf 7) (leaf 1) x5)
                       («mIs» (leaf 7) (leaf 1) x6))).label ≠ 0 then
                     let x7 : T := «mArg» x5 (leaf 0);
                     let x8 : T := «at» x3 (leaf 0);
                     let x9 : T := «at» x3 (leaf 1);
                     if («and»
                       («mIs» (leaf 2) (leaf 2) x7)
                       («and»
                         (Const.eq («mD» x5 (leaf 0)) x8)
                         («and»
                           (Const.eq («mD» x6 (leaf 0)) x9)
                           («and»
                             («primIs» x0 x8 «casePrim»)
                             («primIs» x0 x9 x1))))).label ≠ 0 then
                       «some» («mApp» («mArg» x7 x2) («mArg» x6 (leaf 0)))
                     else
                       «none»
                   else
                     «none»);
    x5

def «rootThm» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (let x6 : List T := Const.children («at» x4 (leaf 1));
                   let x7 : List T := Const.children («at» x4 (leaf 2));
                   let x8 : T := «at» x4 (leaf 3);
                   «bindO»
                     («bindO» («nth» x1 («at» x4 (leaf 0))) «entryLanguage»)
                     (fun (x9 : T) =>
                       «bindO»
                         (if («isEmpty» («thHyps» x9)).label ≠ 0 then
                           «eqParts» («thConcl» x9)
                         else
                           «none»)
                         (fun (x10 : T) =>
                           if («and»
                             («instOk» x0 x2 x3 x9 x6 x7)
                             (Const.equal
                               x5
                               («instTerm»
                                 x6
                                 x7
                                 (if (x8).label ≠ 0 then «p2» x10 else «p1» x10)))).label ≠ 0 then
                             «some»
                               («instTerm» x6 x7 (if (x8).label ≠ 0 then «p1» x10 else «p2» x10))
                           else
                             «none»)));
    x6

def «rootHyp» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «at» x1 (leaf 1);
                   «bindO»
                     («bindO» («nth» x0 («at» x1 (leaf 0))) «eqParts»)
                     (fun (x4 : T) =>
                       if (Const.equal
                         x2
                         (if (x3).label ≠ 0 then «p2» x4 else «p1» x4)).label ≠ 0 then
                         «some» (if (x3).label ≠ 0 then «p1» x4 else «p2» x4)
                       else
                         «none»));
    x3

def «rootStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T) =>
    let x8 : T := (if (Const.eq x5 (leaf 3)).label ≠ 0 then
      «rootBeta» x7
    else
      if (Const.eq x5 (leaf 4)).label ≠ 0 then
        «rootFst» x7
      else
        if (Const.eq x5 (leaf 5)).label ≠ 0 then
          «rootSnd» x7
        else
          if (Const.eq x5 (leaf 6)).label ≠ 0 then
            «rootPairEta» x7
          else
            if (Const.eq x5 (leaf 7)).label ≠ 0 then
              «rootUnitEta» x0 x2 x3 x7
            else
              if (Const.eq x5 (leaf 8)).label ≠ 0 then
                «rootDelta» x0 x7
              else
                if («or»
                  (Const.eq x5 (leaf 9))
                  (Const.eq x5 (leaf 10))).label ≠ 0 then
                  «rootNat» x0 x5 x6 x7
                else
                  if (Const.eq x5 (leaf 11)).label ≠ 0 then
                    «rootListNil» x0 x6 x7
                  else
                    if (Const.eq x5 (leaf 12)).label ≠ 0 then
                      «rootListCons» x0 x6 x7
                    else
                      if (Const.eq x5 (leaf 13)).label ≠ 0 then
                        «rootRoseNode» x0 x6 x7
                      else
                        if (Const.eq x5 (leaf 14)).label ≠ 0 then
                          «rootCase» x0 «inlPrim» (leaf 0) x6 x7
                        else
                          if (Const.eq x5 (leaf 15)).label ≠ 0 then
                            «rootCase» x0 «inrPrim» (leaf 1) x6 x7
                          else
                            if (Const.eq x5 (leaf 16)).label ≠ 0 then
                              «rootThm» x0 x1 x2 x3 x6 x7
                            else
                              if (Const.eq x5 (leaf 17)).label ≠ 0 then
                                «rootHyp» x4 x6 x7
                              else
                                «none»);
    x8

def «dpTrees» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
    let x1 : List
      T := Const.foldr
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := List T)
      (fun (x1 : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (x2 : List T) =>
        ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «dpTail» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
    let x1 : List
      (T ×
        ((List T → List T → T → T) ×
          (List T →
            List T →
              T →
                T))) := Const.lcase
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := List
        (T × ((List T → List T → T → T) × (List T → List T → T → T))))
      x0
      ([] : List (T ×
        ((List T → List T → T → T) × (List T → List T → T → T))))
      (fun (_ : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (x2 : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        x2);
    x1

def «dpAt» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : (List T → List T → T → T) ×
      (List T →
        List T →
          T →
            T) := Const.lcase
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := (List T → List T → T → T) × (List T → List T → T → T))
      (Const.iter
        (α := List
          (T × ((List T → List T → T → T) × (List T → List T → T → T))))
        «dpTail»
        x0
        x1)
      (fun (_ : List T) (_ : List T) (_ : T) => «none»,
        fun (_ : List T) (_ : List T) (_ : T) => leaf 0)
      (fun (x2 : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (_ : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        (x2).2);
    x2

def «rw» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : List T → List T → T → T := («dpAt» x0 x1).1; x2

def «pf» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : List T → List T → T → T := («dpAt» x0 x1).2; x2

def «rewriteStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x7 : List T)
    (x8 : List T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «length» x5;
                    if («and»
                      (Const.eq x3 (leaf 0))
                      (Const.eq x10 (leaf 0))).label ≠ 0 then
                      «some» x9
                    else
                      if («and»
                        (Const.eq x3 (leaf 1))
                        (Const.eq x10 (leaf 2))).label ≠ 0 then
                        «bindO» («rw» x6 (leaf 0) x7 x8 x9) («rw» x6 (leaf 1) x7 x8)
                      else
                        if (Const.eq x3 (leaf 2)).label ≠ 0 then
                          «bindO»
                            («congCtxs» x0 x2 x9 x7 x8 x5)
                            (fun (x11 : T) =>
                              let x12 : List T := Const.children x11;
                              let x13 : List T := «mArgs» x9;
                              if («and»
                                (Const.eq x10 («length» x13))
                                (Const.eq («length» x12) («length» x13))).label ≠ 0 then
                                «mapO»
                                  (fun (x14 : T) =>
                                    Const.node
                                      (Const.label x9)
                                      ((Const.child x9 (leaf 0)) :: (Const.children x14)))
                                  («allSomeT»
                                    («mapT»
                                      (fun (x14 : T) =>
                                        let x15 : T := «at» x12 x14;
                                        «rw»
                                          x6
                                          x14
                                          (Const.children («p1» x15))
                                          (Const.children («p2» x15))
                                          («at» x13 x14))
                                      («range» x10)))
                              else
                                «none»)
                        else
                          if (Const.eq x10 (leaf 0)).label ≠ 0 then
                            «rootStep» x0 x1 x2 x7 x8 x3 x4 x9
                          else
                            «none»);
    x10

def «rosePrimsOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «and»
      («or»
        («and» («primIs» x0 x1 «nodePrim») (Const.equal x4 «rose»))
        («and» («primIs» x0 x1 «lnodePrim») (Const.equal x4 («lrose» x5))))
      («and» («primIs» x0 x2 «nilPrim») («primIs» x0 x3 «consPrim»));
    x6

def «proveStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x7 : List T)
    (x8 : List T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «length» x5;
                    let x11 : T := «eqParts» x9;
                    let x12 : T := «p1» («get» x11);
                    let x13 : T := «p2» («get» x11);
                    let x14 : T := «at» x4 (leaf 0);
                    let x15 : T := «at» x4 (leaf 1);
                    if («and»
                      (Const.eq x3 (leaf 18))
                      (Const.eq x10 (leaf 2))).label ≠ 0 then
                      if («isSome» x11).label ≠ 0 then
                        let x16 : T := «rw» x6 (leaf 0) x7 x8 x12;
                        let x17 : T := «rw» x6 (leaf 1) x7 x8 x13;
                        «and»
                          («isSome» x16)
                          («and» («isSome» x17) (Const.equal («get» x16) («get» x17)))
                      else
                        leaf 0
                    else
                      if («and»
                        (Const.eq x3 (leaf 19))
                        (Const.eq x10 (leaf 3))).label ≠ 0 then
                        if («and» («isSome» x11) («not» («isEmpty» x7))).label ≠ 0 then
                          let x16 : T := «at» x7 (leaf 0);
                          let x17 : List T := «tail» x7;
                          let x18 : T := «at» x4 (leaf 2);
                          let x19 : T := «mTypeIn» x0 x2 x7 x12;
                          let x20 : T := «lowerHyps» x0 x2 x17 x8;
                          if («and» («isSome» x19) («isSome» x20)).label ≠ 0 then
                            let x21 : T := «get» x19;
                            let x22 : T := «mArr» x14 ([] : List T) «mStar»;
                            if («and»
                              (Const.equal x16 «nat»)
                              («and»
                                («primIs» x0 x14 «zeroPrim»)
                                («and»
                                  («primIs» x0 x15 «succPrim»)
                                  («and»
                                    (Const.equal («mTypeIn» x0 x2 x7 x13) («some» x21))
                                    (Const.equal
                                      («mTypeIn» x0 x2 (x21 :: x17) x18)
                                      («some» x21)))))).label ≠ 0 then
                              if («pf»
                                x6
                                (leaf 0)
                                x17
                                (Const.children («get» x20))
                                («mEq»
                                  («subst» x12 («instVar» x22))
                                  («subst» x13 («instVar» x22)))).label ≠ 0 then
                                if («pf»
                                  x6
                                  (leaf 1)
                                  x7
                                  x8
                                  («mEq»
                                    («natSuccAt» x15 x12)
                                    («subst» x18 («atVar0» x12)))).label ≠ 0 then
                                  «pf»
                                    x6
                                    (leaf 2)
                                    x7
                                    x8
                                    («mEq» («natSuccAt» x15 x13) («subst» x18 («atVar0» x13)))
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              leaf 0
                          else
                            leaf 0
                        else
                          leaf 0
                      else
                        if («and»
                          (Const.eq x3 (leaf 20))
                          (Const.eq x10 (leaf 3))).label ≠ 0 then
                          if («and» («isSome» x11) («not» («isEmpty» x7))).label ≠ 0 then
                            let x16 : T := «at» x7 (leaf 0);
                            let x17 : List T := «tail» x7;
                            let x18 : T := «at» x4 (leaf 2);
                            let x19 : T := «mTypeIn» x0 x2 x7 x12;
                            let x20 : T := «listPart» x16;
                            let x21 : T := «lowerHyps» x0 x2 x17 x8;
                            if («and»
                              («isSome» x19)
                              («and» («isSome» x20) («isSome» x21))).label ≠ 0 then
                              let x22 : T := «get» x19;
                              let x23 : T := «get» x20;
                              let x24 : List T := (x16 :: (x23 :: x17));
                              let x25 : List T := «mapT» «weaken2» (Const.children («get» x21));
                              let x26 : T := «mArr» x14 («single» x23) «mStar»;
                              if («and»
                                («primIs» x0 x14 «nilPrim»)
                                («and»
                                  («primIs» x0 x15 «consPrim»)
                                  («and»
                                    (Const.equal («mTypeIn» x0 x2 x7 x13) («some» x22))
                                    (Const.equal
                                      («mTypeIn» x0 x2 (x22 :: (x23 :: x17)) x18)
                                      («some» x22))))).label ≠ 0 then
                                if («pf»
                                  x6
                                  (leaf 0)
                                  x17
                                  (Const.children («get» x21))
                                  («mEq»
                                    («subst» x12 («instVar» x26))
                                    («subst» x13 («instVar» x26)))).label ≠ 0 then
                                  if («pf»
                                    x6
                                    (leaf 1)
                                    x24
                                    x25
                                    («mEq»
                                      («listConsAt» x15 x23 x12)
                                      («subst» x18 («atVar0» («weakenElem» x12))))).label ≠ 0 then
                                    «pf»
                                      x6
                                      (leaf 2)
                                      x24
                                      x25
                                      («mEq»
                                        («listConsAt» x15 x23 x13)
                                        («subst» x18 («atVar0» («weakenElem» x13))))
                                  else
                                    leaf 0
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              leaf 0
                          else
                            leaf 0
                        else
                          if («and»
                            (Const.eq x3 (leaf 21))
                            (Const.eq x10 (leaf 0))).label ≠ 0 then
                            Const.equal («nth» x8 x14) («some» x9)
                          else
                            if («and»
                              (Const.eq x3 (leaf 22))
                              (Const.eq x10 (leaf 2))).label ≠ 0 then
                              if («isFormula» x0 x2 x7 x14).label ≠ 0 then
                                if («pf» x6 (leaf 0) x7 x8 x14).label ≠ 0 then
                                  «pf» x6 (leaf 1) x7 («append» x8 («single» x14)) x9
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              if («and»
                                (Const.eq x3 (leaf 23))
                                (Const.eq x10 (leaf 2))).label ≠ 0 then
                                let x16 : T := «rw» x6 (leaf 0) x7 x8 x9;
                                if («isSome» x16).label ≠ 0 then
                                  «pf» x6 (leaf 1) x7 x8 («get» x16)
                                else
                                  leaf 0
                              else
                                if («and»
                                  (Const.eq x3 (leaf 24))
                                  (Const.eq x10 (leaf 2))).label ≠ 0 then
                                  if («and»
                                    («isFormula» x0 x2 x7 x14)
                                    (Const.equal
                                      («rw» x6 (leaf 0) x7 x8 x14)
                                      («some» x9))).label ≠ 0 then
                                    «pf» x6 (leaf 1) x7 x8 x14
                                  else
                                    leaf 0
                                else
                                  if («and»
                                    (Const.eq x3 (leaf 25))
                                    (Const.eq x10 (leaf 2))).label ≠ 0 then
                                    if («isSome» x11).label ≠ 0 then
                                      if («and»
                                        («isFormula» x0 x2 x7 x12)
                                        («isFormula» x0 x2 x7 x13)).label ≠ 0 then
                                        if («pf»
                                          x6
                                          (leaf 0)
                                          x7
                                          («append» x8 («single» x12))
                                          x13).label ≠ 0 then
                                          «pf» x6 (leaf 1) x7 («append» x8 («single» x13)) x12
                                        else
                                          leaf 0
                                      else
                                        leaf 0
                                    else
                                      leaf 0
                                  else
                                    if («and»
                                      (Const.eq x3 (leaf 26))
                                      (Const.eq x10 (leaf 1))).label ≠ 0 then
                                      if («isSome» x11).label ≠ 0 then
                                        let x16 : T := «bindO» («mTypeIn» x0 x2 x7 x12) «expParts»;
                                        if («isSome» x16).label ≠ 0 then
                                          «pf»
                                            x6
                                            (leaf 0)
                                            ((«p1» («get» x16)) :: x7)
                                            («mapT» «weaken1» x8)
                                            («mEq»
                                              («mApp» («weaken1» x12) («mVar» (leaf 0)))
                                              («mApp» («weaken1» x13) («mVar» (leaf 0))))
                                        else
                                          leaf 0
                                      else
                                        leaf 0
                                    else
                                      if (Const.eq x3 (leaf 27)).label ≠ 0 then
                                        let x16 : List T := Const.children x15;
                                        let x17 : List T := Const.children («at» x4 (leaf 2));
                                        let x18 : T := «bindO» («nth» x1 x14) «entryLanguage»;
                                        if («isSome» x18).label ≠ 0 then
                                          let x19 : T := «get» x18;
                                          if («and»
                                            («instOk» x0 x2 x7 x19 x16 x17)
                                            («and»
                                              (Const.equal x9 («instTerm» x16 x17 («thConcl» x19)))
                                              (Const.eq
                                                x10
                                                («length» («thHyps» x19))))).label ≠ 0 then
                                            «allT»
                                              (fun (x20 : T) =>
                                                «pf»
                                                  x6
                                                  x20
                                                  x7
                                                  x8
                                                  («instTerm» x16 x17 («at» («thHyps» x19) x20)))
                                              («range» x10)
                                          else
                                            leaf 0
                                        else
                                          leaf 0
                                      else
                                        if («and»
                                          (Const.eq x3 (leaf 28))
                                          (Const.eq x10 (leaf 2))).label ≠ 0 then
                                          if («not» («isEmpty» x7)).label ≠ 0 then
                                            let x16 : T := «at» x7 (leaf 0);
                                            let x17 : List T := «tail» x7;
                                            let x18 : T := «lowerHyps» x0 x2 x17 x8;
                                            if («isSome» x18).label ≠ 0 then
                                              if («and»
                                                (Const.equal x16 «nat»)
                                                («and»
                                                  («primIs» x0 x14 «zeroPrim»)
                                                  («and»
                                                    («primIs» x0 x15 «succPrim»)
                                                    («isFormula» x0 x2 x7 x9)))).label ≠ 0 then
                                                if («pf»
                                                  x6
                                                  (leaf 0)
                                                  x17
                                                  (Const.children («get» x18))
                                                  («subst»
                                                    x9
                                                    («instVar»
                                                      («mArr»
                                                        x14
                                                        ([] : List T)
                                                        «mStar»)))).label ≠ 0 then
                                                  «pf»
                                                    x6
                                                    (leaf 1)
                                                    x7
                                                    («append» x8 («single» x9))
                                                    («natSuccAt» x15 x9)
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              leaf 0
                                          else
                                            leaf 0
                                        else
                                          if («and»
                                            (Const.eq x3 (leaf 29))
                                            (Const.eq x10 (leaf 2))).label ≠ 0 then
                                            if («not» («isEmpty» x7)).label ≠ 0 then
                                              let x16 : T := «at» x7 (leaf 0);
                                              let x17 : List T := «tail» x7;
                                              let x18 : T := «listPart» x16;
                                              let x19 : T := «lowerHyps» x0 x2 x17 x8;
                                              if («and»
                                                («isSome» x18)
                                                («isSome» x19)).label ≠ 0 then
                                                let x20 : T := «get» x18;
                                                if («and»
                                                  («primIs» x0 x14 «nilPrim»)
                                                  («and»
                                                    («primIs» x0 x15 «consPrim»)
                                                    («isFormula» x0 x2 x7 x9))).label ≠ 0 then
                                                  if («pf»
                                                    x6
                                                    (leaf 0)
                                                    x17
                                                    (Const.children («get» x19))
                                                    («subst»
                                                      x9
                                                      («instVar»
                                                        («mArr»
                                                          x14
                                                          («single» x20)
                                                          «mStar»)))).label ≠ 0 then
                                                    «pf»
                                                      x6
                                                      (leaf 1)
                                                      (x16 :: (x20 :: x17))
                                                      («append»
                                                        («mapT»
                                                          «weaken2»
                                                          (Const.children («get» x19)))
                                                        («single» («weakenElem» x9)))
                                                      («listConsAt» x15 x20 x9)
                                                  else
                                                    leaf 0
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              leaf 0
                                          else
                                            if («and»
                                              (Const.eq x3 (leaf 34))
                                              (Const.eq x10 (leaf 2))).label ≠ 0 then
                                              if («not» («isEmpty» x7)).label ≠ 0 then
                                                let x16 : T := «at» x7 (leaf 0);
                                                let x17 : List T := «tail» x7;
                                                let x18 : T := «coprodParts» x16;
                                                let x19 : T := «lowerHyps» x0 x2 x17 x8;
                                                if («and»
                                                  («isSome» x18)
                                                  («isSome» x19)).label ≠ 0 then
                                                  let x20 : T := «p1» («get» x18);
                                                  let x21 : T := «p2» («get» x18);
                                                  if («and»
                                                    («primIs» x0 x14 «inlPrim»)
                                                    («and»
                                                      («primIs» x0 x15 «inrPrim»)
                                                      («isFormula» x0 x2 x7 x9))).label ≠ 0 then
                                                    if («pf»
                                                      x6
                                                      (leaf 0)
                                                      (x20 :: x17)
                                                      x8
                                                      («subst»
                                                        x9
                                                        («atVar0»
                                                          («mArr»
                                                            x14
                                                            («l2» x20 x21)
                                                            («mVar» (leaf 0)))))).label ≠ 0 then
                                                      «pf»
                                                        x6
                                                        (leaf 1)
                                                        (x21 :: x17)
                                                        x8
                                                        («subst»
                                                          x9
                                                          («atVar0»
                                                            («mArr»
                                                              x15
                                                              («l2» x20 x21)
                                                              («mVar» (leaf 0)))))
                                                    else
                                                      leaf 0
                                                  else
                                                    leaf 0
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              if («and»
                                                (Const.eq x3 (leaf 35))
                                                (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                «and»
                                                  (Const.equal («nth» x7 x14) («some» «cZero»))
                                                  («isFormula» x0 x2 x7 x9)
                                              else
                                                if («and»
                                                  (Const.eq x3 (leaf 36))
                                                  (Const.eq x10 (leaf 1))).label ≠ 0 then
                                                  let x16 : List T := Const.children x15;
                                                  let x17 : T := «nth» («gPrims» x0) x14;
                                                  if («and»
                                                    («not» («isEmpty» x7))
                                                    («isSome» x17)).label ≠ 0 then
                                                    let x18 : T := «at» x7 (leaf 0);
                                                    let x19 : List T := «tail» x7;
                                                    let x20 : T := «get» x17;
                                                    if («and»
                                                      («isCoeqProj» x20)
                                                      («isSome»
                                                        («lowerHyps» x0 x2 x19 x8))).label ≠ 0 then
                                                      if («and»
                                                        (Const.eq («length» x16) («prArity» x20))
                                                        («and»
                                                          («allT» («mIsTy» x0 x2) x16)
                                                          («and»
                                                            (Const.equal
                                                              x18
                                                              («phSubst» x16 («prCod» x20)))
                                                            («isFormula»
                                                              x0
                                                              x2
                                                              x7
                                                              x9)))).label ≠ 0 then
                                                        «pf»
                                                          x6
                                                          (leaf 0)
                                                          ((«phSubst» x16 («prDom» x20)) :: x19)
                                                          x8
                                                          («subst»
                                                            x9
                                                            («atVar0»
                                                              («mArr» x14 x16 («mVar» (leaf 0)))))
                                                      else
                                                        leaf 0
                                                    else
                                                      leaf 0
                                                  else
                                                    leaf 0
                                                else
                                                  if («and»
                                                    (Const.eq x3 (leaf 30))
                                                    (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                    if («isSome» x11).label ≠ 0 then
                                                      let x16 : T := «compileEq» x0 x2 x7 x12 x13;
                                                      if («isSome» x16).label ≠ 0 then
                                                        «certifies» x0 x1 x14 («get» x16)
                                                      else
                                                        leaf 0
                                                    else
                                                      leaf 0
                                                  else
                                                    if («and»
                                                      (Const.eq x3 (leaf 31))
                                                      (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                      if («and»
                                                        («allT» («isFormula» x0 x2 x7) x8)
                                                        («isFormula» x0 x2 x7 x9)).label ≠ 0 then
                                                        «certifies»
                                                          x0
                                                          x1
                                                          x14
                                                          («thmSeq»
                                                            x0
                                                            («mkThm»
                                                              x2
                                                              (Const.node (leaf 0) x7)
                                                              (Const.node (leaf 0) x8)
                                                              x9))
                                                      else
                                                        leaf 0
                                                    else
                                                      if («and»
                                                        (Const.eq x3 (leaf 32))
                                                        (Const.eq x10 (leaf 2))).label ≠ 0 then
                                                        if («and»
                                                          («isSome» x11)
                                                          (Const.eq
                                                            («length» x7)
                                                            (leaf 1))).label ≠ 0 then
                                                          let x16 : T := «at» x7 (leaf 0);
                                                          let x17 : T := «mTypeIn» x0 x2 x7 x12;
                                                          let x18 : T := «roseLabel» x16;
                                                          if («and»
                                                            («isSome» x17)
                                                            («isSome» x18)).label ≠ 0 then
                                                            let x19 : T := «get» x17;
                                                            let x20 : T := «get» x18;
                                                            let x21 : T := «at» x4 (leaf 3);
                                                            let x22 : T := x15;
                                                            let x23 : T := «at» x4 (leaf 2);
                                                            let x24 : List
                                                              T := «l2» («list» x16) x20;
                                                            if («and»
                                                              («rosePrimsOk» x0 x14 x22 x23 x16 x20)
                                                              («and»
                                                                (Const.equal
                                                                  («mTypeIn» x0 x2 x7 x13)
                                                                  («some» x19))
                                                                (Const.equal
                                                                  («mTypeIn»
                                                                    x0
                                                                    x2
                                                                    («l2» («list» x19) x20)
                                                                    x21)
                                                                  («some» x19)))).label ≠ 0 then
                                                              if («pf»
                                                                x6
                                                                (leaf 0)
                                                                x24
                                                                ([] : List T)
                                                                («mEq»
                                                                  («roseNodeAt» x14 x16 x20 x12)
                                                                  («subst»
                                                                    x21
                                                                    («atVar0»
                                                                      («roseMapAt»
                                                                        x22
                                                                        x23
                                                                        x19
                                                                        x12))))).label ≠ 0 then
                                                                «pf»
                                                                  x6
                                                                  (leaf 1)
                                                                  x24
                                                                  ([] : List T)
                                                                  («mEq»
                                                                    («roseNodeAt» x14 x16 x20 x13)
                                                                    («subst»
                                                                      x21
                                                                      («atVar0»
                                                                        («roseMapAt»
                                                                          x22
                                                                          x23
                                                                          x19
                                                                          x13))))
                                                              else
                                                                leaf 0
                                                            else
                                                              leaf 0
                                                          else
                                                            leaf 0
                                                        else
                                                          leaf 0
                                                      else
                                                        if («and»
                                                          (Const.eq x3 (leaf 33))
                                                          (Const.eq x10 (leaf 1))).label ≠ 0 then
                                                          if (Const.eq
                                                            («length» x7)
                                                            (leaf 1)).label ≠ 0 then
                                                            let x16 : T := «at» x7 (leaf 0);
                                                            let x17 : T := «roseLabel» x16;
                                                            if («isSome» x17).label ≠ 0 then
                                                              let x18 : T := «get» x17;
                                                              let x19 : T := «at» x4 (leaf 2);
                                                              if («and»
                                                                («rosePrimsOk»
                                                                  x0
                                                                  x14
                                                                  x15
                                                                  x19
                                                                  x16
                                                                  x18)
                                                                («isFormula»
                                                                  x0
                                                                  x2
                                                                  x7
                                                                  x9)).label ≠ 0 then
                                                                «pf»
                                                                  x6
                                                                  (leaf 0)
                                                                  («l2» («list» x16) x18)
                                                                  («single» («roseHyp» x15 x19 x9))
                                                                  («roseNodeAt» x14 x16 x18 x9)
                                                              else
                                                                leaf 0
                                                            else
                                                              leaf 0
                                                          else
                                                            leaf 0
                                                        else
                                                          leaf 0);
    x10

def «check» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : (List T → List T → T → T) ×
      (List T →
        List T →
          T →
            T) := (Const.fold
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (fun (x4 : T)
         (x5 : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        let x6 : List T := «dpTrees» x5;
        let x7 : List T := Const.children («at» x6 (leaf 0));
        let x8 : List
          (T ×
            ((List T → List T → T → T) ×
              (List T → List T → T → T))) := «dpTail» x5;
        let x9 : List T := «tail» x6;
        (Const.node x4 x6,
          (fun (x10 : List T) (x11 : List T) (x12 : T) =>
            «rewriteStep» x0 x1 x2 x4 x7 x9 x8 x10 x11 x12,
            fun (x10 : List T) (x11 : List T) (x12 : T) =>
              «proveStep» x0 x1 x2 x4 x7 x9 x8 x10 x11 x12)))
      x3).2;
    x4

def «thmChecks» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «thArity» x2;
                   let x5 : List T := «thCtx» x2;
                   if («and»
                     («allT» («mIsTy» x0 x4) x5)
                     («and»
                       («allT» («isFormula» x0 x4 x5) («thHyps» x2))
                       («isFormula» x0 x4 x5 («thConcl» x2)))).label ≠ 0 then
                     («check» x0 x1 x4 x3).2 x5 («thHyps» x2) («thConcl» x2)
                   else
                     leaf 0);
    x4

def «primSeq» :=
  fun (x0 : T) =>
    let x1 : T := «mkSeq»
      («replicate» («prArity» x0) (leaf 0))
      ([] : List T)
      («eqn»
        («comp»
          («idt» («prCod» x0))
          («comp» («prArrow» x0) («idt» («prDom» x0))))
        («prArrow» x0));
    x1

def «primConfirms» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (if («isSome» x3).label ≠ 0 then
      if («anyDefs»
        x0
        (fun (x4 : List T) =>
          «primWf» x0 («thySig» («ext» x4)) x2)).label ≠ 0 then
        «certifies» x0 x1 («get» x3) («primSeq» x2)
      else
        leaf 0
    else
      «anyDefs»
        x0
        (fun (x4 : List T) =>
          if (Const.eq («gBase» x0) («length» «sig»)).label ≠ 0 then
            «primOk» x0 («envOfDefs» x4) x2
          else
            leaf 0));
    x4

def «objConfirms» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (if («isSome» x4).label ≠ 0 then
      if («anyDefs»
        x0
        (fun (x5 : List T) =>
          Const.equal
            («sortOf» («thySig» («ext» x5)) («replicate» x2 (leaf 0)) x3)
            («some» (leaf 0)))).label ≠ 0 then
        «certifies»
          x0
          x1
          («get» x4)
          («mkSeq» («replicate» x2 (leaf 0)) ([] : List T) («dfd» x3))
      else
        leaf 0
    else
      «anyDefs»
        x0
        (fun (x5 : List T) =>
          if (Const.eq («gBase» x0) («length» «sig»)).label ≠ 0 then
            «objOk» («envOfDefs» x5) x2 x3
          else
            leaf 0));
    x5

def «ldChecks» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «and»
      («isSome» («ldCompile» x0 x1))
      («mIsTy» x0 («ldArity» x1) («ldType» x1));
    x2

def «declLang» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «declComb» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «declDef» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «declConst» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: ([] : List T)))

def «declObj» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 4) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «declQuot» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 5) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «declDesc» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 6) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «devState» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «pr» x0 (Const.node (leaf 0) x1); x2

def «withPrims» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «globals»
      (Const.node (leaf 0) x1)
      (Const.node (leaf 0) («gDefs» x0))
      («gBase» x0);
    x2

def «withDefs» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «globals»
      (Const.node (leaf 0) («gPrims» x0))
      (Const.node (leaf 0) x1)
      («gBase» x0);
    x2

def «push» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List T := «append» x0 («single» x1); x2

def «sortsArr» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «anyDefs»
      x0
      (fun (x3 : List T) =>
        Const.equal
          («sortOf» («thySig» («ext» x3)) («replicate» x1 (leaf 0)) x2)
          («some» (leaf 1)));
    x3

def «quotStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : List T := «l2» x3 x3;
                   «bindO»
                     («compile» x0 x2 x4 («ctxObj» x5) («stdEnv» x5))
                     (fun (x6 : T) =>
                       let x7 : T := «relL» x3 («p1» x6);
                       let x8 : T := «relR» x3 («p1» x6);
                       let x9 : T := «primitive»
                         x2
                         («coeqProj» x7 x8)
                         x3
                         («phOp»
                           (Const.add («gBase» x0) («length» («gDefs» x0)))
                           («objVars» x2));
                       let x10 : T := «globals»
                         (Const.node (leaf 0) («push» («gPrims» x0) x9))
                         (Const.node
                           (leaf 0)
                           («push» («gDefs» x0) («defObj» x2 («coeqz» x7 x8))))
                         («gBase» x0);
                       let x11 : T := «length» («gPrims» x0);
                       let x12 : T := «mkThm»
                         x2
                         (Const.node (leaf 0) x5)
                         (Const.node (leaf 0) («single» x4))
                         («mEq»
                           («mArr» x11 («objVars» x2) («mVar» (leaf 1)))
                           («mArr» x11 («objVars» x2) («mVar» (leaf 0))));
                       if («and»
                         (Const.eq («gBase» x0) («length» «sig»))
                         («and»
                           («mIsTy» x0 x2 x3)
                           («and»
                             (Const.equal («p2» x6) «omega»)
                             («and»
                               («scoped» x2 («prArrow» x9))
                               («and»
                                 («mIsTy» x10 x2 («prCod» x9))
                                 («and»
                                   («sortsArr» x0 x2 («prArrow» x9))
                                   («isFormula» x10 x2 x5 («thConcl» x12)))))))).label ≠ 0 then
                         «some» («devState» x10 («push» x1 («entLang» x12)))
                       else
                         «none»));
    x5

def «descStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «bindO»
      («nth» («gPrims» x0) x2)
      (fun (x6 : T) =>
        «bindO»
          («bindO» («nth» x1 x5) «entryLanguage»)
          (fun (x7 : T) =>
            «bindO»
              («primRel» x6)
              (fun (x8 : T) =>
                let x9 : T := «prArity» x6;
                let x10 : List T := «single» («prDom» x6);
                «bindO»
                  («compile» x0 x9 x4 («ctxObj» x10) («stdEnv» x10))
                  (fun (x11 : T) =>
                    if (Const.eq («length» («thHyps» x7)) (leaf 1)).label ≠ 0 then
                      let x12 : T := «at» («thHyps» x7) (leaf 0);
                      let x13 : List T := «l2» («prDom» x6) («prDom» x6);
                      let x14 : T := «primitive»
                        x9
                        («coeqDesc»
                          («relL» («prDom» x6) x8)
                          («relR» («prDom» x6) x8)
                          («p1» x11))
                        («prCod» x6)
                        x3;
                      let x15 : T := «withPrims» x0 («push» («gPrims» x0) x14);
                      let x16 : T := «mArr»
                        («length» («gPrims» x0))
                        («objVars» x9)
                        («mArr» x2 («objVars» x9) («mVar» (leaf 0)));
                      let x17 : T := «mkThm»
                        x9
                        (Const.node (leaf 0) x10)
                        (Const.node (leaf 0) ([] : List T))
                        («mEq» x16 x4);
                      if («and»
                        (Const.eq («gBase» x0) («length» «sig»))
                        («and»
                          (Const.equal («p2» x11) x3)
                          («and»
                            («mIsTy» x0 x9 x3)
                            («and»
                              (Const.eq («thArity» x7) x9)
                              («and»
                                («equalTs» («thCtx» x7) x13)
                                («and»
                                  (Const.equal («thConcl» x7) («mEq» («weaken1» x4) x4))
                                  («and»
                                    (Const.equal
                                      («compile» x0 x9 x12 («ctxObj» x13) («stdEnv» x13))
                                      («some» («pr» x8 «omega»)))
                                    («and»
                                      («scoped» x9 («prArrow» x14))
                                      («and»
                                        («sortsArr» x0 x9 («prArrow» x14))
                                        («isFormula»
                                          x15
                                          x9
                                          x10
                                          («thConcl» x17))))))))))).label ≠ 0 then
                        «some» («devState» x15 («push» x1 («entLang» x17)))
                      else
                        «none»
                    else
                      «none»))));
    x6

def «declStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := x2;
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let x4 : T := Const.child x3 (leaf 0);
                     let x5 : T := Const.child x3 (leaf 1);
                     if («thmChecks» x0 x1 x4 x5).label ≠ 0 then
                       «some» («devState» x0 («push» x1 («entLang» x4)))
                     else
                       «none»
                   else
                     if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
                       let x4 : T := Const.child x3 (leaf 0);
                       let x5 : T := Const.child x3 (leaf 1);
                       if («certifies» x0 x1 x5 x4).label ≠ 0 then
                         «some» («devState» x0 («push» x1 («entComb» x4)))
                       else
                         «none»
                     else
                       if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                         let x4 : T := Const.child x3 (leaf 0);
                         if («ldChecks» x0 x4).label ≠ 0 then
                           «some»
                             («devState» («withDefs» x0 («push» («gDefs» x0) («defLang» x4))) x1)
                         else
                           «none»
                       else
                         if (Const.eq (Const.label x3) (leaf 3)).label ≠ 0 then
                           let x4 : T := Const.child x3 (leaf 0);
                           let x5 : T := Const.child x3 (leaf 1);
                           if («primConfirms» x0 x1 x4 x5).label ≠ 0 then
                             «some» («devState» («withPrims» x0 («push» («gPrims» x0) x4)) x1)
                           else
                             «none»
                         else
                           if (Const.eq (Const.label x3) (leaf 4)).label ≠ 0 then
                             let x4 : T := Const.child x3 (leaf 0);
                             let x5 : T := Const.child x3 (leaf 1);
                             let x6 : T := Const.child x3 (leaf 2);
                             if («objConfirms» x0 x1 x4 x5 x6).label ≠ 0 then
                               «some»
                                 («devState»
                                   («withDefs» x0 («push» («gDefs» x0) («defObj» x4 x5)))
                                   x1)
                             else
                               «none»
                           else
                             if (Const.eq (Const.label x3) (leaf 5)).label ≠ 0 then
                               let x4 : T := Const.child x3 (leaf 0);
                               let x5 : T := Const.child x3 (leaf 1);
                               let x6 : T := Const.child x3 (leaf 2); «quotStep» x0 x1 x4 x5 x6
                             else
                               let x4 : T := Const.child x3 (leaf 0);
                               let x5 : T := Const.child x3 (leaf 1);
                               let x6 : T := Const.child x3 (leaf 2);
                               let x7 : T := Const.child x3 (leaf 3); «descStep» x0 x1 x4 x5 x6 x7);
    x3

def «checkDev» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x3 : T) (x4 : T) =>
        «bindO»
          x4
          (fun (x5 : T) => «declStep» («p1» x5) (Const.children («p2» x5)) x3))
      («some» («devState» x0 x1))
      («reverse» x2);
    x3

end GebMirror.Metalogic

end
