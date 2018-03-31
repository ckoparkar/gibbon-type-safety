module Syntax where

open import Data.Bool
open import Data.String
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
open import Data.AVL.Sets as S

--------------------------------------------------------------------------------

data Var : Set where
  V  : String -> Var

data LocVar : Set where
  eLoc : LocVar
  Loc  : String -> LocVar

data DataCon : Set where
  DataC : String -> DataCon

data TyCon : Set where
  TyC : String -> TyCon

data Prim : Set where
  AddP : Prim
  SubP : Prim
  MulP : Prim
  EqIntP  : Prim
  EqBoolP : Prim
  MkTrue  : Prim
  MkFalse : Prim

data Ty : Set where
  IntTy    : Ty
  BoolTy   : Ty
  ProdTy   : List Ty -> Ty
  PackedTy : TyCon -> LocVar -> Ty
  CursorTy : Ty

--------------------------------------------------------------------------------

data Region : Set where
  Reg : String -> Region

data Modality : Set where
  Input  : Modality
  Output : Modality

record LRM : Set where
  field
    loc : LocVar
    reg : Region
    mod : Modality

data Exp : Set
data LocExp : Set

data LocExp where
  StartOfLE : Region -> LocExp
  AfterConstantLE : ℕ   -> LocVar -> LocExp
  AfterVariableLE : Var -> LocVar -> LocExp

data Exp where
  VarE : Var -> Exp
  LitE : ℕ -> Exp
  AppE : Var -> List LocVar -> Exp -> Exp
  PrimAppE : Prim -> List Exp -> Exp
  LetE : (Var × List LocVar × Ty × Exp) -> Exp -> Exp
  IfE : Exp -> Exp -> Exp -> Exp
  MkProdE : List Exp -> Exp
  ProjE : ℕ -> Exp -> Exp
  CaseE : Exp -> List ((DataCon × List (Var × LocVar)) × Exp) -> Exp
  DataConE : LocVar -> DataCon -> List Exp -> Exp
  -- Location calculus
  LetRegionE : Region -> Exp -> Exp
  LetLocE : LocVar -> LocExp -> Exp -> Exp
  RetE : (List LocVar) -> Exp

--------------------------------------------------------------------------------

record ArrowTy : Set where
  field
    locVars : List LRM
    inT   : Ty
    -- arrEffs : S.Set Effect
    outT  : Ty
    -- locRets : List LRM

record FunDef : Set where
  field
    funName  : Var
    funArg   : Var
    funTy    : ArrowTy
    funBody  : Exp

record DDef : Set where
  field
    tyName   : Var
    dataCons : List (DataCon × List Ty)

record Prog : Set where
  field
    fundefs : List (Var × FunDef)
    ddefs   : List (Var × DDef)
    mainExp : Maybe Exp

--------------------------------------------------------------------------------

ddtree : DDef
ddtree = record { tyName = V "Tree"
                ; dataCons =   (DataC "Leaf" , [ IntTy ] ) ∷
                             [ (DataC "Node" ,   PackedTy (TyC "Tree") (Loc "l") ∷
                                               [ PackedTy (TyC "Tree") (Loc "r") ] )
                             ]
                }

buildTree : FunDef
buildTree = record { funName = V "buildTree"
                   ; funArg  = V "n"
                   ; funTy = record { locVars = [ record { loc = Loc "out2"
                                                         ; reg = Reg "r1"
                                                         ; mod = Output } ]
                                    ; inT  = IntTy
                                    ; outT = PackedTy (TyC "Tree") (Loc "out2") }
                   ; funBody = buildTreeBod
                   }
  where
    buildTreeBod : Exp
    buildTreeBod = LetE ( V "b3" ,  [] , BoolTy
                        , PrimAppE EqIntP (VarE (V "n") ∷ [ LitE 0 ]))
                   (IfE (VarE (V "b3"))
                     (DataConE (Loc "out2") (DataC "Leaf") [ LitE 1 ])
                     ( LetE ( (V "n4") , [] , IntTy
                            , (PrimAppE SubP ( VarE (V "n") ∷ [ LitE 1 ])))
                       (LetLocE (Loc "loc_x5") (AfterConstantLE 1 (Loc "out2"))
                       (LetE ( V "x5" , [] , PackedTy (TyC "Tree") (Loc "loc_x5")
                             , AppE (V "buildTree") [ (Loc "loc_x5") ] (VarE (V "n4")))
                       (LetLocE (Loc "loc_y6") (AfterVariableLE (V "x5") (Loc "loc_x5"))
                       (LetE (V "y8" , [] , PackedTy (TyC "Tree") (Loc "loc_y6")
                             , AppE (V "buildTree") [ (Loc "loc_y6") ] (VarE (V "n4")))
                       (LetE (V "z9" , [] , PackedTy (TyC "Tree") (Loc "out2")
                             , DataConE (Loc "out2") (DataC "Node")
                                        (VarE (V "x5") ∷ [ VarE (V "y8") ]))
                       (VarE (V "z9")))))))))
