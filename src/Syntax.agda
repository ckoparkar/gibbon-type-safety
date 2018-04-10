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

data LocVar : Set where
  eLoc : LocVar
  Loc  : String -> LocVar

Var : Set
Var = String

DataCon : Set
DataCon = String

TyCon : Set
TyCon = String

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
  --
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

DDefs : Set
DDefs = List DDef

FunDefs : Set
FunDefs = List FunDef

record Prog : Set where
  field
    fundefs : FunDefs
    ddefs   : DDefs
    mainExp : Maybe Exp

--------------------------------------------------------------------------------
-- Common

VarEnv : Set
VarEnv = List (Var × Ty)

FunEnv : Set
FunEnv = List (Var × ArrowTy)

record Env2 : Set where
  field
    vEnv : VarEnv
    fEnv : FunEnv

-- lookupVar : Env2 -> Var -> Ty
-- lookupVar = {!!}


--------------------------------------------------------------------------------

ddtree : DDef
ddtree = record { tyName = "Tree"
                ; dataCons =   ("Leaf" , [ IntTy ] ) ∷
                             [ ("Node" ,   PackedTy "Tree" (Loc "l") ∷
                                               [ PackedTy "Tree" (Loc "r") ] )
                             ]
                }

buildTree : FunDef
buildTree = record { funName = "buildTree"
                   ; funArg  = "n"
                   ; funTy = record { locVars = [ record { loc = Loc "out2"
                                                         ; reg = Reg "r1"
                                                         ; mod = Output } ]
                                    ; inT  = IntTy
                                    ; outT = PackedTy "Tree" (Loc "out2") }
                   ; funBody = buildTreeBod
                   }
  where
    buildTreeBod : Exp
    buildTreeBod = LetE ( "b3" ,  [] , BoolTy
                        , PrimAppE EqIntP (VarE "n" ∷ [ LitE 0 ]))
                   (IfE (VarE "b3")
                     (DataConE (Loc "out2") "Leaf" [ LitE 1 ])
                     ( LetE ( ("n4") , [] , IntTy
                            , (PrimAppE SubP ( VarE "n" ∷ [ LitE 1 ])))
                       (LetLocE (Loc "loc_x5") (AfterConstantLE 1 (Loc "out2"))
                       (LetE ( "x5" , [] , PackedTy "Tree" (Loc "loc_x5")
                             , AppE "buildTree" [ (Loc "loc_x5") ] (VarE ("n4")))
                       (LetLocE (Loc "loc_y6") (AfterVariableLE "x5" (Loc "loc_x5"))
                       (LetE ("y8" , [] , PackedTy "Tree" (Loc "loc_y6")
                             , AppE "buildTree" [ (Loc "loc_y6") ] (VarE "n4"))
                       (LetE ("z9" , [] , PackedTy "Tree" (Loc "out2")
                             , DataConE (Loc "out2") "Node"
                                        (VarE "x5" ∷ [ VarE ("y8") ]))
                       (VarE "z9"))))))))
