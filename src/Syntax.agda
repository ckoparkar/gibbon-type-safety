{-# OPTIONS --allow-unsolved-metas #-}

module Syntax where

open import Data.Bool
open import Data.String as Str
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S

--------------------------------------------------------------------------------

LocVar : Set
LocVar = String

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

--------------------------------------------------------------------------------

Region : Set
Region = String

data Modality : Set where
  Input  : Modality
  Output : Modality

data LRM : Set where
  lrm : LocVar -> Region -> Modality -> LRM

lrmLoc : LRM -> LocVar
lrmLoc (lrm l _ _) = l

data LocExp : Set
data Exp : Set
data Ty : Set
CaseBranch : Set

data LocExp where
  StartOfLE : Region -> LocExp
  AfterConstantLE : ℕ   -> LocVar -> LocExp
  AfterVariableLE : Var -> LocVar -> LocExp

data Exp where
  VarE       : Var -> Exp
  AppE       : Var -> List LocVar -> Exp -> Exp
  LetE       : (Var × Ty × Exp) -> Exp -> Exp
  LetRegionE : Region -> Exp -> Exp
  LetLocE    : LocVar -> LocExp -> Exp -> Exp
  LeafE      : LocVar -> Region -> Exp -> Exp
  NodeE      : LocVar -> Region -> Exp -> Exp -> Exp
  --
  LitE : ℕ -> Exp
  PrimAppE : Prim -> List Exp -> Exp
  IfE : Exp -> Exp -> Exp -> Exp
  MkProdE : List Exp -> Exp
  ProjE : ℕ -> Exp -> Exp
  CaseE : Exp -> List CaseBranch -> Exp
  DataConE : LocVar -> DataCon -> List Exp -> Exp
  RetE : (List LocVar) -> Exp -> Exp

CaseBranch = DataCon × (List (Var × LocVar) × Exp)

data Ty where
  IntTy    : Ty
  PackedAt : TyCon -> LocVar -> Region -> Ty

  PackedTy : TyCon -> LocVar -> Ty
  BoolTy   : Ty
  ProdTy   : List Ty -> Ty
  CursorTy : Ty
  RegionTy : Ty
  ErrorTy  : String -> Exp -> Ty


--------------------------------------------------------------------------------

record ArrowTy : Set where
  field
    locVars : List LRM
    inT   : Ty
    outT  : Ty

record FunDef : Set where
  field
    funName  : Var
    funArg   : Var
    funTy    : ArrowTy
    funBody  : Exp

DDef : Set
DDef = Var × List (DataCon × List Ty)

DDefs : Set
DDefs = List DDef

FunDefs : Set
FunDefs = List FunDef

data Prog : Set where
  prog :  DDefs -> FunDefs -> (Exp × Ty) -> Prog

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

emptyEnv2 : Env2
emptyEnv2 = record { vEnv = []
                   ; fEnv = [] }

-- | Insert a var binding to the environment.
extendVEnv : Var -> Ty -> Env2 -> Env2
extendVEnv v ty env2 = record { vEnv = (v , ty) ∷ Env2.vEnv env2
                              ; fEnv = Env2.fEnv env2 }


-- | If the element is a member of a map.
mmemVar : ∀ {a : Set} -> Var -> List (Var × a) -> Bool
mmemVar x [] = false
mmemVar x ((y , _) ∷ ls) = x == y

mlookupVar : Var -> VarEnv -> Maybe Ty
mlookupVar x [] = nothing
mlookupVar x ((y , ty) ∷ rst) = if x == y then just ty else mlookupVar x rst

-- | Lookup the type of a variable in an environment.
mlookupVarEnv : Var -> Env2 -> Maybe Ty
mlookupVarEnv v env2 = mlookupVar v (Env2.vEnv env2)

-- | Simple filter function.
filter' : {A : Set} -> (A -> Bool) -> List A -> List A
filter' p [] = []
filter' p (x ∷ xs) with p x
... | true  = x ∷ filter' p xs
... | false = filter' p xs

-- | Lookup a DataCon.
lookupD : DDefs -> DataCon -> (TyCon × (DataCon × List Ty))
lookupD [] dcon = "ErrorTyCon" , ("ErrorDataCon" , [])
lookupD ((tyName , dcons) ∷ ddfs) dcon with filter' (λ x -> (proj₁ x) == dcon) dcons
... | []      = lookupD ddfs dcon
... | (x ∷ _) = tyName , x
-- ^ Doesn't check for duplicate DataCons

-- | Lookup the name of the TyCon that goes with a given DataCon.
getTyOfDataCon : DDefs -> DataCon -> TyCon
getTyOfDataCon ddfs dcon = proj₁ (lookupD ddfs dcon)

-- | Lookup the types of the arguments to a data contstructor.
lookupDataCon : DDefs -> DataCon -> List Ty
lookupDataCon ddfs dcon = proj₂ (proj₂ (lookupD ddfs dcon))

-- |
isPackedTy : Ty -> Bool
isPackedTy (PackedTy _ _) = true
{-# CATCHALL #-}
isPackedTy _ = false

-- |
isErrorTy : Ty -> Bool
isErrorTy (ErrorTy _ _) = true
{-# CATCHALL #-}
isErrorTy _ = false

-- | If the element is a member of the set.
smemLocVar : LocVar -> List LocVar -> Bool
smemLocVar loc [] = false
smemLocVar loc (l2 ∷ ls) = if loc == l2 then true else false

-- | Lookup the type of a variable in an environment.
mlookupLocVar : Var -> List (LocVar × LocVar) -> Maybe LocVar
mlookupLocVar v [] = nothing
mlookupLocVar v ((v2 , l) ∷ ls) = if v == v2 then just l else mlookupLocVar v ls


-- |
getFunTy : Var -> FunDefs -> ArrowTy
getFunTy f [] = record { locVars = []
                       ; inT = ErrorTy "ErrorIn" (LitE 0)
                       ; outT = ErrorTy "ErrorOut" (LitE 0) }
getFunTy f (fn ∷ fndefs) = if f == FunDef.funName fn
                           then FunDef.funTy fn
                           else getFunTy f fndefs

{-# TERMINATING #-}
substTy : List (LocVar × LocVar) -> Ty -> Ty
substTy mp IntTy = IntTy
substTy mp BoolTy = BoolTy
substTy mp (ProdTy tys) = ProdTy (L.map (substTy mp) tys)
substTy mp (PackedTy dc l1)  with mlookupLocVar l1 mp
... | just l2 = PackedTy dc l2
... | nothing = PackedTy dc l1
substTy mp CursorTy = CursorTy
substTy mp RegionTy = RegionTy
substTy mp (ErrorTy msg ex) = ErrorTy msg ex
substTy mp (PackedAt dc l1 reg) with mlookupLocVar l1 mp
... | just l2 = PackedAt dc l2 reg
... | nothing = PackedAt dc l1 reg

--------------------------------------------------------------------------------
-- Eq

{-# TERMINATING #-}
eqTy : Ty -> Ty -> Bool
eqTy IntTy IntTy = true
eqTy BoolTy BoolTy = true
eqTy (ProdTy tys1) (ProdTy tys2) = all (λ x -> eqTy (proj₁ x) (proj₂ x)) (L.zip tys1 tys2)
eqTy (PackedTy dc1 l1) (PackedTy dc2 l2) = (dc1 == dc2) ∧ (l1 == l2)
eqTy CursorTy CursorTy = true
eqTy (ErrorTy msg1 e1) (ErrorTy msg2 e2) = true
{-# CATCHALL #-}
eqTy ty1 ty2 = false

{-# TERMINATING #-}
eqTyNoLoc : Ty -> Ty -> Bool
eqTyNoLoc IntTy IntTy = true
eqTyNoLoc BoolTy BoolTy = true
eqTyNoLoc (ProdTy tys1) (ProdTy tys2) = all (λ x -> eqTyNoLoc (proj₁ x) (proj₂ x)) (L.zip tys1 tys2)
eqTyNoLoc (PackedTy dc1 l1) (PackedTy dc2 l2) = (dc1 == dc2)
eqTyNoLoc CursorTy CursorTy = true
eqTyNoLoc (ErrorTy msg1 e1) (ErrorTy msg2 e2) = true
{-# CATCHALL #-}
eqTyNoLoc ty1 ty2 = false


--------------------------------------------------------------------------------
-- Slides examples

data Tree : Set where
  Leaf : ℕ -> Tree
  Node : Tree -> Tree -> Tree

ex1 : Tree
ex1 = Node (Leaf 1) (Leaf 2)

----------------------------------------------------

buildtree : ℕ -> Tree
buildtree zero = Leaf 1
buildtree (suc n) = Node (buildtree n) (buildtree n)

ex2 : Tree
ex2 = buildtree 1
