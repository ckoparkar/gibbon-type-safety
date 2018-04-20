module Typecheck where

open import Data.Bool
open import Data.String as Str
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S

open import Syntax

data LocationConstraint : Set where
  StartOfC : LocVar -> Region -> LocationConstraint
  AfterConstantC : ℕ -> LocVar -> LocVar -> LocationConstraint
  AfterVariableC : ℕ -> LocVar -> LocVar -> LocationConstraint
  InRegionC : LocVar -> Region -> LocationConstraint

ConstraintSet : Set
ConstraintSet = List LocationConstraint

LocationTypeState : Set
LocationTypeState = List (Var × (Modality ×  Bool))

--------------------------------------------------------------------------------
-- Helpers

isIntTy : Ty -> Bool
isIntTy IntTy = true
isIntTy     _ = false

--------------------------------------------------------------------------------
{-# TERMINATING #-}
typecheck : DDefs -> FunDefs -> Env2 -> ConstraintSet -> LocationTypeState -> Exp
          -> (Ty × LocationTypeState)
typecheck ddfs fndefs env2 constrs tstatein (VarE x) with lookupVar x env2
-- Maybe it'd be better to just use the unsafe version here
... | just ty = ty , tstatein
... | nothing = Error (x Str.++ " not found") , tstatein
typecheck ddfs fndefs env2 constrs tstatein (LitE x) = (IntTy , tstatein)
typecheck ddfs fndefs env2 constrs tstatein (AppE f locs arg) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (PrimAppE pr args) = tcPrimAppE pr args
  where    
    tcPrimAppE : Prim -> List Exp -> (Ty × LocationTypeState)
    tcPrimAppE AddP args =
      let tys = L.map proj₁ (L.map (typecheck ddfs fndefs env2 constrs tstatein) args) 
      in if (all isIntTy tys)
         then IntTy , tstatein
         else Error ("AddP expects ints.") , tstatein
    tcPrimAppE SubP args = {!!}
    tcPrimAppE MulP args = {!!}
    tcPrimAppE EqIntP args = {!!}
    tcPrimAppE EqBoolP args = {!!}
    tcPrimAppE MkTrue args = {!!}
    tcPrimAppE MkFalse args = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (IfE ex ex₁ ex₂) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (MkProdE x) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (ProjE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (CaseE ex x) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (DataConE x x₁ x₂) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetRegionE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetLocE x x₁ ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (RetE x) = {!!}
