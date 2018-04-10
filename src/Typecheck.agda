{-# OPTIONS --allow-unsolved-metas #-}

module Typecheck where

open import Data.Bool
open import Data.String
open import Data.Nat
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List
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

lookupVar : Env2 -> Var -> Ty
lookupVar = {!!}

typecheck : DDefs -> FunDefs -> Env2 -> ConstraintSet -> LocationTypeState -> Exp
          -> (Ty × LocationTypeState)
typecheck ddfs fndefs env2 constrs tstatein (VarE x) = (lookupVar env2 x , tstatein)
typecheck ddfs fndefs env2 constrs tstatein (LitE x) = (IntTy , tstatein)
typecheck ddfs fndefs env2 constrs tstatein (AppE x x₁ ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (PrimAppE x x₁) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (IfE ex ex₁ ex₂) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (MkProdE x) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (ProjE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (CaseE ex x) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (DataConE x x₁ x₂) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetRegionE x ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (LetLocE x x₁ ex) = {!!}
typecheck ddfs fndefs env2 constrs tstatein (RetE x) = {!!}
