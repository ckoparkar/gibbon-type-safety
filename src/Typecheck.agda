module Typecheck where

open import Data.Bool
open import Data.String as Str
open import Data.Nat
import Agda.Builtin.Nat as N
open import Data.Product
open import Data.Sum
open import Data.Maybe as M
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S

open import Syntax

data LocationConstraint : Set where
  StartOfC : LocVar -> Region -> LocationConstraint
  AfterConstantC : ℕ -> LocVar -> LocVar -> LocationConstraint
  AfterVariableC : Var -> LocVar -> LocVar -> LocationConstraint
  InRegionC : LocVar -> Region -> LocationConstraint

ConstraintSet : Set
ConstraintSet = List LocationConstraint

RegionSet : Set
RegionSet = List Region

LocationTypeState : Set
LocationTypeState = List (Var × (Modality ×  Bool))

--------------------------------------------------------------------------------
-- Helpers

combineTStates : LocationTypeState -> LocationTypeState -> LocationTypeState
combineTStates ts1 ts2 = ts1 L.++ ts2

-- |
projTy : ℕ -> List Ty -> Ty
projTy zero (x ∷ ls) = x
projTy (suc n) (x ∷ ls) = projTy n ls
projTy zero [] = ErrorTy "projTy: Unexpected projection" (LitE 0)
projTy (suc n) [] = ErrorTy "projTy: Unexpected projection" (LitE n)

-- | Typecheck a projection.
tcProj : ℕ -> Ty -> Ty
tcProj n (ProdTy ls) = projTy n ls
{-# CATCHALL #-}
tcProj n ty = ErrorTy "tcProj: Projection from non-tuple type." (LitE n)

-- | Return a location of a Packed type.
tyLoc : Ty -> LocVar
tyLoc (PackedTy _ loc) = loc
{-# CATCHALL #-}
tyLoc _ = "ErrorLoc"

-- | Turn an output location to an input location
switchOutLoc : LocVar -> LocationTypeState -> LocationTypeState
switchOutLoc loc [] = []
switchOutLoc loc ((loc2 , (m , b)) ∷ tstate) =
  if loc == loc2
  then (loc2 , (Input , b)) ∷ tstate
  else (loc2 , (m , b)) ∷ switchOutLoc loc tstate

getRegion :  LocVar -> ConstraintSet -> Region
getRegion loc [] = "ErrorRegion"
getRegion loc (InRegionC loc2 r ∷ constrs) =
  if (loc == loc2) then r else getRegion loc constrs
{-# CATCHALL #-}
getRegion loc (_ ∷ constrs) = getRegion loc constrs

-- | Insert a region into a region set.
regionInsert : Region -> RegionSet -> RegionSet
regionInsert r regset = r ∷ regset

-- | Ensure that a region is in a region set, reporting an error otherwise.
elemRegion : Region -> RegionSet -> Bool
elemRegion r [] = false
elemRegion r (r2 ∷ regset) = if r == r2 then true else elemRegion r regset

-- | Ensure that a location is not already "defined" by a start constraint.
absentStart : Region -> ConstraintSet -> Bool
absentStart r [] = true
absentStart r ((StartOfC _ r2) ∷ constrs) =
  if r == r2 then false else true
{-# CATCHALL #-}
absentStart r (_ ∷ constrs) = absentStart r constrs

extendConstrs : LocationConstraint -> ConstraintSet -> ConstraintSet
extendConstrs c cs = c ∷ cs

extendTS : LocVar -> (Modality × Bool) -> LocationTypeState -> LocationTypeState
extendTS loc val tstate = (loc , val) ∷ tstate

removeTS : LocVar -> LocationTypeState -> LocationTypeState
removeTS loc tstate = filter' (λ x -> not (proj₁ x == loc)) tstate

setAliased : LocVar -> LocationTypeState -> LocationTypeState
setAliased loc [] = []
setAliased loc ((loc2 , (m , b)) ∷ tstate) =
  if loc == loc2
  then (loc2 , (m , true)) ∷ tstate
  else (loc2 , (m , b)) ∷ (setAliased loc tstate)

-- | Check that l2 is after l1
ensureAfterConstant : ℕ -> LocVar -> LocVar -> ConstraintSet -> Bool
ensureAfterConstant n l1 l2 [] = false
ensureAfterConstant n l1 l2 (StartOfC _ _ ∷ cs) = ensureAfterConstant n l1 l2 cs
ensureAfterConstant n l1 l2 (AfterConstantC n' l1' l2' ∷ cs) =
  if (n N.== n') ∧ (l1 == l1') ∧ (l2 == l2')
  then true
  else ensureAfterConstant n l1 l2 cs
ensureAfterConstant n l1 l2 (AfterVariableC _ _ _ ∷ cs) = ensureAfterConstant n l1 l2 cs
ensureAfterConstant n l1 l2 (InRegionC _ _ ∷ cs) = ensureAfterConstant n l1 l2 cs

-- | Check that l2 is after l1
ensureAfterPacked : LocVar -> LocVar -> ConstraintSet -> Bool
ensureAfterPacked l1 l2 [] = false
ensureAfterPacked l1 l2 (StartOfC _ _ ∷ cs) = ensureAfterPacked l1 l2 cs
ensureAfterPacked l1 l2 (AfterConstantC _ _ _ ∷ cs) = ensureAfterPacked l1 l2 cs
ensureAfterPacked l1 l2 (AfterVariableC _ l1' l2' ∷ cs) =
  if (l1 == l1') ∧ (l2 == l2')
  then true
  else ensureAfterPacked l1 l2 cs
ensureAfterPacked l1 l2 (InRegionC _ _ ∷ cs) = ensureAfterPacked l1 l2 cs

--------------------------------------------------------------------------------

tcExp : DDefs -> FunDefs -> Env2 -> ConstraintSet -> RegionSet -> LocationTypeState ->
        Exp -> (Ty × LocationTypeState)

tcExps : DDefs -> FunDefs -> Env2 -> ConstraintSet -> RegionSet -> LocationTypeState ->
         List Exp -> (List Ty × LocationTypeState)

tcCases : DDefs -> FunDefs -> Env2 -> ConstraintSet -> RegionSet -> LocationTypeState ->
          LocVar -> Region -> List CaseBranch -> (List Ty × LocationTypeState)

tcDataCon : LocVar -> List Ty -> ConstraintSet -> Bool

--| The main typechecking function.
tcExp ddfs fndefs env2 constrs regset tstatein (VarE x) with mlookupVarEnv x env2
-- Maybe it'd be better to just use the unsafe version here
... | just ty = ty , tstatein
... | nothing = ErrorTy (x Str.++ " not found") (VarE x) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (LitE x) = (IntTy , tstatein)

tcExp ddfs fndefs env2 constrs regset tstatein (AppE f locs arg) =
  let fnty = getFunTy f fndefs in
  let (ty , tstate) = tcExp ddfs fndefs env2 constrs regset tstatein arg in
  -- If we pass a packed structure as an argument, its location should be among the
  -- passed-in locations.
  let argok = (if isPackedTy ty
                  then (if smemLocVar (tyLoc ty) locs
                       then true
                       else false)
                  else true)
  in if argok
     -- Inputs line up with the expected types
     then (if eqTyNoLoc ty (ArrowTy.inT fnty)
           then (let arroutmap = L.zip (L.map lrmLoc (ArrowTy.locVars fnty)) locs in
                 let outTy' = substTy arroutmap (ArrowTy.outT fnty) in
                 outTy' , tstate)
           else ErrorTy "AppE: argument type doesn't match" (AppE f locs arg) , tstatein)
     else ErrorTy "AppE: location of argument not passed" (AppE f locs arg) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (PrimAppE pr args) = tcPrimAppE pr args
  where
    -- TODO: Check the length of args.
    tcPrimAppE : Prim -> List Exp -> (Ty × LocationTypeState)
    tcPrimAppE AddP args =
      let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein args
      in if (all (eqTy IntTy) tys)
         then IntTy , tstate
         else ErrorTy ("AddP expects ints.") (PrimAppE pr args) , tstate
    tcPrimAppE SubP args =
      let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein args
      in if (all (eqTy IntTy) tys)
         then IntTy , tstate
         else ErrorTy ("SubP expects ints.") (PrimAppE pr args) , tstate
    tcPrimAppE MulP args =
      let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein args
      in if (all (eqTy IntTy) tys)
         then IntTy , tstate
         else ErrorTy ("MulP expects ints.") (PrimAppE pr args) , tstate
    tcPrimAppE EqIntP args =
      let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein args
      in if (all (eqTy IntTy) tys)
         then BoolTy , tstate
         else ErrorTy ("EqIntP expects ints.") (PrimAppE pr args) , tstate
    tcPrimAppE EqBoolP args =
      let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein args
      in if (all (eqTy BoolTy) tys)
         then BoolTy , tstate
         else ErrorTy ("EqBoolP expects ints.") (PrimAppE pr args) , tstate
    tcPrimAppE MkTrue args =
      if L.null args
      then BoolTy , tstatein
      else ErrorTy ("MkTrue doesn't take any arguments.") (PrimAppE pr args) , tstatein
    tcPrimAppE MkFalse args =
      if L.null args
      then BoolTy , tstatein
      else ErrorTy ("MkFalse doesn't take any arguments.") (PrimAppE pr args) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (LetE (v , ty , rhs) bod) =
  let (ty1 , tstate1) = tcExp ddfs fndefs env2 constrs regset tstatein rhs
  in if eqTyNoLoc ty1 ty
     then (let env2' = extendVEnv v ty env2
           in tcExp ddfs fndefs env2' constrs regset tstate1 bod)
     else ErrorTy ("LetE: Failed to typecheck RHS") rhs , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (IfE a b c) =
  let (ty1 , tstate1) = tcExp ddfs fndefs env2 constrs regset tstatein a
  in if eqTyNoLoc ty1 BoolTy
     then (let (ty2 , tstate2) = tcExp ddfs fndefs env2 constrs regset tstate1 b in
           let (ty3 , tstate3) = tcExp ddfs fndefs env2 constrs regset tstate2 c in
           let tstate = combineTStates tstate2 tstate2 in
           if eqTy ty2 ty3
           then ty2 , tstate
           else ErrorTy ("IfE: Branches don't match") (IfE a b c) , tstatein)
     else ErrorTy ("IfE: Conditional expects a boolean type") (IfE a b c) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (MkProdE ls) =
  let (tys , tstate) = tcExps ddfs fndefs env2 constrs regset tstatein ls
  in ProdTy tys , tstate

tcExp ddfs fndefs env2 constrs regset tstatein (ProjE i e) =
  let (ty , tstate) = tcExp ddfs fndefs env2 constrs regset tstatein e
  in tcProj i ty , tstate

tcExp ddfs fndefs env2 constrs regset tstatein (CaseE ex ls) =
  let (ty , tstate) = tcExp ddfs fndefs env2 constrs regset tstatein ex in
  let lin = tyLoc ty in
  if lin == "ErrorLoc"
  then ErrorTy "CaseE: Scrutinee is not Packed" (CaseE ex ls) , tstatein
  else (let reg = getRegion lin constrs in
        let (tys , tstate') = tcCases ddfs fndefs env2 constrs regset tstate lin reg ls in
        projTy 0 tys , tstate')

tcExp ddfs fndefs env2 constrs regset tstatein (DataConE loc dc ls) =
  let tycon = getTyOfDataCon ddfs dc in
  let (tys , tstate') = tcExps ddfs fndefs env2 constrs regset tstatein ls in
  let expectedtys = lookupDataCon ddfs dc in
  if all (λ x -> eqTyNoLoc (proj₁ x) (proj₂ x)) (L.zip tys expectedtys)
  then (if tcDataCon loc tys constrs
        then  (let tstate'' = switchOutLoc loc tstate' in
               PackedTy tycon loc , tstate'')
        else ErrorTy ("DataConE: Could not verify constraints") (DataConE loc dc ls) , tstatein)
  else ErrorTy ("DataConE: Argument types don't match") (DataConE loc dc ls) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (LetRegionE r e) =
  let regset' = regionInsert r regset in
  tcExp ddfs fndefs env2 constrs regset' tstatein e

tcExp ddfs fndefs env2 constrs regset tstatein (LetLocE loc (StartOfLE r) e) =
  if (elemRegion r regset ∧ absentStart r constrs)
  then (let constrs' = extendConstrs (StartOfC loc r) (extendConstrs (InRegionC loc r) constrs) in
        let tstate' = extendTS loc (Output , false) tstatein in
        let (ty , tstate'') = tcExp ddfs fndefs env2 constrs' regset tstate' e in
        let tstate3 = removeTS loc tstate'' in
        ty , tstate3)
  else ErrorTy ("LetLocE: ErrorTy2") (LetLocE loc (StartOfLE r) e) , tstatein

tcExp ddfs fndefs env2 constrs regset tstatein (LetLocE loc (AfterConstantLE n loc2) e) =
  let r = getRegion loc2 constrs in
  let constrs' = extendConstrs (AfterConstantC n loc2 loc) (extendConstrs (InRegionC loc r) constrs) in
  let tstate' = extendTS loc (Output , true) (setAliased loc2 tstatein) in
  let (ty , tstate'') = tcExp ddfs fndefs env2 constrs' regset tstate' e in
  let tstate3 = removeTS loc tstate'' in
  ty , tstate3
tcExp ddfs fndefs env2 constrs regset tstatein (LetLocE loc (AfterVariableLE v loc2) e) =
  let r = getRegion loc2 constrs in
  let constrs' = extendConstrs (AfterVariableC v loc2 loc) (extendConstrs (InRegionC loc r) constrs) in
  let (_ , tstate1) = tcExp ddfs fndefs env2 constrs regset tstatein (VarE v) in
  let tstate' = extendTS loc (Output , true) (setAliased loc2 tstate1) in
  let (ty , tstate'') = tcExp ddfs fndefs env2 constrs' regset tstate' e in
  let tstate3 = removeTS loc tstate'' in
  ty , tstate3

tcExp ddfs fndefs env2 constrs regset tstatein (RetE locs e) =
  tcExp ddfs fndefs env2 constrs regset tstatein e

-- Hacks:
tcExp ddfs fndefs env2 constrs regset tstatein (LeafE loc r n) =
  let (ty , tstate) = tcExp ddfs fndefs env2 constrs regset tstatein n in
  if eqTy ty IntTy
  -- TODO: Check after constant 1
  then PackedTy "Tree" loc , tstate
  else ErrorTy "LeafE: Argument not an int" (LeafE loc r n) , tstate

tcExp ddfs fndefs env2 constrs regset tstatein (NodeE loc r x y) =
  let (tyx , tstate1) = tcExp ddfs fndefs env2 constrs regset tstatein x in
  let (tyy , tstate2) = tcExp ddfs fndefs env2 constrs regset tstate1 y in
  (if (isPackedTy tyx)
  then (if (isPackedTy tyy)
        then (let locx = tyLoc tyx in
              let locy = tyLoc tyy in
              if (ensureAfterConstant 1 loc locx constrs)
              then (if (ensureAfterPacked locx locy constrs)
                    then PackedTy "Tree" loc , tstate2
                    else (ErrorTy "NodeE: ly = l + lx not found." (NodeE loc r x y)) , tstate2)
              else (ErrorTy "NodeE: lx = l + 1 not found." (NodeE loc r x y)) , tstate2)
        else (ErrorTy "NodeE: not packed" y) , tstate2)
  else (ErrorTy "NodeE: x not packed" x) , tstate2)

-- |
tcExps ddfs fndefs env2 constrs regset tstatein [] = [] , tstatein
tcExps ddfs fndefs env2 constrs regset tstatein (exp ∷ exps) =
  let (ty , tstate') = tcExp ddfs fndefs env2 constrs regset tstatein exp in
  let (tys , tstate'') = tcExps ddfs fndefs env2 constrs regset tstate' exps in
  ty ∷ tys , tstate''

-- |
tcCases ddfs fndefs env2 constrs regset tstatein lin reg [] = [] , tstatein
tcCases ddfs fndefs env2 constrs regset tstatein lin reg ((dc , (vs , bod)) ∷ brs) =
  let argtys : List ((Var × LocVar) × Ty)
      argtys = L.zip vs (lookupDataCon ddfs dc) in
  let pairwise : List (((Var × LocVar) × Ty) × Maybe ((Var × LocVar) × Ty))
      pairwise = L.zip argtys (nothing ∷ (L.map just argtys)) in
  let constrs1 = L.foldr extendConstrs constrs (proj₂ (L.foldr genConstrs (lin , []) pairwise)) in
  let tstate1 = L.foldr genTS tstatein argtys in
  let env2' = L.foldr genEnv env2 argtys in
  let (ty1 , tstate2) = tcExp ddfs fndefs env2' constrs1 regset tstate1 bod in
  let (tyrst , tstaterst) = tcCases ddfs fndefs env2 constrs regset tstatein lin reg brs in
  let tstatecombine = combineTStates tstate2 tstaterst in
  let tstate'' = L.foldr remTS tstatecombine argtys in
  (ty1 ∷ tyrst) , tstate''
  where
    -- Generate the new constraints to check a case branch
    genConstrs : (((Var × Var) × Ty) × Maybe ((Var × LocVar) × Ty)) ->
                 (LocVar × List LocationConstraint) -> (Var × List LocationConstraint)
    genConstrs (((_v1 , l1) , PackedTy _ _) , nothing) (lin , lst) =
      (l1 , [ AfterConstantC 1 lin l1 ] L.++ [ InRegionC l1 reg ] L.++ lst)
    genConstrs (((_v1 , l1) , PackedTy _ _) , just ((v2 , l2) , PackedTy _ _)) (_lin , lst) =
      (l1 , [ AfterVariableC v2 l2 l1 ] L.++ [ InRegionC l1 reg ] L.++ lst)
    genConstrs (((_v1 , l1) , PackedTy _ _) , just ((_v2 , _l2) , IntTy)) (lin , lst) =
      -- Hard coding the size is fine for now
      (l1 , [ AfterConstantC 8 lin l1 ] L.++ [ InRegionC l1 reg ] L.++ lst)
    {-# CATCHALL #-}
    genConstrs (((_ , l1) , _) , _) (lin , lst) =
        (lin , InRegionC l1 reg ∷ lst)

    -- Generate the new location state map to check a case branch
    genTS : ((LocVar × LocVar) × Ty) -> LocationTypeState -> LocationTypeState
    genTS ((_v , l) , PackedTy _ _) ts = extendTS l (Input , false) ts
    {-# CATCHALL #-}
    genTS _ ts = ts


    genEnv : ((Var × LocVar) × Ty) -> Env2 -> Env2
    genEnv ((v , l) , PackedTy dc _l') env = extendVEnv v (PackedTy dc l) env
    {-# CATCHALL #-}
    genEnv ((v , _l) , ty) env = extendVEnv v ty env

    -- Remove the pattern-bound location variables from the location state map
    remTS : ((LocVar × LocVar) × Ty) -> LocationTypeState -> LocationTypeState
    remTS ((_v , l) , PackedTy _ _) ts = removeTS l ts
    {-# CATCHALL #-}
    remTS _ ts = ts

-- | TODO
tcDataCon loc tys constrs = true

--------------------------------------------------------------------------------

tcFunDef : DDefs -> FunDefs -> FunDef -> Ty
tcFunDef ddfs fndefs fn =
  let fnty = FunDef.funTy fn in
  let env2 = extendVEnv (FunDef.funArg fn) (ArrowTy.inT fnty) emptyEnv2 in
  let lvars = ArrowTy.locVars fnty in
  let constrs = fnConstrs lvars in
  let regset = fnRegset lvars in
  let tstatein = fnTState lvars in
  proj₁ (tcExp ddfs fndefs env2 constrs regset tstatein (FunDef.funBody fn))
  where
    fnConstrs : List LRM -> ConstraintSet
    fnConstrs [] = []
    fnConstrs ((lrm l r _) ∷ ls) = extendConstrs (InRegionC l r) (fnConstrs ls)

    fnRegset : List LRM -> RegionSet
    fnRegset [] = []
    fnRegset ((lrm _ r _) ∷ ls) = r ∷ (fnRegset ls)

    fnTState : List LRM -> LocationTypeState
    fnTState [] = []
    fnTState ((lrm l r m) ∷ ls) = extendTS l (m , false) (fnTState ls)

tcProg : Prog -> (List Ty) ⊎ Prog
tcProg (prog ddfs fndefs (mainexp , ty)) =
  let fntys = L.map (tcFunDef ddfs fndefs) fndefs in
  let errors = filter' isErrorTy fntys in
  if L.null errors
  then (let (ty1 , _) = tcExp ddfs fndefs emptyEnv2 [] [] [] mainexp in
        if isErrorTy ty ∨ (not (eqTy ty ty1))
        then inj₂ (prog ddfs fndefs (mainexp , ty))
        else inj₁ [ ty ]
       )
  else inj₁ errors

--------------------------------------------------------------------------------

ddtree : DDef
ddtree = ( "Tree"
         ,
           ("Leaf" , [ IntTy ] ) ∷
         [ ("Node" ,   PackedTy "Tree" "l" ∷
                       [ PackedTy "Tree" "r" ] )
         ])

buildTreeFunDef : FunDef
buildTreeFunDef = record
                   { funName = "buildTree"
                   ; funArg  = "n"
                   ; funTy = record { locVars = [ lrm "out2" "r1" Output ]
                                    ; inT  = IntTy
                                    ; outT = PackedTy "Tree" "out2" }
                   ; funBody = buildTreeBod
                   }
  where
    buildTreeBod : Exp
    buildTreeBod = LetE ( "b3" , BoolTy
                        , PrimAppE EqIntP (VarE "n" ∷ [ LitE 0 ]))
                   (IfE (VarE "b3")
                     (LeafE "out2" "r1" (LitE 1))
                     ( LetE ( ("n4") , IntTy
                            , (PrimAppE SubP ( VarE "n" ∷ [ LitE 1 ])))
                       (LetLocE "loc_x5" (AfterConstantLE 1 "out2")
                       (LetE ( "x5" , PackedTy "Tree" "loc_x5"
                             , AppE "buildTree" [ "loc_x5" ] (VarE ("n4")))
                       (LetLocE "loc_y6" (AfterVariableLE "x5" "loc_x5")
                       (LetE ("y8" , PackedTy "Tree" "loc_y6"
                             , AppE "buildTree" [ "loc_y6" ] (VarE "n4"))
                       (LetE ("z9" , PackedTy "Tree" "out2" ,
                              NodeE "out2" "r1" (VarE "x5") (VarE "y8"))
                       (VarE "z9"))))))))

buildTreeMainExp : Exp
buildTreeMainExp = LetRegionE "r20"
                   (LetLocE "l21" (StartOfLE "r20")
                   (AppE "buildTree" ["l21"] (LitE 2)))

buildTreeProg : Prog
buildTreeProg = prog [ ddtree ] [ buildTreeFunDef ] (buildTreeMainExp , PackedAt "Tree" "l21" "r1")

test1 : (List Ty) ⊎ Prog
test1 = tcProg buildTreeProg
