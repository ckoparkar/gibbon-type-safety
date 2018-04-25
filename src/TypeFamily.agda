module TypeFamily where

open import Data.Bool as B
open import Data.String as Str
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe as M
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


open import Syntax
open import Typecheck

--------------------------------------------------------------------------------

data TEnv : Set where
  etenv : TEnv
  _,_  : (String × Ty) -> TEnv -> TEnv

data _∈T_ : (String × Ty) → TEnv → Set where
  heret : ∀ {Γ s τ} -> (s , τ) ∈T ((s , τ) , Γ)
  skipt : ∀ {Γ s τ s' τ'} ->
           {α : False (s Str.≟ s')} -> (s , τ) ∈T Γ -> (s , τ) ∈T ((s' , τ') , Γ)

--------------------------------------------------------------------------------

data LEnv : Set where
  elenv : LEnv
  _,_  : (LocVar × (Bool × (Bool × Bool))) -> LEnv -> LEnv
                  -- (Written × Before × After)

data _∈L_ : (LocVar × (Bool × (Bool × Bool))) -> LEnv -> Set where
  herel : ∀ {l w b a L} -> (l , (w , (b , a))) ∈L ((l , (w , (b , a))) , L)
  skipl : ∀ {l1 w1 b1 a1 l2 w2 b2 a2 L} ->
            {α : False (l1 Str.≟ l2)} ->
            (l1 , (w1 , (b1 , a1))) ∈L L ->
            (l1 , (w1 , (b1 , a1))) ∈L ((l2 , (w2 , (b2 , a2))) , L)

{-

-- TODO: Define a substitution relation in Agda

-- Written
data _∈W_ : (LocVar × (Bool × (Bool × Bool))) -> LEnv -> Set where
  herew : ∀ {l before after L} -> (l , (true , (before , after))) ∈W ((l , (true , (before , after))) , L)
  skipw : ∀ {L l1 w1 b1 a1 l2 w2 b2 a2} ->
            {α : False (l1 Str.≟ l2)} ->
            (l1 , (w1 , (b1 , a1))) ∈W L ->
            (l1 , (w1 , (b1 , a1))) ∈W ((l2 , (w2 , (b2 , a2))) , L)

-- Before
data _∈B_ : LocVar -> LEnv -> Set where
  hereb : ∀ {l written after L} -> l ∈B ((l , (written , (true , after))) , L)

-- After
data _∈A_ : LocVar -> LEnv -> Set where
  herea : ∀ {l written before L} -> l ∈A ((l , (written , (before , true))) , L)

-- Not after
data _∉A_ : LocVar -> LEnv -> Set where
  notherea : ∀ {l written before L} -> l ∉A ((l , (written , (before , false))) , L)

-}

--------------------------------------------------------------------------------

data REnv : Set where
  erenv : REnv
  _,_   : Region -> REnv -> REnv

-- Does this make sense ?
data _∉R_ : Region -> REnv -> Set where
  notherer : ∀ {r R} -> r ∉R R

data _∈R_ : Region -> REnv -> Set where
  herer : ∀ {r R} -> r ∈R R

--------------------------------------------------------------------------------

data CEnv : Set where
  ecenv : CEnv
  _,_   : LocationConstraint -> CEnv -> CEnv

data _∈C_ : LocationConstraint -> CEnv -> Set where
  hereac : ∀ {l0 l1 C} -> (AfterConstantC 1 l0 l1) ∈C C
  skipac : ∀ {l0 l1 l0' l1' C} ->
             {α : False (l0 Str.≟ l0')} ->
             {β : False (l1 Str.≟ l1')} ->
             (AfterConstantC 1 l0 l1) ∈C C ->
             (AfterConstantC 1 l0 l1) ∈C ((AfterConstantC 1 l0' l1') , C)

  hereav : ∀ {s l0 l1 C} -> (AfterVariableC s l0 l1) ∈C C
  skipav : ∀ {s1 s2 l0 l1 l0' l1' C} ->
             {α : False (l0 Str.≟ l0')} ->
             {β : False (l1 Str.≟ l1')} ->
             (AfterVariableC s1 l0 l1) ∈C C ->
             (AfterVariableC s1 l0 l1) ∈C ((AfterVariableC s2 l0' l1') , C)

--------------------------------------------------------------------------------

data _,_,_,_⊢_∷_,_ : (L : LEnv) -> (R : REnv) -> (C : CEnv) -> (T : TEnv) -> (e : Exp) -> (t : Ty) -> (L' : LEnv) -> Set where

   LitT       : ∀ {L R C T n} ->
                ----------------------------------
                L , R , C , T ⊢ LitE n ∷ IntTy , L


   VarT       : ∀ {L R C T v tycon loc reg} ->
                  ((v , PackedAt tycon loc reg) ∈T T) ->
                  -- loc ∈W L ->
                  -- reg ∈R R ->
                  ------------------------------------------------------
                  L , R , C , T  ⊢ VarE v ∷ (PackedAt tycon loc reg) , L


   LetRegionT : ∀ {L L2 R C T tycon loc r1 r2 bod} ->
                  r1 ∉R R ->
                  L , (r1 , R) , C , T  ⊢ bod ∷ (PackedAt tycon loc r2) , L2 ->
                  -----------------------------------------------------------------
                  L , R , C , T  ⊢ LetRegionE r1 bod ∷ (PackedAt tycon loc r2) , L2


   LetLocStartT : ∀ {L1 L3 R C T l1 r1 bod t} ->
                    -- -- ∃ some loc with before set to true
                    -- -- l1 not in C
                    ((l1 , (false , false , false)) , L1) , R ,
                    ((StartOfC l1 r1) , C) , T ⊢ bod ∷ t , L3 ->
                    -- (l1 , (true , (b , a))) ∈W L3 ->
                    -- L4 = L3 - l1
                    -------------------------------------------------------
                    L1 , R , C , T  ⊢ LetLocE l1 (StartOfLE r1) bod ∷ t , L3


   LetLocAfterVT : ∀ {L1 L3 R C T l1 x bod t tycon l2 r1} ->
                     (x , PackedAt tycon l2 r1) ∈T T ->
                     -- l2 ∈W L1 ->
                     -- l2 ∉A L1 ->
                     -- set after(l2) = True
                     -- l1 not in C
                     ((l1 , (false , (true , false))) , L1)
                     , R ,
                     ((AfterVariableC x l2 l1) , C) , T ⊢ bod ∷ t , L3 ->
                     -- l1 ∈W L3 ->
                     -- L4 = L3 - l1
                     ----------------------------------------------------------------
                     L1 , R , C , T  ⊢ LetLocE l1 (AfterVariableLE x l2) bod ∷ t , L3


   LetLocAfterCT :  ∀ {L1 L3 R C T l1 n bod t l2} ->
                      -- l1 not in C
                      -- l2 ∉A L1 ->
                      ((l1 , (false , (true , false))) , L1) , R ,
                      ((AfterConstantC n l2 l1) , C) , T ⊢ bod ∷ t , L3 ->
                      -- l1 ∈W L3 ->
                      -- L4 = L3 - l1
                      ----------------------------------------------------------------
                      L1 , R , C , T  ⊢ LetLocE l1 (AfterConstantLE n l2) bod ∷ t , L3


   LetPackedT : ∀ {L1 L2 L3 R C T tycon1 l1 r1 x rhs bod tycon2 l2 r2} ->
                  L1 , R , C , T ⊢ rhs ∷ (PackedAt tycon1 l1 r1) , L2 ->
                  L2 , R , C , ((x , (PackedAt tycon1 l1 r1)) , T) ⊢ bod ∷ (PackedAt tycon2 l2 r2) , L3 ->
                  -------------------------------------------------------------------------------------------
                  L1 , R , C , T  ⊢ LetE (x , PackedAt tycon1 l1 r1 , rhs) bod ∷ (PackedAt tycon2 l2 r2) , L3


   LeafT : ∀ {L1 L2 R C T l1 r1 arg w b a} ->
             (l1 , (w , (b , a))) ∈L L1 ->
             L1 , R , C , T ⊢ arg ∷ IntTy , L1 ->
             ----------------------------------------------------------------
             L1 , R , C , T  ⊢ LeafE l1 r1 arg ∷ (PackedAt "Tree" l1 r1) , L2


   NodeT : ∀ {L1 L2 L3 R C T l0 r0 dc1 l1 r1 dc2 l2 r2 x y} ->
              L1 , R , C , T ⊢ x ∷ PackedAt dc1 l1 r1 , L2 ->
              L2 , R , C , T ⊢ y ∷ PackedAt dc2 l2 r2 , L3 ->
              (AfterConstantC 1 l0 l1) ∈C C ->
              (AfterVariableC {!!} l1 l2) ∈C C ->
              ----------------------------------------------------------------
              L1 , R , C , T  ⊢ NodeE l0 r0 x y ∷ (PackedAt "Tree" l0 r0) , L3


ex3 : Exp
ex3 = LetRegionE "r" (
      LetLocE "l0" (StartOfLE "r") (
      LetLocE "l1" (AfterConstantLE 1 "l0") (
      LetE ("x" , PackedAt "Tree" "l1" "r" , LeafE "l1" "r" (LitE 1)) (
      LetLocE "l2" (AfterVariableLE "x" "l1") (
      LetE ("y" , PackedAt "Tree" "l2" "r" , LeafE "l2" "r" (LitE 2)) (
      LetE ("z" , PackedAt "Tree" "l0" "r" , NodeE "l0" "r" (VarE "x") (VarE "y")) (
      VarE "z"
      )))))))

test3 : ∀ {L1 L2 R C T} -> L1 , R , C , T  ⊢ ex3 ∷ PackedAt "Tree" "l0" "r" , L2
test3 = LetRegionT notherer (
        LetLocStartT (
        LetLocAfterCT (
        LetPackedT (
        LeafT herel LitT) (
        LetLocAfterVT heret (
        LetPackedT (
        LeafT herel LitT) (
        LetPackedT (
        NodeT (VarT (skipt heret)) (VarT heret) hereac hereav) (
        VarT heret))))
        )))

ex4 : Exp
ex4 = LetRegionE "r" (
      LetLocE "l1" (StartOfLE "r") (
      LetE ("x" , PackedAt "Tree" "l1" "r" , LeafE "l1" "r" (LitE 1)) (
      VarE "x"
      )))

test4 : ∀ {L1 L2 R C T} -> L1 , R , C , T  ⊢ ex4 ∷ PackedAt "Tree" "l1" "r" , L2
test4 {L1 = L1} {L2 = L2} {R = R} {C = C} {T = T} =
  LetRegionT notherer (LetLocStartT (LetPackedT (LeafT herel LitT) (VarT heret)))