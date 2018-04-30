module TypeFamily where

open import Data.Bool as B
open import Data.String as Str
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe as M
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Syntax
open import Typecheck

--------------------------------------------------------------------------------
-- The type environment

data TEnv : Set where
  etenv : TEnv
  _,_  : (String × Ty) -> TEnv -> TEnv

data _∈T_ : (String × Ty) -> TEnv -> Set where
  heret : ∀ {Γ s τ} -> (s , τ) ∈T ((s , τ) , Γ)
  skipt : ∀ {Γ s τ s' τ'} ->
           {α : False (s Str.≟ s')} -> (s , τ) ∈T Γ -> (s , τ) ∈T ((s' , τ') , Γ)

--------------------------------------------------------------------------------
-- Location type state environment: contains information about whether a location:
-- (1) has been written to,
-- (2) has been aliased (some other location depends on this one)


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
-- Region Environment (to check if a region is bound)


data REnv : Set where
  erenv : REnv
  _,_   : Region -> REnv -> REnv

-- Does this make sense ?
data _∉R_ : Region -> REnv -> Set where
  notherer : ∀ {r R} -> r ∉R R

data _∈R_ : Region -> REnv -> Set where
  herer : ∀ {r R} -> r ∈R R

--------------------------------------------------------------------------------
-- Constraint environment

data CEnv : Set where
  ecenv : CEnv
  _,_   : LocationConstraint -> CEnv -> CEnv

data _∈C_ : LocationConstraint -> CEnv -> Set where
  hereac : ∀ {n l0 l1 C} -> (AfterConstantC n l0 l1) ∈C C
  skipac : ∀ {l0 l1 l0' l1' n n' C} ->
             {α : False (l0 Str.≟ l0')} ->
             {β : False (l1 Str.≟ l1')} ->
             (AfterConstantC n l0 l1) ∈C C ->
             (AfterConstantC n l0 l1) ∈C ((AfterConstantC n' l0' l1') , C)

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
                  L , (r1 , R) , C , ((r1 , CursorTy) , T)  ⊢ bod ∷ (PackedAt tycon loc r2) , L2 ->
                  -----------------------------------------------------------------
                  L , R , C , T  ⊢ LetRegionE r1 bod ∷ (PackedAt tycon loc r2) , L2


   LetLocStartT : ∀ {L1 L3 R C T l1 r1 bod t} ->
                    -- -- ∃ some loc with before set to true
                    -- -- l1 not in C
                    ((l1 , (false , false , false)) , L1) , R ,
                    ((StartOfC l1 r1) , C) , ((l1 , CursorTy) , T) ⊢ bod ∷ t , L3 ->
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
                     ((AfterVariableC x l2 l1) , C) , ((l1 , CursorTy) , T) ⊢ bod ∷ t , L3 ->
                     -- l1 ∈W L3 ->
                     -- L4 = L3 - l1
                     ----------------------------------------------------------------
                     L1 , R , C , T  ⊢ LetLocE l1 (AfterVariableLE x l2) bod ∷ t , L3


   LetLocAfterCT :  ∀ {L1 L3 R C T l1 n bod t l2} ->
                      -- l1 not in C
                      -- l2 ∉A L1 ->
                      ((l1 , (false , (true , false))) , L1) , R ,
                      ((AfterConstantC n l2 l1) , C) , ((l1 , CursorTy) , T) ⊢ bod ∷ t , L3 ->
                      -- l1 ∈W L3 ->
                      -- L4 = L3 - l1
                      ----------------------------------------------------------------
                      L1 , R , C , T  ⊢ LetLocE l1 (AfterConstantLE n l2) bod ∷ t , L3


   -- Add a let scalar rule ...

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


   NodeT : ∀ {L1 L2 L3 R C T l0 r0 dc1 l1 r1 dc2 l2 x y} ->
              L1 , R , C , T ⊢ x ∷ PackedAt dc1 l1 r1 , L2 ->
              L2 , R , C , T ⊢ y ∷ PackedAt dc2 l2 r1 , L3 ->
              (AfterConstantC 1 l0 l1) ∈C C ->
              (AfterVariableC {!!} l1 l2) ∈C C ->
              ----------------------------------------------------------------
              L1 , R , C , T  ⊢ NodeE l0 r0 x y ∷ (PackedAt "Tree" l0 r0) , L3


-- Ex3: (Node (Leaf 1) (Leaf 2))
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
        NodeT (VarT (skipt (skipt heret))) (VarT heret) hereac hereav) (
        VarT heret))))
        )))

-- Ex3: (Leaf 1)
ex4 : Exp
ex4 = LetRegionE "r" (
      LetLocE "l1" (StartOfLE "r") (
      LetE ("x" , PackedAt "Tree" "l1" "r" , LeafE "l1" "r" (LitE 1)) (
      VarE "x"
      )))

test4 : ∀ {L1 L2 R C T} -> L1 , R , C , T  ⊢ ex4 ∷ PackedAt "Tree" "l1" "r" , L2
test4 {L1 = L1} {L2 = L2} {R = R} {C = C} {T = T} =
  LetRegionT notherer (LetLocStartT (LetPackedT (LeafT herel LitT) (VarT heret)))

--------------------------------------------------------------------------------
-- Value environment (used in the reduction relation)

data StoreVal : Set where
  N : StoreVal
  L : StoreVal
  I : ℕ -> StoreVal

Store : Set
Store = List (ℕ × StoreVal)


data Val : Set where
  LitV : ℕ -> Val
  -- Offset into some region
  CurV : Store -> ℕ -> Val
  StV  : Store -> Val

data VEnv : Set where
  evenv : VEnv
  _,_  : (String × Val) -> VEnv -> VEnv

data _∈V_ : (String × Val) -> VEnv -> Set where
  herev : ∀ {Γ s τ} -> (s , τ) ∈V ((s , τ) , Γ)
  skipv : ∀ {Γ s τ s' τ'} ->
           {α : False (s Str.≟ s')} -> (s , τ) ∈V Γ -> (s , τ) ∈V ((s' , τ') , Γ)

--------------------------------------------------------------------------------
-- Reduction relation

Closure : Set
Closure = VEnv × Exp


data Eval : Closure -> Val -> Set where
  LitR : ∀ {ve n} ->
           Eval (ve , (LitE n)) (LitV n)


  VarR : ∀ {ve x v} ->
           (x , v) ∈V ve -> Eval (ve , (VarE x)) v


  LetRegionR : ∀ {ve r bod v} ->
                 Eval (((r , (StV [])) , ve) , bod) v ->
                 Eval (ve , (LetRegionE r bod)) v


  LetLocStartR : ∀ {ve l r bod v st} ->
                 (r , StV st) ∈V ve ->
                 Eval (((l , (CurV st 0)) , ve) , bod) v ->
                 Eval (ve , (LetLocE l (StartOfLE r) bod)) v


  LetLocAfterCR : ∀ {ve l2 offset l1 n1 r1 bod v} ->
                    (l1 , (CurV r1 n1)) ∈V ve ->
                    Eval (((l2 , CurV r1 (n1 + offset)) , ve) , bod) v ->
                    Eval (ve , (LetLocE l2 (AfterConstantLE offset l1) bod)) v

  -- The 2 needs to be replaced with the "size" of the element at l1
  LetLocAfterVR : ∀ {ve l2 l1 n1 r1 bod v x} ->
                    (l1 , (CurV r1 n1)) ∈V ve ->
                    Eval (((l2 , CurV r1 (n1 + 2)) , ve) , bod) v ->
                    Eval (ve , (LetLocE l2 (AfterVariableLE x l1) bod)) v

  LetR : ∀ {ve x ty rhs vrhs bod v} ->
           Eval (ve , rhs) vrhs ->
           Eval (((x , vrhs) , ve) , bod) v ->
           Eval (ve , LetE (x , ty , rhs) bod) v


  LeafR : ∀ {st ve l r n o nv} ->
            (r , StV st) ∈V ve ->
            (l , CurV st o) ∈V ve ->
            Eval (ve , n) (LitV nv) ->
            Eval (ve , (LeafE l r n))
                 (StV (st L.++ (o , L) ∷ L.[ (suc o , I nv) ]))


  NodeR : ∀ {ve l r e1 e2 stx sty st o} ->
            (r , StV st) ∈V ve ->
            (l , CurV st o) ∈V ve ->
            Eval (ve , e1) (StV stx) ->
            Eval (ve , e2) (StV sty) ->
            Eval (ve , NodeE l r e1 e2)
                 (StV (st L.++ L.[ (o , N) ] L.++ stx L.++ sty))


rtest5 : Eval (evenv , LitE 42) (LitV 42)
rtest5 = LitR


-- Ex4: (Leaf 1)
rtest4 : Eval (evenv , ex4) (StV ((0 , L) ∷ (1 , I 1) ∷ []))
rtest4 = LetRegionR (
         LetLocStartR herev (
         LetR (LeafR (skipv herev) herev LitR) (
         VarR herev)))

-- Ex3: (Node (Leaf 1) (Leaf 2))
redEx3 : Val
redEx3 = StV ((0 , N) ∷  (1 , L) ∷ (2 , I 1) ∷ (3 , L) ∷ (4 , I 2) ∷ [])

rtest3 : Eval (evenv , ex3) redEx3
rtest3 = LetRegionR (
         LetLocStartR herev (
         LetLocAfterCR herev (
         LetR (LeafR (skipv (skipv herev)) herev LitR) (
         LetLocAfterVR (skipv herev) (
         LetR (LeafR (skipv (skipv (skipv (skipv herev)))) herev LitR) (
         LetR (NodeR (skipv (skipv (skipv (skipv (skipv herev)))))
                     (skipv (skipv (skipv (skipv herev))))
                     (VarR (skipv (skipv herev)))
                     (VarR herev))
         (VarR herev)))))))

--------------------------------------------------------------------------------
-- Type safety

-- When is a value compatible with a type v ∼ τ
-- When is a runtime environment compatible with a typing context (ve ≈ te)

data _∼_ : Val -> Ty -> Set
data _≈_ : VEnv -> TEnv -> Set

data _∼_ where
  num~ : ∀ {n} -> LitV n ∼ IntTy
  cursor~ : ∀ {st o} -> CurV st o ∼ CursorTy
  packed~ : ∀ {l r t st} -> StV st ∼ PackedAt t l r
  -- TODO: HACK to encode regions for now. They return a store, but are do not have a packed type ...
  region~ : ∀ {st} -> StV st ∼ CursorTy

data _≈_ where
  e≈ : evenv ≈ etenv
  x≈ : ∀ {x y v ty ve te} ->
         x ≡ y -> v ∼ ty -> ve ≈ te -> ((x , v) , ve) ≈ ((y , ty) , te)

-- Compatible environments mean that for every variable its value is
-- compatible with its type

ρ⇒vτ : ∀ {x v ty ve te} →
       ve ≈ te -> ((x , v) ∈V ve) -> ((x , ty) ∈T te) -> v ∼ ty
ρ⇒vτ e≈ ()
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) herev heret = v∼τ
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) herev (skipt {α = α} inΓ) =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipv {α = α} inρ) heret =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipv inρ) (skipt inΓ) = ρ⇒vτ ρ≈Γ inρ inΓ

--------------------------------------------------------------------------------

type-safety : ∀ {L1 R C T L2 e t V v} ->
                (V ≈ T) ->
                (L1 , R , C , T ⊢ e ∷ t , L2) -> Eval (V , e) v -> (v ∼ t)
type-safety ve≈te LitT LitR = num~
type-safety ve≈te (VarT x) (VarR y) = ρ⇒vτ ve≈te y x
type-safety ve≈te (LetRegionT r tyb) (LetRegionR ev) =
  let ve'≈te' = x≈ refl region~ ve≈te
  in type-safety ve'≈te' tyb ev
type-safety ve≈te (LetLocStartT tyj) (LetLocStartR x ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetLocAfterVT x₁ tyj) (LetLocAfterVR x₂ ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetLocAfterCT tyj) (LetLocAfterCR x ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetPackedT tyj1 tyj2) (LetR ev1 ev2) =
  let v1t1 = type-safety ve≈te tyj1 ev1
      ve'≈te' = x≈ refl v1t1 ve≈te
  in type-safety ve'≈te' tyj2 ev2
-- TODO: This check is useless. Should be more strict.
type-safety ve≈te (LeafT inL tyint) (LeafR rInV lInV ev) = packed~
type-safety ve≈te (NodeT tyj tyj₁ x₁ x₂) (NodeR x₃ x₄ ev ev₁) = packed~
