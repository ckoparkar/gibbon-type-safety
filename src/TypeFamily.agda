module TypeFamily where

open import Data.Bool as B
open import Data.String as Str hiding (_++_)
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe as M
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L
open import Data.AVL.Sets as S
open import Relation.Nullary.Decidable
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
-- (2) has been aliased (if l₂ = l₁ + 1; then this bit is true for l₁)
-- (3) aliases another location (if l₂ = l₁ + 1; then this bit is true for l₂)

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

data _∉L_ : Region -> LEnv -> Set where
  notherel : ∀ {L} -> {l : LocVar} -> l ∉L L

{-

These relations aren't being used anywhere. Essentially, we do not
update or check any properties about the locations.
TODO.


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
  notherer : ∀ {R} -> {r : Region} -> r ∉R R

data _∈R_ : Region -> REnv -> Set where
  herer : ∀ {r R} -> r ∈R R

∉R⇒r : ∀ {r R} -> r ∉R R -> String
∉R⇒r {r = r} notherer = r

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

  hereav : ∀ {l0 l1 C} -> (AfterVariableC l0 l1) ∈C C
  skipav : ∀ {l0 l1 l0' l1' C} ->
             {α : False (l0 Str.≟ l0')} ->
             {β : False (l1 Str.≟ l1')} ->
             (AfterVariableC l0 l1) ∈C C ->
             (AfterVariableC l0 l1) ∈C ((AfterVariableC l0' l1') , C)

--------------------------------------------------------------------------------

data _,_,_,_⊢_::_,_ : (L : LEnv) -> (R : REnv) -> (C : CEnv) -> (T : TEnv) -> (e : Exp) -> (t : Ty) -> (L' : LEnv) -> Set where
   LitT       : ∀ {L R C T n} ->
                ----------------------------------
                L , R , C , T ⊢ LitE n :: IntTy , L


   VarT       : ∀ {L R C T v tycon loc reg} ->
                  ((v , PackedAt tycon loc reg) ∈T T) ->
                  -- loc ∈W L ->
                  -- reg ∈R R ->
                  ------------------------------------------------------
                  L , R , C , T  ⊢ VarE v :: (PackedAt tycon loc reg) , L


   LetRegionT : ∀ {L L2 R C T tycon loc r1 r2 bod} ->
                  r1 ∉R R ->
                  L , (r1 , R) , C , ((r1 , RegionTy) , T)  ⊢ bod :: (PackedAt tycon loc r2) , L2 ->
                  -----------------------------------------------------------------
                  L , R , C , T  ⊢ LetRegionE r1 bod :: (PackedAt tycon loc r2) , L2


   LetLocStartT : ∀ {L1 L3 R C T l1 r1 bod t} ->
                    -- ∃ some loc with _before_ set to true
                    (r1 , RegionTy) ∈T T ->
                    l1 ∉L L1 ->
                    ((l1 , (false , false , false)) , L1) , R ,
                    ((StartOfC l1 r1) , C) , ((l1 , CursorTy) , T) ⊢ bod :: t , L3 ->
                    -- (l1 , (true , (b , a))) ∈W L3 ->
                    -------------------------------------------------------
                    L1 , R , C , T  ⊢ LetLocE l1 (StartOfLE r1) bod :: t , L3


   LetLocAfterVT : ∀ {L1 L3 R C T l1 x bod t tycon l2 r1} ->
                     (x , PackedAt tycon l2 r1) ∈T T ->
                     -- l2 ∈W L1 ->
                     -- l2 ∉A L1 ->
                     -- set after(l2) = True
                     (l2 , CursorTy) ∈T T ->
                     l1 ∉L L1 ->
                     ((l1 , (false , (true , false))) , L1)
                     , R ,
                     ((AfterVariableC l2 l1) , C) , ((l1 , CursorTy) , T) ⊢ bod :: t , L3 ->
                     -- l1 ∈W L3 ->
                     ----------------------------------------------------------------
                     L1 , R , C , T  ⊢ LetLocE l1 (AfterVariableLE x l2) bod :: t , L3


   LetLocAfterCT :  ∀ {L1 L3 R C T l1 n bod t l2} ->
                      (l2 , CursorTy) ∈T T ->
                      l1 ∉L L1 ->
                      -- l2 ∉A L1 ->
                      ((l1 , (false , (true , false))) , L1) , R ,
                      ((AfterConstantC n l2 l1) , C) , ((l1 , CursorTy) , T) ⊢ bod :: t , L3 ->
                      -- l1 ∈W L3 ->
                      ----------------------------------------------------------------
                      L1 , R , C , T  ⊢ LetLocE l1 (AfterConstantLE n l2) bod :: t , L3


   LetPackedT : ∀ {L1 L2 L3 R C T tycon1 l1 r1 x rhs bod tycon2 l2 r2} ->
                  L1 , R , C , T ⊢ rhs :: (PackedAt tycon1 l1 r1) , L2 ->
                  L2 , R , C , ((x , (PackedAt tycon1 l1 r1)) , T) ⊢ bod :: (PackedAt tycon2 l2 r2) , L3 ->
                  -------------------------------------------------------------------------------------------
                  L1 , R , C , T  ⊢ LetE (x , PackedAt tycon1 l1 r1 , rhs) bod :: (PackedAt tycon2 l2 r2) , L3


   LeafT : ∀ {L1 L2 R C T l1 r1 arg w b a} ->
             (l1 , (w , (b , a))) ∈L L1 ->
             L1 , R , C , T ⊢ arg :: IntTy , L1 ->
             ----------------------------------------------------------------
             L1 , R , C , T  ⊢ LeafE l1 r1 arg :: (PackedAt "Tree" l1 r1) , L2


   NodeT : ∀ {L1 L2 L3 R C T l0 r l1 l2 x y} ->
              L1 , R , C , T ⊢ x :: PackedAt "Tree" l1 r , L2 ->
              L2 , R , C , T ⊢ y :: PackedAt "Tree" l2 r , L3 ->
              (AfterConstantC 1 l0 l1) ∈C C ->
              (AfterVariableC l1 l2) ∈C C ->
              ----------------------------------------------------------------
              L1 , R , C , T  ⊢ NodeE l0 r x y :: (PackedAt "Tree" l0 r) , L3


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

test3 : ∀ {L1 L2 R C T} -> L1 , R , C , T  ⊢ ex3 :: PackedAt "Tree" "l0" "r" , L2
test3 = LetRegionT notherer (
        LetLocStartT heret notherel (
        LetLocAfterCT heret notherel (
        LetPackedT (
        LeafT herel LitT) (
        LetLocAfterVT heret (skipt heret) notherel (
        LetPackedT (
        LeafT herel LitT) (
        LetPackedT (
        NodeT (VarT (skipt (skipt heret))) (VarT heret) hereac hereav) (
        VarT heret)))))))

-- Ex3: (Leaf 1)
ex4 : Exp
ex4 = LetRegionE "r" (
      LetLocE "l1" (StartOfLE "r") (
      LetE ("x" , PackedAt "Tree" "l1" "r" , LeafE "l1" "r" (LitE 1)) (
      VarE "x"
      )))

test4 : ∀ {L1 L2 R C T} -> L1 , R , C , T  ⊢ ex4 :: PackedAt "Tree" "l1" "r" , L2
test4 {L1 = L1} {L2 = L2} {R = R} {C = C} {T = T} =
  LetRegionT notherer (LetLocStartT heret notherel (LetPackedT (LeafT herel LitT) (VarT heret)))

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
-- SizeOf relation

data SizeOf : Val -> ℕ -> Set where
  szStV : ∀ {st} -> SizeOf (StV st) (length st)

sztest1 : SizeOf (StV ((0 , L) ∷ (1 , I 1) ∷ [])) 2
sztest1 = szStV

-- data SizeOf : Exp -> ℕ -> Set where
--   szLeaf : ∀ {l r n } -> SizeOf (LeafE l r n) 2
--   szNode : ∀ {l r e1 e2 n1 n2} ->
--              SizeOf e1 n1 ->
--              SizeOf e2 n2 ->
--              SizeOf (NodeE l r e1 e2) (1 + n1 + n2)

-- sztest2 : ∀ {n r l1 l2 l3} -> SizeOf (NodeE l1 r (LeafE l2 r n) (LeafE l3 r n)) 5
-- sztest2 = szNode szLeaf szLeaf

-- sztest3 : ∀ {n r l1 l2 l4 l5} -> SizeOf (NodeE l1 r (LeafE l2 r n) (NodeE l5 r (LeafE l4 r n) (LeafE l5 r n))) 8
-- sztest3 = szNode szLeaf (szNode szLeaf szLeaf)

--------------------------------------------------------------------------------
-- Reduction relation (version 1)

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
                    Eval (((l2 , CurV [] (n1 + offset)) , ve) , bod) v ->
                    Eval (ve , (LetLocE l2 (AfterConstantLE offset l1) bod)) v


  LetLocAfterVR : ∀ {ve l2 l1 r1 bod v x sz} ->
                    (x , (StV r1)) ∈V ve ->
                    SizeOf (StV r1) sz ->
                    Eval (((l2 , CurV [] (1 + sz)) , ve) , bod) v ->
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
                 (StV (st ++ (o , L) ∷ [ (suc o , I nv) ]))


  NodeR : ∀ {ve l r e1 e2 stx sty st o} ->
            (r , StV st) ∈V ve ->
            (l , CurV st o) ∈V ve ->
            Eval (ve , e1) (StV stx) ->
            Eval (ve , e2) (StV sty) ->
            Eval (ve , NodeE l r e1 e2)
                 (StV (st ++ [ (o , N) ] ++ stx ++ sty))


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
         LetLocAfterVR herev szStV (
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
  -- Regions return a store, but do not have a packed type ...
  region~ : ∀ {st} -> StV st ∼ RegionTy

data _≈_ where
  e≈ : evenv ≈ etenv
  x≈ : ∀ {x y v ty ve te} ->
         x ≡ y -> v ∼ ty -> ve ≈ te -> ((x , v) , ve) ≈ ((y , ty) , te)

-- Compatible environments mean that for every variable its value is
-- compatible with its type

ρ⇒vτ : ∀ {x v ty ve te} →
       ve ≈ te -> ((x , v) ∈V ve) -> ((x , ty) ∈T te) -> v ∼ ty
ρ⇒vτ e≈ ()
ρ⇒vτ (x≈ refl v∼τ ve≈te) herev heret = v∼τ
ρ⇒vτ (x≈ refl v∼τ ve≈te) herev (skipt {α = α} inΓ) =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ve≈te) (skipv {α = α} inρ) heret =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ve≈te) (skipv inρ) (skipt inΓ) = ρ⇒vτ ve≈te inρ inΓ


Γ⇒v : ∀ {x t ve te} -> ve ≈ te -> ((x , t) ∈T te) -> Σ[ v ∈ Val ] (x , v) ∈V ve
Γ⇒v e≈ ()
Γ⇒v (x≈ refl v∼t ve≈te) heret = _ , herev
Γ⇒v (x≈ refl v∼t ve≈te) (skipt {α = α} inT) =
  let (v , inV) = Γ⇒v ve≈te inT
  in v , skipv {α = α} inV


-- | If a variable of type RegionTy bound in Γ, it also binds a store in the "value environment"
Γ⇒r : ∀ {x te ve} -> ve ≈ te -> ((x , RegionTy) ∈T te) -> Σ[ st ∈ Store ] (x , StV st) ∈V ve
Γ⇒r e≈ ()
Γ⇒r (x≈ refl region~ ve≈te) heret = _ , herev
Γ⇒r (x≈ refl region~ ve≈te) (skipt {α = α} inT) =
  let (v , inV) = Γ⇒r ve≈te inT
  in v , skipv {α = α} inV
Γ⇒r (x≈ refl num~ ve≈te) (skipt {α = α} inT) =
  let (v , inV) = Γ⇒r ve≈te inT
  in v , skipv {α = α} inV
Γ⇒r (x≈ refl cursor~ ve≈te) (skipt {α = α} inT) =
  let (v , inV) = Γ⇒r ve≈te inT
  in v , skipv {α = α} inV
Γ⇒r (x≈ refl packed~ ve≈te) (skipt {α = α} inT) =
  let (v , inV) = Γ⇒r ve≈te inT
  in v , skipv {α = α} inV


-- | If a variable of type CursorTy bound in Γ, it also binds a Cursor in the "value environment"
Γ⇒l : ∀ {x te ve} -> ve ≈ te -> ((x , CursorTy) ∈T te) -> Σ[ st ∈ Store ] (Σ[ o ∈ ℕ ] (x , CurV st o) ∈V ve)
Γ⇒l e≈ ()
Γ⇒l (x≈ refl cursor~ ve≈te) heret = _ , (_ , herev)
Γ⇒l (x≈ refl cursor~ ve≈te) (skipt {α = α} inT) =
  let (v , w , inV) = Γ⇒l ve≈te inT
  in v , w , skipv {α = α} inV
Γ⇒l (x≈ refl num~ ve≈te) (skipt {α = α} inT) =
  let (v , w , inV) = Γ⇒l ve≈te inT
  in v , w , skipv {α = α} inV
Γ⇒l (x≈ refl packed~ ve≈te) (skipt {α = α} inT) =
  let (v , w , inV) = Γ⇒l ve≈te inT
  in v , w , skipv {α = α} inV
Γ⇒l (x≈ refl region~ ve≈te) (skipt {α = α} inT) =
  let (v , w , inV) = Γ⇒l ve≈te inT
  in v , w , skipv {α = α} inV

--------------------------------------------------------------------------------
-- Type safety (version 1)

type-safety : ∀ {L1 R C T L2 e t V v} ->
                (V ≈ T) -> (L1 , R , C , T ⊢ e :: t , L2) -> Eval (V , e) v -> (v ∼ t)
type-safety ve≈te LitT LitR = num~
type-safety ve≈te (VarT x) (VarR y) = ρ⇒vτ ve≈te y x
type-safety ve≈te (LetRegionT _ tyb) (LetRegionR ev) =
  let ve'≈te' = x≈ refl region~ ve≈te
  in type-safety ve'≈te' tyb ev
type-safety ve≈te (LetLocStartT _ _ tyj) (LetLocStartR _ ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetLocAfterVT _ _ _ tyj) (LetLocAfterVR _ _ ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetLocAfterCT _ _ tyj) (LetLocAfterCR _ ev) =
  let ve'≈te' = x≈ refl cursor~ ve≈te
  in type-safety ve'≈te' tyj ev
type-safety ve≈te (LetPackedT tyj1 tyj2) (LetR ev1 ev2) =
  let v1t1 = type-safety ve≈te tyj1 ev1
      ve'≈te' = x≈ refl v1t1 ve≈te
  in type-safety ve'≈te' tyj2 ev2
-- TODO: This check is useless. Should be more strict.
type-safety ve≈te (LeafT _ _) (LeafR _ _ _) = packed~
type-safety ve≈te (NodeT _ _ _ _) (NodeR _ _ _ _) = packed~


--------------------------------------------------------------------------------
-- Progress and preservation

data Frame : Set where
  LetK  : Var -> Closure -> Frame
  LeafK : LocVar -> Region -> VEnv -> Frame
  NodeLK : LocVar -> Region -> Closure -> Frame
  NodeRK : LocVar -> Region -> Val -> Frame

Cont : Set
Cont = List Frame

data State : Set where
  Enter  : Closure -> Cont -> State
  Return : Cont -> Val -> State

-- Reduction relation (version 2)
data _↦_ : State -> State -> Set where
  LitSR : ∀ {k ve n} -> Enter (ve , LitE n) k ↦ Return k (LitV n)
  VarSR : ∀ {k ve x v} -> (x , v) ∈V ve -> Enter (ve , VarE x) k ↦ Return k v
  LetRegionSR : ∀ {k ve r bod} -> Enter (ve , LetRegionE r bod) k ↦ Enter (((r , StV []) , ve) , bod) k
  LetLocStartSR : ∀ {k ve l r st bod} ->
                    (r , (StV st)) ∈V ve ->
                    Enter (ve , LetLocE l (StartOfLE r) bod) k ↦ Enter (((l , CurV st 0) , ve) , bod) k

  LetLocAfterCSR : ∀ {ve l2 offset l1 bod k r1 n1} ->
                     (l1 , CurV r1 n1) ∈V ve ->
                     Enter (ve , LetLocE l2 (AfterConstantLE offset l1) bod) k ↦
                     Enter (((l2 , CurV [] (n1 + offset)) , ve) , bod) k

  LetLocAfterVSR : ∀ {ve l2 offset l1 bod k r1 n1 sz} ->
                     (l1 , CurV r1 n1) ∈V ve ->
                     SizeOf (StV r1) sz ->
                     Enter (ve , LetLocE l2 (AfterVariableLE offset l1) bod) k ↦
                     Enter (((l2 , CurV [] (1 + sz)) , ve) , bod) k

  LetSR   : ∀ {k ve x ty rhs bod} ->
             Enter (ve , LetE (x , ty , rhs) bod) k ↦ Enter (ve , rhs) (LetK x (ve , bod) ∷ k)

  LetKR  : ∀ {ve k x bod v} ->
             Return (LetK x (ve , bod) ∷ k) v ↦ Enter (((x , v) , ve) , bod) k

  LeafSR : ∀ {k ve l r e} ->
            Enter (ve , LeafE l r e) k ↦ Enter (ve , e) (LeafK l r ve ∷ k)

  LeafKR : ∀ {k ve l r st o n} ->
             (r , StV st) ∈V ve ->
             (l , CurV st o) ∈V ve ->
             Return ((LeafK l r ve) ∷ k) (LitV n) ↦ Return k (StV (st ++ (o , L) ∷ [ (suc o , I n) ]))

  NodeSR : ∀ {l r x y ve k} ->
             Enter (ve , NodeE l r x y) k ↦ Enter (ve , x) (NodeLK l r (ve , y) ∷ k)

  NodeLKR : ∀ {l r y ve k stx} ->
              Return (NodeLK l r (ve , y) ∷ k) stx ↦ Enter (ve , y) (NodeRK l r stx ∷ k)

  NodeRKR : ∀ {l r stx sty st o ve k} ->
              (r , StV st) ∈V ve ->
              (l , CurV st o) ∈V ve ->
              Return (NodeRK l r (StV stx) ∷ k) (StV sty) ↦ Return k (StV (st ++ L.[ (o , N) ] ++ stx ++ sty))


--------------------------------------------------------------------------------

infixr 10 _•_

data _↦*_ : State -> State -> Set where
  ∎   : ∀ {s} -> s ↦* s
  _•_ : ∀ {s₁ s₂ s₃} -> s₁ ↦ s₂ -> s₂ ↦* s₃ -> s₁ ↦* s₃

SEval : Exp -> Val -> Set
SEval e v = Enter (evenv , e) [] ↦* (Return [] v)

srtest4 : SEval ex4 (StV ((0 , L) ∷ (1 , I 1) ∷ []))
srtest4 = LetRegionSR • LetLocStartSR herev • LetSR • LeafSR • LitSR • LeafKR (skipv herev) herev •
          LetKR • VarSR herev • ∎

--------------------------------------------------------------------------------

-- Closure typing cl ⊢c τ
_,_,_,_⊢c_,_ : LEnv -> REnv -> CEnv -> Closure -> Ty -> LEnv -> Set
le , re , ce , (ve , e) ⊢c t , le2 = Σ[ te ∈ TEnv ] (ve ≈ te × (le , re , ce , te ⊢ e :: t , le2))

extend : Closure -> String -> Val -> Closure
extend (ve , e) x v = (((x , v) , ve) , e)

-- Frame typing fr ⊢f (τ , τ)
data _⊢f_ : Frame -> (Ty × Ty) -> Set where
  LetKT : ∀ {x cl t1 t2 L R C L2} ->
            (∀ {v1} -> (v1 ∼ t1) -> L , R , C , (extend cl x v1) ⊢c t2 , L2) ->
            LetK x cl ⊢f (t1 , t2)

  LeafKT : ∀ {l r ve} ->
             LeafK l r ve ⊢f (IntTy , PackedAt "Tree" l r)

  NodeLKT : ∀ {L1 L2 R C l y ve r l1 l2} ->
              L1 , R , C , (ve , y) ⊢c PackedAt "Tree" l2 r , L2 ->
              NodeLK l r (ve , y) ⊢f (PackedAt "Tree" l1 r , PackedAt "Tree" l r)

  NodeRKT : ∀ {l r stx l1 l2} ->
              (stx ∼ PackedAt "Tree" l1 r) ->
              NodeRK l r stx ⊢f (PackedAt "Tree" l2 r , PackedAt "Tree" l r)


-- Continuation typing κ ⊢κ (τ , τ)
data _⊢k_ : Cont -> (Ty × Ty) -> Set where
  EmptyKT : ∀ {t} ->
    [] ⊢k (t , t)
  PushKT  : ∀ {fr κ t1 t2 t3} ->
    fr ⊢f (t1 , t2) ->
    κ ⊢k (t2 , t3) ->
    (fr ∷ κ) ⊢k (t1 , t3)

-- State typing
data _⊢s_ : State -> Ty -> Set where
  EnterT  : ∀ {cl κ τ₁ τ₂ L R C L2} ->
    L , R , C , cl ⊢c τ₁ , L2 ->
    κ ⊢k (τ₁ , τ₂) ->
    (Enter cl κ) ⊢s τ₂
  ReturnT : ∀ {κ v τ₁ τ₂} ->
    κ ⊢k (τ₁ , τ₂) ->
    v ∼ τ₁ ->
    Return κ v ⊢s τ₂

loadT : ∀ {L1 L2 R C e t} -> (L1 , R , C , etenv ⊢ e :: t , L2) -> (Enter (evenv , e) []) ⊢s t
loadT et = EnterT (etenv , e≈ , et) EmptyKT

data Final : State -> Ty -> Set where
  F : ∀ {v τ} -> (v ∼ τ) -> Final (Return [] v) τ

--------------------------------------------------------------------------------

-- Progress
-- If we are well-typed and not final then we can make some progress

progress : ∀ {s τ} -> s ⊢s τ -> (Final s τ) ⊎ (Σ[ s' ∈ State ] s ↦ s')
progress (EnterT (te , ve≈te , LitT) kt) = inj₂ (_ , LitSR)
progress (EnterT (te , ve≈te , VarT inT) kt) = inj₂ (_ , VarSR (proj₂ (Γ⇒v ve≈te inT)))
progress (EnterT (te , ve≈te , LetRegionT _ _) kt) = inj₂ (_ , LetRegionSR)
progress (EnterT (te , ve≈te , LetLocStartT inT _ _) kt) = inj₂ (_ , LetLocStartSR (proj₂ (Γ⇒r ve≈te inT)))
progress (EnterT (te , ve≈te , LetLocAfterVT _ inT _ _) kt) =
  inj₂ (_ , (LetLocAfterVSR (proj₂ (proj₂ (Γ⇒l ve≈te inT))) szStV))
progress (EnterT (te , ve≈te , LetLocAfterCT y _ x) kt) = inj₂ (_ , (LetLocAfterCSR (proj₂ (proj₂ (Γ⇒l ve≈te y)))))
progress (EnterT (te , ve≈te , LetPackedT _ _) kt) = inj₂ (_ , LetSR)
progress (EnterT (te , ve≈te , LeafT _ _) kt) = inj₂ (_ , LeafSR)
progress (EnterT (te , ve≈te , NodeT tyjx tyjy c1 c2) kt) = inj₂ (_ , NodeSR)
progress (ReturnT EmptyKT v∼t) = inj₁ (F v∼t)
progress (ReturnT (PushKT (LetKT _) _) kt) = inj₂ (_ , LetKR)
progress (ReturnT (PushKT LeafKT x) num~) = inj₂ (_ , LeafKR {!!} {!!})
progress (ReturnT (PushKT (NodeLKT _) _) _) = inj₂ (_ , NodeLKR)
progress (ReturnT (PushKT (NodeRKT packed~) kt) packed~) = inj₂ (_ , NodeRKR {!!} {!!})

-- Preservation
-- If we are well-typed and make a step then the next state is also
-- well-typed

preservation : ∀ {s s' τ} -> s ↦ s' -> s ⊢s τ -> s' ⊢s τ
preservation LitSR (EnterT (te , ve≈te , LitT) kt) = ReturnT kt num~
preservation (VarSR y) (EnterT (te , ve≈te , VarT inT) kt) =
  ReturnT kt (ρ⇒vτ ve≈te y inT)
preservation LetRegionSR (EnterT (te , ve≈te , LetRegionT (notherer {r = r}) tyj) kt) =
  EnterT (((r , RegionTy) , te) , x≈ refl region~ ve≈te , tyj) kt
preservation (LetLocStartSR _) (EnterT (te , ve≈te , LetLocStartT _ (notherel {l = l}) tyj) kt) =
  EnterT (((l , CursorTy) , te) , x≈ refl cursor~ ve≈te , tyj) kt
preservation (LetLocAfterCSR _) (EnterT (te , ve≈te , LetLocAfterCT _ (notherel {l = l}) tyj) kt) =
  EnterT (((l , CursorTy) , te) , (x≈ refl cursor~ ve≈te) , tyj) kt
preservation (LetLocAfterVSR _ _) (EnterT (te , ve≈te , LetLocAfterVT _ _ (notherel {l = l}) tyj) kt) =
  EnterT (((l , CursorTy) , te) , x≈ refl cursor~ ve≈te , tyj ) kt
preservation LetSR (EnterT (te , ve≈te , LetPackedT tyj tyj2) kt) =
  EnterT (te , ve≈te , tyj) (PushKT (LetKT λ v∼t → (_ , te) , (x≈ refl v∼t ve≈te) , tyj2) kt)
preservation LetKR (ReturnT (PushKT (LetKT pct) kt) v∼t) = EnterT (pct v∼t) kt
preservation LeafSR (EnterT (te , ve≈te , LeafT x tyj) kt) =
  EnterT (te , ve≈te , tyj) (PushKT LeafKT kt)
preservation (LeafKR _ _) (ReturnT (PushKT LeafKT kt) v∼t) = ReturnT kt packed~
preservation NodeSR (EnterT (te , ve≈te , NodeT tyj1 tyj2 _ _) kt) =
  EnterT (te , ve≈te , tyj1) (PushKT (NodeLKT (te , ve≈te , tyj2)) kt)
preservation NodeLKR (ReturnT (PushKT (NodeLKT (te , ve≈te , tyj)) kt) vt) =
  EnterT (te , ve≈te , tyj) (PushKT (NodeRKT vt) kt)
preservation (NodeRKR _ _) (ReturnT (PushKT (NodeRKT _) kt) packed~) =
  ReturnT kt packed~


-- Main theorem

-- If we are well-typed, then either
--   - we are final
--   - we can make a step and the next state has the same type
--   - we diverge (at least as far as Agda is concerned)

type-safety-step : ∀ {s τ} → s ⊢s τ →
  Final s τ ⊎ Σ[ s' ∈ State ] (s ↦ s' × s' ⊢s τ)
type-safety-step st with progress st
type-safety-step st | inj₁ f = inj₁ f
type-safety-step st | inj₂ (s' , step) =
  inj₂ (s' , step , preservation step st)

{-# TERMINATING #-}
type-safety-step* : ∀ {s τ} → s ⊢s τ →
                    Σ[ s' ∈ State ] (s ↦* s' × Final s' τ)
type-safety-step* st with type-safety-step st
... | inj₁ f = _ , ∎ , f
... | inj₂ (s' , step , s't) =
  let (sf , steps , f) = type-safety-step* s't
  in sf , step • steps , f

-- Type safety (version 2)
type-safety2 : ∀ {e τ L1 L2 C R} -> (L1 , C , R , etenv ⊢ e :: τ , L2) -> Σ[ v ∈ Val ] (SEval e v) × (v ∼ τ)
type-safety2 et with type-safety-step* (loadT et)
... | (Return [] v) , steps , F vτ = v , steps , vτ
