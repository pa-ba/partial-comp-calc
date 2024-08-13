{-# OPTIONS --copatterns --sized-types --guardedness #-}


------------------------------------------------------------------------
-- Calculation for Simply RaTT
------------------------------------------------------------------------

module Calculations.Stack.RaTT where


open import CTree hiding (τ) public
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat
open import Data.Unit
open import Agda.Builtin.Nat
open import Data.Bool 
open import Data.Product
open import Data.List renaming (lookup to lookupL ; map to mapL)
open import Data.List.Properties
open import Function

----------------------------
-- Source language syntax --
----------------------------

Location : Set
Location = ℕ


data Expr : Set where
  Delay : Expr → Expr
  Adv : Expr → Expr
  Num : ℕ → Expr
  Add : Expr → Expr → Expr
  Abs : Expr → Expr
  App : Expr → Expr → Expr
  Fix : Expr
  Var : ℕ → Expr
  Box : Expr → Expr
  Unbox : Expr → Expr
  Pair : Expr → Expr → Expr
  Pr1 : Expr → Expr
  Pr2 : Expr → Expr
  Inl : Expr → Expr
  Inr : Expr → Expr
  Case : Expr → Expr → Expr → Expr


mutual
  data Value : Set where
    NumV : ℕ → Value
    CloV : Expr → Env → Value
    LocV : Location → Value
    BoxV : Expr → Env → Value
    PairV : Value → Value → Value
    InlV : Value → Value
    InrV : Value → Value

  Env : Set
  Env = List Value

Partial : Set → Size → Set₁
Partial A i = CTree⊥ None A i

∞Partial : Set → Size → Set₁
∞Partial A i = ∞CTree⊥ None A i

---------------------------
-- eliminators for Value --
---------------------------

getNum : ∀ {i} → Value → Partial ℕ i
getNum (NumV n) = return n
getNum _ = stuck

getLoc : ∀ {i} → Value → Partial Location i
getLoc (LocV l) = return l
getLoc _ = stuck

getClo : ∀ {i} → Value → Partial (Expr × Env) i
getClo (CloV x e) = return (x , e)
getClo _ = stuck

getBox : ∀ {i} → Value → Partial (Expr × Env) i
getBox (BoxV x e) = return (x , e)
getBox _ = stuck

getPair : ∀ {i} → Value → Partial (Value × Value) i
getPair (PairV v1 v2) = return (v1 , v2)
getPair _ = stuck

caseSum : ∀ {A i} → Value → (Value → Partial A i) → (Value → Partial A i) → Partial A i
caseSum (InlV v) k1 k2 = k1 v
caseSum (InrV v) k1 k2 = k2 v
caseSum _ _ _ = stuck

----------------------
-- heaps and stores --
----------------------

Heap : Set → Set
Heap A = List A

alloc : ∀ {A} → Heap A → A → (Location × Heap A)
alloc η v =  length η , η ++ [ v ]

lookup : ∀ {A i} → List A → ℕ → Partial A i
lookup [] l = stuck
lookup (x ∷ η) zero = return x
lookup (x ∷ η) (suc l) = lookup η l


data Store (A : Set) : Set where
  ⟨_✓_⟩ : Heap A → Heap A → Store A
  ⟨_⟩ : Heap A → Store A


allocS : ∀ {A} → Store A → A → (Location × Store A)
allocS ⟨ ηN ✓ ηL ⟩ v with l , ηL' ← alloc ηL v = l , ⟨ ηN ✓ ηL' ⟩
allocS ⟨ ηN ⟩ v with l , ηN' ← alloc ηN v = l , ⟨ ηN' ⟩
  
lookupS : ∀ {A i} → Store A → Location → Partial A i
lookupS ⟨ ηN ✓ ηL ⟩ l = lookup ηL l
lookupS ⟨ ηN ⟩ l = lookup ηN l



getSingleHeap : ∀ {A i} → Store A → Partial (Heap A) i
getSingleHeap ⟨ η ⟩ = return η
getSingleHeap _ = stuck

HElem : Set
HElem = Expr × Env

-------------------------------
-- source language semantics --
-------------------------------

mutual
  eval : ∀ {i} → Expr → Env → Store HElem → Partial (Value × Store HElem) i
  eval (Delay t) e σ = let l , σ' = allocS σ (t , e)
                       in return (LocV l , σ')
  eval (Adv t) e ⟨ ηN ✓ ηL ⟩ = do v , σ ← eval t  e ⟨ ηN ⟩
                                  l ← getLoc v
                                  ηN' ← getSingleHeap σ
                                  t' , e' ← lookup ηN' l
                                  later (∞eval t' e' ⟨ ηN' ✓ ηL ⟩)
  eval (Adv t) e ⟨ _ ⟩  = stuck
  eval (Num n) e σ = return (NumV n , σ)
  eval (Add t1 t2) e σ = do v1 , σ1 ← eval t1 e σ
                            n1 ← getNum v1
                            v2 , σ2 ← eval t2 e σ1
                            n2 ← getNum v2
                            return (NumV (n1 + n2) , σ2)
  eval (Abs t) e σ = return (CloV t e , σ)
  eval (App t1 t2) e σ = do v1 , σ1 ← eval t1 e σ
                            t1' , e' ← getClo v1
                            v2 , σ2 ← eval t2 e σ1
                            later (∞eval t1' (v2 ∷ e') σ2)
  eval Fix e σ = return (CloV (App (Var 0) (Box (Delay (App Fix (Var 0))))) e , σ)
--  eval t (BoxV (Delay (Fix t)) e ∷ e) σ
  eval (Var x) e σ = do v ← lookup e x
                        return (v , σ)
  eval (Box t) e σ = return (BoxV t e , σ)
  eval (Unbox t) e σ = do v , σ' ← eval t e σ
                          t' , e' ← getBox v
                          later (∞eval t' e' σ')
  eval (Pair t1 t2) e σ =  do v1 , σ1 ← eval t1 e σ
                              v2 , σ2 ← eval t2 e σ1
                              return (PairV v1 v2 , σ2)
  eval (Pr1 t) e σ = do v , σ' ← eval t e σ
                        v1 , v2 ← getPair v
                        return (v1 , σ')
  eval (Pr2 t) e σ = do v , σ' ← eval t e σ
                        v1 , v2 ← getPair v
                        return (v2 , σ')
  eval (Inl t) e σ = do v , σ' ← eval t e σ
                        return (InlV v , σ')
  eval (Inr t) e σ = do v , σ' ← eval t e σ
                        return (InrV v , σ')
  eval (Case t t1 t2) e σ = do v , σ' ← eval t e σ
                               caseSum v (λ vl → eval t1 (vl ∷ e) σ') (λ vr → eval t2 (vr ∷ e) σ')

  ∞eval : ∀ {i} → Expr → Env → Store (Expr × Env) → ∞Partial (Value × Store (Expr × Env)) i
  force (∞eval t e σ) = eval t e σ


---------------------
-- Target language --
---------------------

data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  PAIR : Code → Code
  PR1 : Code → Code
  PR2 : Code → Code
  INL : Code → Code
  INR : Code → Code
  ENDCASE : Code → Code
  CASE : Code → Code → Code  
  LOOKUP : ℕ → Code → Code
  RET : Code
  APP : Code → Code
  ABS : Code → Code → Code
  ENDADV : Code → Code
  ADV : Code → Code
  DELAY : Code → Code → Code
  UNBOX : Code → Code
  BOX : Code → Code → Code
  FIX : Code → Code
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'
    Box' : Code → Env' → Value'
    Loc' : ℕ → Value'
    Pair' : Value' → Value' → Value'
    Inl' : Value' → Value'
    Inr' : Value' → Value'

  Env' : Set
  Env' = List Value'
  

data Elem : Set where
  VAL : Value' → Elem
  HEAP : Heap (Code × Env') → Elem
  CLO : Code → Env' → Elem

---------------------
-- virtual machine --
---------------------

Stack : Set
Stack = List Elem

HElem' : Set
HElem' = Code × Env'

Conf : Set
Conf = Stack × Env' × Store HElem'

mutual
  {-# TERMINATING #-}
  exec : ∀ {i} → Code → Conf → Partial Conf i
  exec (PUSH n c) (s , e , σ) = exec c (VAL (Num' n) ∷ s , e , σ)
  exec (ADD c) (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e , σ) = exec c (VAL (Num' (m + n)) ∷ s , e , σ)
  exec (PAIR c) (VAL v2 ∷ VAL v1 ∷ s , e , σ) = exec c (VAL (Pair' v1 v2) ∷ s , e , σ)  
  exec (PR1 c) (VAL (Pair' v1 v2) ∷ s , e , σ) = exec c (VAL v1 ∷ s , e , σ)
  exec (PR2 c) (VAL (Pair' v1 v2) ∷ s , e , σ) = exec c (VAL v2 ∷ s , e , σ)
  exec (INL c) (VAL v ∷ s , e , σ) = exec c (VAL (Inl' v) ∷ s , e , σ)
  exec (INR c) (VAL v ∷ s , e , σ) = exec c (VAL (Inr' v) ∷ s , e , σ)  
  exec (LOOKUP n c) (s , e , σ) = do v <- lookup e n
                                     exec c (VAL v ∷ s , e , σ)
  exec RET  (VAL u ∷ CLO c e' ∷ s , _ , σ) = exec c (VAL u ∷ s , e' , σ)
  exec (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e , σ) = later (∞exec c' (CLO c e ∷ s , v ∷ e' , σ))
  exec (ABS c' c) (s , e , σ) = exec c (VAL (Clo' c' e) ∷ s , e , σ)
  exec HALT c = return c
  exec (ADV c) (s , e , ⟨ ηN ✓ ηL ⟩) =  exec c (HEAP ηL ∷ s , e , ⟨ ηN ⟩)
  exec (ENDADV c) (VAL (Loc' l) ∷ HEAP ηL ∷ s , e , ⟨ ηN ⟩) =
    do c' , e' ← lookup ηN l
       later (∞exec c' (CLO c e ∷ s , e' , ⟨ ηN ✓ ηL ⟩))
  exec (DELAY c' c) (s , e , σ) =
    let l , σ' = allocS σ (c' , e)
    in exec c (VAL (Loc' l) ∷ s , e , σ')
  exec (UNBOX c) (VAL (Box' c' e') ∷ s , e , σ) = later (∞exec c' (CLO c e ∷ s , e' , σ))
  exec (BOX c' c) (s , e , σ) = exec c (VAL (Box' c' e) ∷ s , e , σ)
  exec (FIX c) (s , e , σ) = exec c (VAL (Clo' (LOOKUP 0 (BOX (DELAY (FIX (LOOKUP 0 (APP RET))) RET) (APP RET))) e) ∷ s , e , σ)
  exec (ENDCASE c) (s , v ∷ e , σ) = exec c (s , e , σ)
  exec (CASE c1 c2) (VAL (Inl' v) ∷ s , e , σ) = exec c1 (s , v ∷ e , σ)
  exec (CASE c1 c2) (VAL (Inr' v) ∷ s , e , σ) = exec c2 (s , v ∷ e , σ)    
  exec _ _ = stuck


  ∞exec : ∀ {i} → Code → Conf → ∞Partial Conf i
  force (∞exec c e) = exec c e


--------------
-- Compiler --
--------------

comp : Expr → Code → Code
comp (Num n) c = PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (Adv x) c = (ADV (comp x (ENDADV c)))
comp (Delay x) c = DELAY (comp x RET) c
comp (Unbox x) c = comp x (UNBOX c)
comp (Box x) c = BOX (comp x RET) c
comp (App x y) c = comp x (comp y (APP c))
comp (Abs x) c = ABS (comp x RET) c
comp (Var n) c = LOOKUP n c
comp (Fix) c = FIX c
comp (Pair x y) c = comp x (comp y (PAIR c))
comp (Pr1 x) c = comp x (PR1 c)
comp (Pr2 x) c = comp x (PR2 c)
comp (Inl x) c = comp x (INL c)
comp (Inr x) c = comp x (INR c)
comp (Case x x1 x2) c = comp x (CASE (comp x1 (ENDCASE c)) (comp x2 (ENDCASE c)))

----------------------------------------------
-- conversion functions (for compiler spec) --
----------------------------------------------

mutual
  conv : Value → Value'
  conv (CloV x' e') = Clo' (comp x' RET) (convE e')
  conv (NumV n) = Num' n
  conv (LocV l) = Loc' l
  conv (BoxV x' e') = Box' (comp x' RET) (convE e')
  conv (PairV x y) = Pair' (conv x) (conv y)
  conv (InlV x) = Inl' (conv x)
  conv (InrV x) = Inr' (conv x)  
  
  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs

convHE : HElem → HElem'
convHE (t , e) = (comp t RET , convE e)

convH : Heap HElem → Heap HElem'
convH η = mapL convHE η

convS : Store HElem → Store HElem'
convS ⟨ ηN ✓ ηL ⟩ = ⟨ convH ηN ✓ convH ηL ⟩
convS ⟨ ηN ⟩ = ⟨ convH ηN ⟩

------------
-- lemmas --
------------

getSingleHeap-conv : ∀ {i A} σ → (f : Heap (Code × Env') → Partial A ∞) →
  (getSingleHeap σ >>= (f ∘ convH)) ~[ i ] (getSingleHeap (convS σ) >>= f)
getSingleHeap-conv ⟨ x ✓ x₁ ⟩ f = ~istuck-refl
getSingleHeap-conv ⟨ x ⟩ f = ~irefl

lookup-convE : ∀ {i A} n e → (f : Value' → Partial A ∞) →
  (lookup e n >>= (f ∘ conv)) ~[ i ] (lookup (convE e) n >>= f)
lookup-convE zero (x ∷ e) f =  ~irefl
lookup-convE (suc n) (x ∷ e) f = lookup-convE n e f
lookup-convE (suc n) [] f = ~istuck-refl
lookup-convE zero [] f = ~istuck-refl


lookup-convH : ∀ {i A} n e → (f : Code × Env' → Partial A ∞) →
  (lookup e n >>= (λ (t , e) → f (comp t RET , convE e) )) ~[ i ] (lookup (convH e) n >>= f)
lookup-convH zero (x ∷ e) f =  ~irefl
lookup-convH (suc n) (x ∷ e) f = lookup-convH n e f
lookup-convH (suc n) [] f = ~istuck-refl
lookup-convH zero [] f = ~istuck-refl


allocS-conv : ∀ {l} {A : Set l} σ (e : HElem) → (f : Location × Store HElem' → A) →
  (let l , σ' = allocS σ e in f (l , convS σ') ) ≡ (f (allocS (convS σ) (convHE e)))
allocS-conv ⟨ ηN ✓ ηL ⟩ e f
  rewrite length-map convHE ηN rewrite map-++-commute convHE ηN [ e ]
  rewrite length-map convHE ηL rewrite map-++-commute convHE ηL [ e ] =  refl
allocS-conv ⟨ η ⟩ e f rewrite length-map convHE η rewrite map-++-commute convHE η [ e ] =  refl


--------------------------
-- compiler calculation --
--------------------------

open ⊥~i-Calculation

spec : ∀ i x {s c e σ} →
  (do v , σ' ← eval x e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~[ i ]
  (exec (comp x c) (s , convE e , convS σ))
spec zero _ =  ⊥~izero
spec i (Num x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Num x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (exec (comp (Num x) c) (s , convE e , convS σ))
  ∎

spec i (Add x y) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Add x y) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← (do v1 , σ1 ← eval x e σ
                   n1 ← getNum v1
                   v2 , σ2 ← eval y e σ1
                   n2 ← getNum v2
                   return (NumV (n1 + n2), σ2))
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc' (eval x e σ) (λ (v1 , σ1) →
     ~i>>=-assoc' (getNum v1) (λ n1 →
     ~i>>=-assoc' (eval y e σ1) (λ (v2 , σ2) →
     ~i>>=-assoc (getNum v2))))⟩
  (do v1 , σ1 ← eval x e σ
      n1 ← getNum v1
      v2 , σ2 ← eval y e σ1
      n2 ← getNum v2
      exec c (VAL (Num' (n1 + n2)) ∷ s , convE e , convS σ2))
  ≡⟨⟩
  (do v1 , σ1 ← eval x e σ
      n1 ← getNum v1
      v2 , σ2 ← eval y e σ1
      n2 ← getNum v2
      exec (ADD c) (VAL (Num' n2) ∷ VAL (Num' n1) ∷ s , convE e , convS σ2))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e σ) (λ { (NumV _ , _) → ⊥~irefl ; (CloV _ _ , _) → ⊥~istuck ; (LocV _ , _) → ⊥~istuck ;
      (BoxV _ _ , _) → ⊥~istuck ; (PairV _ _ , _) → ⊥~istuck ; (InlV _ , _) → ⊥~istuck ; (InrV _ , _) → ⊥~istuck}) ⟩
  (do v1 , σ1 ← eval x e σ
      v2 , σ2 ← eval y e σ1
      n2 ← getNum v2
      exec (ADD c) (VAL (Num' n2) ∷ VAL (conv v1) ∷ s , convE e , convS σ2))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e σ) (λ (v1 , σ1) → 
      ⊥~i>>=-cong-r (eval y e σ1) 
         (λ {(NumV m , _) → ⊥~irefl; (CloV _ _ , _) → ⊥~istuck ; (LocV _ , _) → ⊥~istuck ;
      (BoxV _ _ , _) → ⊥~istuck ; (PairV _ _ , _) → ⊥~istuck ; (InlV _ , _) → ⊥~istuck ; (InrV _ , _) → ⊥~istuck })) ⟩
  (do v1 , σ1 ← eval x e σ
      v2 , σ2 ← eval y e σ1
      exec (ADD c) (VAL (conv v2) ∷ VAL (conv v1) ∷ s , convE e , convS σ2))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e σ) (λ (v1 , σ1) → spec i y) ⟩
  (do v1 , σ1 ← eval x e σ
      exec (comp y (ADD c)) (VAL (conv v1) ∷ s , convE e , convS σ1))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (comp y (ADD c))) (s , convE e , convS σ))
  ∎  

spec (suc i) (Adv x) {s} {c} {e} { ⟨ ηN ⟩ } = ⊥~istuck
spec (suc i) (Adv x) {s} {c} {e} { ⟨ ηN ✓ ηL ⟩ } =
  (do v , σ' ← eval (Adv x) e ⟨ ηN ✓ ηL ⟩
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v , σ ← eval x  e ⟨ ηN ⟩
                  l ← getLoc v
                  ηN' ← getSingleHeap σ
                  t' , e' ← lookup ηN' l
                  later (∞eval t' e' ⟨ ηN' ✓ ηL ⟩)
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc' (eval x e ⟨ ηN ⟩) (λ (v , σ) →
     ~i>>=-assoc' (getLoc v) λ l → 
     ~i>>=-assoc' (getSingleHeap σ) λ ηN' → 
     ~i>>=-assoc' (lookup ηN' l) λ _ → ~irefl) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩  
      l ← getLoc v
      ηN' ← getSingleHeap σ
      t' , e' ← lookup ηN' l
      later (∞eval t' e' ⟨ ηN' ✓ ηL ⟩ ∞>>= λ (v , σ') →
                exec c (VAL (conv v) ∷ s , convE e , convS σ')))
  ≡⟨⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      l ← getLoc v
      ηN' ← getSingleHeap σ
      t' , e' ← lookup ηN' l
      later (∞eval t' e' ⟨ ηN' ✓ ηL ⟩ ∞>>= λ (v , σ') →
                exec RET (VAL (conv v) ∷ CLO c (convE e) ∷ s , convE e' , convS σ')))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e ⟨ ηN ⟩) (λ (v , σ) →
     ⊥~i>>=-cong-r (getLoc v) λ l → 
     ⊥~i>>=-cong-r (getSingleHeap σ) λ ηN' → 
     ⊥~i>>=-cong-r (lookup ηN' l) λ (t' , e') →
     ⊥~ilater (spec i t')) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      l ← getLoc v
      ηN' ← getSingleHeap σ
      t' , e' ← lookup ηN' l
      later (∞exec (comp t' RET) (CLO c (convE e) ∷ s , convE e' , convS ⟨ ηN' ✓ ηL ⟩)))
  ~⟨ ~i>>=-cong-r (eval x e ⟨ ηN ⟩) (λ (v , σ) →
     ~i>>=-cong-r (getLoc v) λ l → 
     ~i>>=-cong-r (getSingleHeap σ) λ ηN' → 
     lookup-convH l ηN' _) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      l ← getLoc v
      ηN' ← getSingleHeap σ
      c' , e' ← lookup (convH ηN') l
      later (∞exec c' (CLO c (convE e) ∷ s , e' , convS ⟨ ηN' ✓ ηL ⟩)))
  ~⟨ ~i>>=-cong-r (eval x e ⟨ ηN ⟩) (λ (v , σ) →
     ~i>>=-cong-r (getLoc v) λ l → 
     getSingleHeap-conv σ _) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      l ← getLoc v
      ηN' ← getSingleHeap (convS σ)
      c' , e' ← lookup ηN' l
      later (∞exec c' (CLO c (convE e) ∷ s , e' , ⟨ ηN' ✓ convH ηL ⟩)))
  ~⟨ ~i>>=-cong-r (eval x  e ⟨ ηN ⟩) (λ { (v , ⟨ x ✓ x₁ ⟩)
    → ~i>>=-cong-r (getLoc v) λ _ → ~istuck-refl ; (v , ⟨ x ⟩) → ~irefl}) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      l ← getLoc v
      exec (ENDADV c) (VAL (Loc' l) ∷ HEAP (convH ηL) ∷ s , convE e , convS σ))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x  e ⟨ ηN ⟩)
    (λ { (NumV x , _) → ⊥~istuck ; (CloV x x₁ , _) → ⊥~istuck ; (LocV x , _) → ⊥~irefl ; (BoxV x x₁ , _) → ⊥~istuck ;
      (PairV v v₁ , _) → ⊥~istuck ; (InlV v , _) → ⊥~istuck ; (InrV v , _) → ⊥~istuck }) ⟩
  (do v , σ ← eval x  e ⟨ ηN ⟩
      exec (ENDADV c) (VAL (conv v) ∷  HEAP (convH ηL) ∷ s , convE e , convS σ))
  ⊥~⟨ spec (suc i) x  ⟩
  (exec (comp x (ENDADV c)) (HEAP (convH ηL) ∷ s , convE e , convS ⟨ ηN ⟩))
  ≡⟨⟩
  (exec (ADV (comp x (ENDADV c))) (s , convE e , convS ⟨ ηN ✓ ηL ⟩))
  ∎


spec i (Delay x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Delay x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (let l , σ' = allocS σ (x , e)
   in exec c (VAL (Loc' l) ∷ s , convE e , convS σ'))
  ~⟨ ~i≡ (allocS-conv σ (x , e) (λ (l , σ') → exec c (VAL (Loc' l) ∷ s , convE e , σ'))) ⟩
  (let l , σ' = allocS (convS σ) (convHE (x , e))
   in exec c (VAL (Loc' l) ∷ s , convE e , σ'))
  ≡⟨⟩
  (let l , σ' = allocS (convS σ) (comp x RET , convE e)
   in exec c (VAL (Loc' l) ∷ s , convE e , σ'))
  ≡⟨⟩
  (exec (DELAY (comp x RET) c) (s , convE e , convS σ))
  ∎


spec (suc i) (Unbox x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Unbox x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v , σ' ← eval x e σ
                  x' , e' ← getBox v
                  later (∞eval x' e' σ')
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ( ~i>>=-assoc' (eval x e σ) λ (v , σ') →
     ~i>>=-assoc (getBox v)) ⟩
  (do v , σ' ← eval x e σ
      x' , e' ← getBox v
      later (∞eval x' e' σ' ∞>>= (λ (v , σ') →
        exec c (VAL (conv v) ∷ s , convE e , convS σ'))))
  ≡⟨⟩
  (do v , σ' ← eval x e σ
      x' , e' ← getBox v
      later (∞eval x' e' σ' ∞>>= (λ (v , σ') →
        exec RET (VAL (conv v) ∷ CLO c (convE e) ∷ s , convE e' , convS σ'))))
  ⊥~⟨ (⊥~i>>=-cong-r (eval x e σ) λ (v , σ') →
     ⊥~i>>=-cong-r (getBox v) λ (x' , e') → ⊥~ilater (spec i x')) ⟩
  (do v , σ' ← eval x e σ
      x' , e' ← getBox v
      later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE e' , convS σ')))
  ≡⟨⟩
  (do v , σ' ← eval x e σ
      x' , e' ← getBox v
      exec (UNBOX c) (VAL (Box' (comp x' RET) (convE e')) ∷ s , convE e , convS σ'))
  ⊥~⟨ ((⊥~i>>=-cong-r (eval x e σ)
    λ { (NumV x , σ') → ⊥~istuck ; (CloV _ _ , σ') → ⊥~istuck ; (LocV x , σ') → ⊥~istuck ; (BoxV _ _ , σ') → ⊥~irefl ;
      (PairV _ _ , σ') → ⊥~istuck ; (InlV _ , σ') → ⊥~istuck ; (InrV _ , σ') → ⊥~istuck})) ⟩
  (do v , σ' ← eval x e σ
      exec (UNBOX c) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec (suc i) x ⟩
  (exec (comp x (UNBOX c)) (s , convE e , convS σ))
  ∎


spec i (Box x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Box x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← return (BoxV x e , σ)
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (exec c (VAL (Box' (comp x RET) (convE e)) ∷ s , convE e , convS σ))
  ≡⟨⟩
  (exec (BOX (comp x RET) c) (s , convE e , convS σ))
  ∎

spec i@(suc j) (App x y) {s} {c} {e} {σ} =
  (do v , σ' ← eval (App x y) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v1 , σ1 ← eval x e σ
                  x' , e' ← getClo v1
                  v2 , σ2 ← eval y e σ1
                  later (∞eval x' (v2 ∷ e') σ2)
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ (~i>>=-assoc' (eval x e σ) λ (v1 , σ1) →
      ~i>>=-assoc' (getClo v1) λ (x' , e') →
      ~i>>=-assoc (eval y e σ1)) ⟩
  (do v1 , σ1 ← eval x e σ
      x' , e' ← getClo v1
      v2 , σ2 ← eval y e σ1
      later (∞eval x' (v2 ∷ e') σ2 ∞>>= λ (v , σ') →
        exec c (VAL (conv v) ∷ s , convE e , convS σ')))
  ≡⟨⟩
  (do v1 , σ1 ← eval x e σ
      x' , e' ← getClo v1
      v2 , σ2 ← eval y e σ1
      later (∞eval x' (v2 ∷ e') σ2 ∞>>= λ (v , σ') →
        exec RET (VAL (conv v) ∷ CLO c (convE e) ∷ s , convE (v2 ∷ e') , convS σ')))
  ⊥~⟨ ( (⊥~i>>=-cong-r (eval x e σ) λ (v1 , σ1) →
      ⊥~i>>=-cong-r (getClo v1) λ (x' , e') →
      ⊥~i>>=-cong-r (eval y e σ1) λ (v2 , σ2) →
      ⊥~ilater (spec j x'))) ⟩
  (do v1 , σ1 ← eval x e σ
      x' , e' ← getClo v1
      v2 , σ2 ← eval y e σ1
      later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE (v2 ∷ e') , convS σ2)))
  ≡⟨⟩
  (do v1 , σ1 ← eval x e σ
      x' , e' ← getClo v1
      v2 , σ2 ← eval y e σ1
      exec (APP c) (VAL (conv v2) ∷ VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e , convS σ2))
  ⊥~⟨ (⊥~i>>=-cong-r (eval x e σ)
    λ { (NumV x , σ1) → ⊥~istuck ; (CloV x x₁ , σ1) → ⊥~irefl ; (LocV x , σ1) → ⊥~istuck ; (BoxV x x₁ , σ1) → ⊥~istuck ;
      (PairV v1 v2 , σ1) → ⊥~istuck ; (InlV v1 , σ1) → ⊥~istuck ; (InrV v1 , σ1) → ⊥~istuck}) ⟩
  (do v1 , σ1 ← eval x e σ
      v2 , σ2 ← eval y e σ1
      exec (APP c) (VAL (conv v2) ∷ VAL (conv v1) ∷ s , convE e , convS σ2))
  ⊥~⟨ (⊥~i>>=-cong-r (eval x e σ) λ (v1 , σ1) → spec i y) ⟩
  (do v1 , σ1 ← eval x e σ
      exec (comp y (APP c)) (VAL (conv v1) ∷ s , convE e , convS σ1))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (comp y (APP c))) ( s , convE e , convS σ))
  ∎

spec i (Abs x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Abs x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (exec c (VAL (Clo' (comp x RET) (convE e)) ∷ s , convE e , convS σ))
  ≡⟨⟩
  (exec (ABS (comp x RET) c) ( s , convE e , convS σ))
  ∎



spec i (Var n) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Var n) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc (lookup e n)  ⟩
  (do v ← lookup e n
      exec c (VAL (conv v) ∷ s , convE e , convS σ))
  ~⟨ lookup-convE n e _ ⟩
  (do v ← lookup (convE e) n
      exec c (VAL v ∷ s , convE e , convS σ))
  ≡⟨⟩
  (exec (LOOKUP n c) (s , convE e , convS σ))
  ∎


spec i Fix {s} {c} {e} {σ} =
  (do v , σ' ← eval Fix e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩ 
  (exec c (VAL (Clo' (comp (App (Var 0) (Box (Delay (App Fix (Var 0))))) RET) (convE e)) ∷ s , convE e , convS σ))
  ≡⟨⟩ 
  (exec c (VAL (Clo' (LOOKUP 0 (BOX (DELAY (comp Fix (LOOKUP 0 (APP RET))) RET) (APP RET))) (convE e)) ∷ s , convE e , convS σ))
  ≡⟨⟩
  (exec (FIX c) (s , convE e , convS σ))
  ∎

spec i (Pair x y) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Pair x y) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v1 , σ1 ← eval x e σ
                  v2 , σ2 ← eval y e σ1
                  return (PairV v1 v2 , σ2)
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ (~i>>=-assoc' (eval x e σ) λ (v1 , σ1) →
     ~i>>=-assoc (eval y e σ1) ) ⟩
  (do v1 , σ1 ← eval x e σ
      v2 , σ2 ← eval y e σ1
      exec c (VAL (Pair' (conv v1) (conv v2)) ∷ s , convE e , convS σ2))
  ≡⟨⟩
  (do v1 , σ1 ← eval x e σ
      v2 , σ2 ← eval y e σ1
      exec (PAIR c) (VAL (conv v2) ∷ VAL (conv v1) ∷ s , convE e , convS σ2))
  ⊥~⟨ (~i>>=-cong-r (eval x e σ) λ (v1 , σ1) → spec i y )⟩
  (do v1 , σ1 ← eval x e σ
      exec (comp y (PAIR c)) (VAL (conv v1) ∷ s , convE e , convS σ1))
  ⊥~⟨ spec i x ⟩
  (do exec (comp x (comp y (PAIR c))) (s , convE e , convS σ))
  ∎

spec i (Pr1 x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Pr1 x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v , σ' ← eval x e σ
                  v1 , v2 ← getPair v
                  return (v1 , σ')
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ( ~i>>=-assoc' (eval x e σ) λ (v , σ') →
     ~i>>=-assoc (getPair v)) ⟩
  (do v , σ' ← eval x e σ
      v1 , v2 ← getPair v
      exec c (VAL (conv v1) ∷ s , convE e , convS σ'))
  ⊥~⟨ (~i>>=-cong-r (eval x e σ)
    λ { (NumV x , σ') → ⊥~istuck ; (CloV x x₁ , σ') → ⊥~istuck ; (LocV x , σ') → ⊥~istuck ; (BoxV x x₁ , σ') → ⊥~istuck ;
      (PairV v v₁ , σ') → ⊥~irefl ; (InlV v , σ') → ⊥~istuck ; (InrV v , σ') → ⊥~istuck}) ⟩
  (do v , σ' ← eval x e σ
      exec (PR1 c) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (PR1 c)) (s , convE e , convS σ))
  ∎
  
spec i (Pr2 x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Pr2 x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v , σ' ← eval x e σ
                  v1 , v2 ← getPair v
                  return (v2 , σ')
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ( ~i>>=-assoc' (eval x e σ) λ (v , σ') →
     ~i>>=-assoc (getPair v)) ⟩
  (do v , σ' ← eval x e σ
      v1 , v2 ← getPair v
      exec c (VAL (conv v2) ∷ s , convE e , convS σ'))
  ⊥~⟨ (~i>>=-cong-r (eval x e σ)
    λ { (NumV x , σ') → ⊥~istuck ; (CloV x x₁ , σ') → ⊥~istuck ; (LocV x , σ') → ⊥~istuck ; (BoxV x x₁ , σ') → ⊥~istuck ;
      (PairV v v₁ , σ') → ⊥~irefl ; (InlV v , σ') → ⊥~istuck ; (InrV v , σ') → ⊥~istuck}) ⟩
  (do v , σ' ← eval x e σ
      exec (PR2 c) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (PR2 c)) (s , convE e , convS σ))
  ∎


spec i (Inl x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Inl x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc (eval x e σ) ⟩
  (do v , σ' ← eval x e σ
      exec c (VAL (Inl' (conv v)) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← eval x e σ
      exec (INL c) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec i x ⟩
  (do exec (comp x (INL c)) (s , convE e , convS σ))
  ∎
  
spec i (Inr x) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Inr x) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc (eval x e σ) ⟩
  (do v , σ' ← eval x e σ
      exec c (VAL (Inr' (conv v)) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← eval x e σ
      exec (INR c) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec i x ⟩
  (do exec (comp x (INR c)) (s , convE e , convS σ))
  ∎



spec i (Case x x1 x2) {s} {c} {e} {σ} =
  (do v , σ' ← eval (Case x x1 x2) e σ
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ≡⟨⟩
  (do v , σ' ← do v , σ' ← eval x e σ
                  caseSum v (λ vl → eval x1 (vl ∷ e) σ') (λ vr → eval x2 (vr ∷ e) σ')
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ~⟨ ~i>>=-assoc (eval x e σ) ⟩
  (do v , σ' ← eval x e σ
      v , σ' ← caseSum v (λ vl → eval x1 (vl ∷ e) σ') (λ vr → eval x2 (vr ∷ e) σ')
      exec c (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ (⊥~i>>=-cong-r (eval x e σ)
    λ { (NumV x , σ') → ⊥~istuck ; (CloV x x₁ , σ') → ⊥~istuck ; (LocV x , σ') → ⊥~istuck ; (BoxV x x₁ , σ') → ⊥~istuck ;
      (PairV v v₁ , σ') → ⊥~istuck ; (InlV v , σ') → ~irefl ; (InrV v , σ') → ~irefl}) ⟩
  (do v , σ' ← eval x e σ
      caseSum v
        (λ vl → do v , σ' ← eval x1 (vl ∷ e) σ'; exec c (VAL (conv v) ∷ s , convE e , convS σ'))
        (λ vr → do v , σ' ← eval x2 (vr ∷ e) σ'; exec c (VAL (conv v) ∷ s , convE e , convS σ')))
  ≡⟨⟩
  (do v , σ' ← eval x e σ
      caseSum v
        (λ vl → do v , σ' ← eval x1 (vl ∷ e) σ'; exec (ENDCASE c) (VAL (conv v) ∷ s , convE (vl ∷ e) , convS σ'))
        (λ vr → do v , σ' ← eval x2 (vr ∷ e) σ'; exec (ENDCASE c) (VAL (conv v) ∷ s , convE (vr ∷ e) , convS σ')))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e σ)
    (λ { (NumV x , σ) → ⊥~irefl ; (CloV x x₁ , σ) → ⊥~irefl ; (LocV x , σ) → ⊥~irefl ; (BoxV x x₁ , σ) → ⊥~irefl ;
    (PairV v v₁ , σ) → ⊥~irefl ; (InlV v , σ) → spec i x1 ; (InrV v , σ) → spec i x2}) ⟩
  (do v , σ' ← eval x e σ
      caseSum v
        (λ vl → exec (comp x1 (ENDCASE c)) (s , convE (vl ∷ e) , convS σ'))
        (λ vr → exec (comp x2 (ENDCASE c)) (s , convE (vr ∷ e) , convS σ')))
  ~⟨ ~i>>=-cong-r (eval x e σ)
    (λ { (NumV x , σ) → ~irefl ; (CloV x x₁ , σ) → ~irefl ; (LocV x , σ) → ~irefl ; (BoxV x x₁ , σ) → ~irefl ;
    (PairV v v₁ , σ) → ~irefl ; (InlV v , σ) → ~irefl ; (InrV v , σ) → ~irefl}) ⟩
  (do v , σ' ← eval x e σ
      exec (CASE (comp x1 (ENDCASE c)) (comp x2 (ENDCASE c))) (VAL (conv v) ∷ s , convE e , convS σ'))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (CASE (comp x1 (ENDCASE c)) (comp x2 (ENDCASE c)))) (s , convE e , convS σ))
  ∎
