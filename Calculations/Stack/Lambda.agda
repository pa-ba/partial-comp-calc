{-# OPTIONS --copatterns --sized-types --guardedness #-}


------------------------------------------------------------------------
-- Calculation for call-by-value lambda calculus with integers and
-- addition.
------------------------------------------------------------------------

module Calculations.Stack.Lambda where


open import CTree hiding (τ) public
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Unit
open import Agda.Builtin.Nat
open import Data.Bool 
open import Data.Product
open import Data.List hiding (lookup)
open import Function hiding (force)

---------------------
-- Source language --
---------------------

data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Abs : Expr → Expr
  App : Expr → Expr → Expr
  Var : ℕ → Expr

mutual
  data Value : Set where
    Num : ℕ → Value
    Clo : Expr → Env → Value

  Env : Set
  Env = List Value

Partial : Set → Size → Set₁
Partial A i = CTree⊥ None A i

∞Partial : Set → Size → Set₁
∞Partial A i = ∞CTree⊥ None A i



lookup : ∀ {a i} → ℕ → List a → Partial a i
lookup 0 (x ∷ xs) = return x
lookup (suc i) (x ∷ xs) = lookup i xs
lookup _ _ = stuck


-- The following two functions are used instead of partial pattern
-- matching. Agda supports an Idris-style pattern matching syntax
-- within the do notation, but that is useless for reasoning (see
-- https://agda.readthedocs.io/en/v2.6.2/language/lambda-abstraction.html)

getNum : ∀ {i} → Value → Partial ℕ i
getNum (Num n) = return n
getNum _ = stuck

getClo : ∀ {i} → Value → Partial (Expr × Env) i
getClo (Clo x e) = return (x , e)
getClo _ = stuck


mutual
  eval : ∀ {i} → Expr → Env → Partial Value i
  eval (Val x) e = return (Num x)
  eval (Add x y) e =
    do n ← eval x e >>= getNum
       m ← eval y e >>= getNum
       return (Num (n + m))
  eval (Var i) e = lookup i e
  eval (Abs x)   e = return (Clo x e)
  eval (App x y) e = do x' , e' ← eval x e >>= getClo
                        v <- eval y e
                        later (∞eval x' (v ∷ e'))

  ∞eval : ∀ {i} → Expr → Env → ∞Partial Value i
  force (∞eval x e) = eval x e


---------------------
-- Target language --
---------------------

data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  LOOKUP : ℕ → Code → Code
  RET : Code
  APP : Code → Code
  ABS : Code → Code → Code
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'

  Env' : Set
  Env' = List Value'
  

data Elem : Set where
  VAL : Value' → Elem
  CLO : Code → Env' → Elem


Stack : Set
Stack = List Elem

Conf : Set
Conf = Stack × Env'


--------------
-- Compiler --
--------------

comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (Var i) c = LOOKUP i c
comp (App x y) c = comp x (comp y (APP c))
comp (Abs x) c = ABS (comp x RET) c




-----------------
-- Calculation --
-----------------


mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs


-- We use the TERMINATING pragma since Agda does not recognize that
-- `exec` is terminating. We prove that `exec` is terminating
-- separately in the `Terminating.Lambda` module.

mutual
  {-# TERMINATING #-}
  exec : ∀ {i} → Code → Conf → Partial Conf i
  exec (PUSH n c) (s , e) = exec c (VAL (Num' n) ∷ s , e)
  exec (ADD c) (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e) = exec c (VAL (Num' (m + n)) ∷ s , e)
  exec (LOOKUP n c) (s , e) = do v <- lookup n e
                                 exec c (VAL v ∷ s , e)
  exec RET  (VAL u ∷ CLO c e' ∷ s , _) = exec c (VAL u ∷ s , e')
  exec (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e) = later (∞exec c' (CLO c e ∷ s , v ∷ e'))
  exec (ABS c' c) (s , e) = exec c (VAL (Clo' c' e) ∷ s , e)
  exec HALT c = return c
  exec _ _ = stuck


  ∞exec : ∀ {i} → Code → Conf → ∞Partial Conf i
  force (∞exec c e) = exec c e


-- This is the lookup lemma that is used in the `Var` case.
lookup-conv : ∀ {i A} n e → (f : Value' → Partial A ∞) →
  (lookup n e >>= (f ∘ conv)) ~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ~irefl
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f = ~istuck-refl
lookup-conv zero [] f = ~istuck-refl

open ⊥~i-Calculation

-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.

spec : ∀ i x {s c e} →
  (do v ← eval x e
      exec c (VAL (conv v) ∷ s , convE e))
  ⊥~[ i ]
  (exec (comp x c) (s , convE e))
spec zero _ =  ⊥~izero
spec i (Val x) {s} {c} {e}  =
  (do v ← eval (Val x) e
      exec c (VAL (conv v) ∷ s , convE e))
  ≡⟨⟩
  (exec (comp (Val x) c) (s , convE e))
  ∎
spec i (Add x y) {s} {c} {e} =
  (do v ← eval (Add x y) e
      exec c (VAL (conv v) ∷ s , convE e))
  ≡⟨⟩
  (do v <- (do n ← eval x e >>= getNum
               m ← eval y e >>= getNum
               return (Num (n + m)))
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ ~i>>=-assoc (eval x e >>= getNum) ⟩
  (do n ← eval x e >>= getNum
      v <- (do m ← eval y e >>= getNum
               return (Num (n + m)))
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (\ n -> ~i>>=-assoc (eval y e >>= getNum))⟩
  (do n ← eval x e >>= getNum
      m ← eval y e >>= getNum
      exec c (VAL (Num' (n + m)) ∷ s , convE e))
  ≡⟨⟩
  (do n ← eval x e >>= getNum
      m ← eval y e >>= getNum
      exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))
  ~⟨ ~i>>=-assoc (eval x e) ⟩
  (do n' ← eval x e
      n ← getNum n'
      m ← eval y e >>= getNum
      exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))
  ⊥~⟨  ⊥~i>>=-cong-r (eval x e) (λ {(Num n) → ⊥~irefl;
      (Clo _ _) →  ⊥~istuck})  
   ⟩
  (do n ← eval x e
      m ← eval y e >>= getNum
      exec (ADD c) (VAL (Num' m) ∷ VAL (conv n) ∷ s , convE e))
  ⊥~⟨  ⊥~i>>=-cong-r (eval x e) ( λ n →
        ⊥~itrans (⊥~i>>=-assoc (eval y e)) ( ⊥~i>>=-cong-r (eval y e) 
        (λ {(Num m) → ⊥~irefl;
        (Clo _ _) → ⊥~istuck })))⟩
  (do n ← eval x e
      m ← eval y e
      exec (ADD c) (VAL (conv m) ∷ VAL (conv n) ∷ s , convE e))
  ⊥~⟨  ⊥~i>>=-cong-r (eval x e) (λ n → spec i y ) ⟩
  (do n ← eval x e
      exec (comp y (ADD c)) (VAL (conv n) ∷ s , convE e))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (comp y (ADD c))) (s , convE e))
  ∎  

spec i (Var n) {s} {c} {e} =
  (do v ← eval (Var n) e
      exec c (VAL (conv v) ∷ s , convE e))
  ≡⟨⟩
  (do v ← lookup n e
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ lookup-conv n e _ ⟩
  (do v ← lookup n (convE e)
      exec c (VAL v ∷ s , convE e))
  ≡⟨⟩
  (exec (LOOKUP n c) (s , convE e))
  ∎

spec i@(suc j) (App x y) {s} {c} {e} =
  (do v ← eval (App x y) e
      exec c (VAL (conv v) ∷ s , convE e))
  ≡⟨⟩
  (do v ← do x' , e' <- eval x e >>= getClo
             v <- eval y e
             later (∞eval x' (v ∷ e'))
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ ~i>>=-assoc ( eval x e >>= getClo) ⟩
  (do x' , e' <- eval x e >>= getClo
      v ← do v <- eval y e
             later (∞eval x' (v ∷ e'))
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ _ → ~i>>=-assoc (eval y e)) ⟩
  (do x' , e' <- eval x e >>= getClo
      v <- eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec c (VAL (conv w) ∷ s , convE e))
  ≡⟨⟩
  (do x' , e' <- eval x e >>= getClo
      v <- eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e')))
  ≡⟨⟩
  (do x' , e' <- eval x e >>= getClo
      v <- eval y e
      later(∞eval x' (v ∷ e') ∞>>= λ w →
       exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e'))))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e >>= getClo) (λ (x' , e') → ⊥~i>>=-cong-r (eval y e)
                 (λ v →  ⊥~ilater ( spec j x') )) ⟩
  (do x' , e' <- eval x e >>= getClo
      v <- eval y e
      later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE (v ∷ e'))))
  ≡⟨⟩
  (do x' , e' <- eval x e >>= getClo
      v <- eval y e
      exec (APP c) (VAL (conv v) ∷ VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
  ⊥~⟨ ⊥~itrans (⊥~i>>=-assoc (eval x e)) ( ⊥~i>>=-cong-r (eval x e)
      λ {(Num _) →   ⊥~istuck ;
         (Clo x e) → ⊥~irefl}) ⟩
  (do w <- eval x e
      v <- eval y e
      exec (APP c) (VAL (conv v) ∷ VAL (conv w) ∷ s , convE e))
  ⊥~⟨ ⊥~i>>=-cong-r (eval x e) (λ w → spec i y) ⟩
  (do w <- eval x e
      exec (comp y (APP c)) (VAL (conv w) ∷ s , convE e))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (comp y (APP c))) (s , convE e))
  ∎

spec i (Abs x) {s} {c} {e} =
  (do v ← eval (Abs x) e
      exec c (VAL (conv v) ∷ s , convE e))
  ≡⟨⟩ -- definition of eval & conv
  (exec c (VAL (Clo' (comp x RET) (convE e)) ∷ s , convE e))
  ≡⟨⟩ -- definition of exec (ABS c) 
  (exec (ABS (comp x RET) c) (s , convE e))
  ∎


-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).
spec' : ∀ s c e x →
  (do v ← eval x e
      exec c (VAL (conv v) ∷ s , convE e))
  ⊥~
  (exec (comp x c) (s , convE e))
spec' s c e x =  ⊥~i-⊥~  (λ i → spec i x)

------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT


specCompile : ∀ s x →
  (do v ← eval x []
      return (VAL (conv v) ∷ s , []))
  ⊥~
  (exec (compile x) (s , []))
specCompile s x = spec' s HALT [] x


-- Well-typed terms never go wrong and are thus strongly bisimilar to
-- their compiled code.

-----------------
-- Type system --
-----------------

data type : Set where
  N : type
  _⇒_ : type → type → type

ctx : Set
ctx = List type

infix 3 _⊢x_∶_
infix 3 ⊢c_∶_
infix 3 ⊢v_∶_
infix 3 _⊢_∶_
infix 4 _⇒_


data _⊢x_∶_ : ctx → ℕ → type → Set where
  ⊢zero : ∀ {τ Γ} → τ ∷ Γ ⊢x 0 ∶ τ
  ⊢succ : ∀ {τ τ' Γ i} → Γ ⊢x i ∶ τ → τ' ∷ Γ ⊢x suc i ∶ τ

data _⊢_∶_ : ctx → Expr → type → Set where
  ⊢val : ∀ {Γ n} → Γ ⊢ Val n ∶ N
  ⊢add : ∀ {Γ x y} → Γ ⊢ x ∶ N → Γ ⊢ y ∶ N → Γ ⊢ Add x y ∶ N
  ⊢var : ∀ {Γ i τ} → Γ ⊢x i ∶ τ → Γ ⊢ Var i ∶ τ
  ⊢abs : ∀ {Γ x τ₁ τ₂} → τ₁ ∷ Γ ⊢ x ∶ τ₂ → Γ ⊢ Abs x ∶ τ₁ ⇒ τ₂
  ⊢app : ∀ {Γ x y τ τ'} → Γ ⊢ x ∶ τ' ⇒ τ → Γ ⊢ y ∶ τ' → Γ ⊢ App x y ∶ τ

mutual
  data ⊢v_∶_ : Value → type → Set where
    ⊢num : ∀ {n} → ⊢v Num n ∶ N
    ⊢clo : ∀ {τ τ' γ Γ t} → τ ∷ Γ ⊢ t ∶ τ' → ⊢c γ ∶ Γ → ⊢v Clo t γ ∶ τ ⇒ τ'

  data ⊢c_∶_ : Env → ctx → Set where
    ⊢cnil : ⊢c [] ∶ []
    ⊢ccons : ∀ {v τ γ Γ} → ⊢v v ∶ τ → ⊢c γ ∶ Γ → ⊢c v ∷ γ ∶ τ ∷ Γ


-- Well-typed terms are safe

mutual
  eval-safe : ∀ {i Γ t τ γ} → Γ ⊢ t ∶ τ → ⊢c γ ∶ Γ → safeP {i} (λ v → ⊢v v ∶ τ ) (eval t γ)
  eval-safe ⊢val E = spnow ⊢num
  eval-safe {γ = γ} (⊢add  T₁ T₂) E =
               safeP->>= (safeP->>= (eval-safe T₁ E)  λ {⊢num → spnow tt})
               λ _ → safeP->>= ((safeP->>= (eval-safe T₂ E)  λ {⊢num → spnow tt}))
               λ _ → spnow ⊢num
  eval-safe (⊢var x) E = lookup⊢ E x
    where lookup⊢ : ∀ {Γ i τ γ} → ⊢c γ ∶ Γ → Γ ⊢x i ∶ τ → safeP (λ v → ⊢v v ∶ τ) (lookup i γ)
          lookup⊢ (⊢ccons x _) ⊢zero = spnow x
          lookup⊢ (⊢ccons x xs) (⊢succ T) = lookup⊢ xs T

  eval-safe (⊢abs T) E = spnow (⊢clo T E)
  eval-safe {γ = γ} (⊢app {x = x} {y} {τ} {τ'} T1 T2) E =  safeP->>= {p = eval x γ >>= getClo}
    (safeP->>= {p = eval x γ} {λ v → ⊢v v ∶ τ' ⇒ τ} (eval-safe T1 E) (λ {(⊢clo x' e') → spnow ((⊢clo x' e'))} ) )
    λ { {v} (⊢clo x' e') → safeP->>= {p = eval y γ} (eval-safe T2 E)
    λ {v'} T' → splater ( ∞eval-safe x' (⊢ccons T' e')) }


  ∞eval-safe : ∀ {i Γ t τ γ} → (Γ ⊢ t ∶ τ) → (⊢c γ ∶ Γ) → ∞safeP {i} (λ v → ⊢v v ∶ τ ) (∞eval t γ)
  spforce (∞eval-safe T G) = eval-safe T G


-- stronger version of the compiler correctness property for
-- well-typed terms

specCompileTyped : ∀ s x τ →
  [] ⊢ x ∶ τ →
  (do v ← eval x []
      return (VAL (conv v) ∷ s , []))
  ~
  (exec (compile x) (s , []))
specCompileTyped s x τ T = ⊥~-~ (safeP->>= (eval-safe T ⊢cnil) λ _ → spnow _) (specCompile s x)
