{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for lambda calculus + fork/send/receive + channels 
------------------------------------------------------------------------

module Calculations.Stack.LambdaConcur where

open import CCTree hiding (τ) public
open import Data.Nat
open import Data.Bool.Properties hiding (_≟_)
open import Data.Product hiding (map)
open import Data.List hiding (map;lookup)
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Agda.Builtin.Equality

-------------
-- Effects --
-------------


Chan : Set
Chan = ℕ


data ChanEff : Set → Set where
  SendInt    : Chan → ℕ → ChanEff ⊤
  ReceiveInt : Chan → ChanEff ℕ
  NewChan    : ChanEff Chan


instance
  chan : Concurrent ChanEff
  
  -- concurrent effect handler
  _⇄_ {{chan}} (SendInt ch n) (ReceiveInt ch')
    =  if ch ≡ᵇ ch' then mk⇄ [(tt , n)] else mk⇄ []
  _⇄_ {{chan}} (ReceiveInt ch') (SendInt ch n)
    = if ch ≡ᵇ ch' then mk⇄ [(n , tt)] else mk⇄ []
  _⇄_ {{chan}} _ _ = mk⇄ []

  -- symmetry of ⇄
  ⇄-sym ⦃ chan ⦄ (SendInt ch x₁) (ReceiveInt ch') tr with ch ≡ᵇ ch'
  ⇄-sym ⦃ chan ⦄ (SendInt ch x₁) (ReceiveInt ch') ⇒-later | true = ⇒-later
  ⇄-sym ⦃ chan ⦄ (ReceiveInt ch') (SendInt ch x₂) tr  with ch ≡ᵇ ch'
  ⇄-sym ⦃ chan ⦄ (ReceiveInt ch') (SendInt ch x₂) ⇒-later | true = ⇒-later
  ⇄-sym ⦃ chan ⦄ (SendInt x x₁) NewChan ()
  ⇄-sym ⦃ chan ⦄ (ReceiveInt x) NewChan ()
  ⇄-sym ⦃ chan ⦄ NewChan NewChan ()

  -- ⇄ only has τ transitions to return
  ⇄-step ⦃ chan ⦄ (SendInt ch _) (ReceiveInt ch') tr with ch ≡ᵇ ch'
  ⇄-step ⦃ chan ⦄ (SendInt ch _) (ReceiveInt ch') ⇒-later | true = refl , _ , refl
  ⇄-step ⦃ chan ⦄ (ReceiveInt ch') (SendInt ch _) tr  with ch ≡ᵇ ch'
  ⇄-step ⦃ chan ⦄ (ReceiveInt ch') (SendInt ch _) ⇒-later | true = refl , _ , refl
  ⇄-step ⦃ chan ⦄ (SendInt x x₁) NewChan ()
  ⇄-step ⦃ chan ⦄ (ReceiveInt x) NewChan ()
  ⇄-step ⦃ chan ⦄ NewChan NewChan ()


send : ∀ {i} → Chan → ℕ → CCTree⊥ ChanEff ⊤ i
send tid n = eff (notStuck (SendInt tid n)) return

receive : ∀ {i} → Chan → CCTree⊥ ChanEff ℕ i
receive tid = eff (notStuck (ReceiveInt tid)) return

newChan : ∀ {i} → CCTree⊥ ChanEff Chan i
newChan = eff (notStuck NewChan) return



---------------------
-- Source language --
---------------------

data Expr : Set where
  App : Expr → Expr → Expr
  Abs : Expr → Expr
  Var : ℕ → Expr
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Send : Expr → Expr → Expr
  Receive : Expr → Expr
  Fork : Expr → Expr



lookup : ∀ {i A e} → ℕ → List A → CCTree⊥ e A i
lookup _ [] = stuck
lookup 0 (x ∷ e) = return x
lookup (suc n) (x ∷ e) = lookup n e

mutual
  data Value : Set where
    Num : ℕ → Value
    Clo : Expr → Env → Value
  
  Env : Set
  Env = List Value

getNum : ∀ {i} → Value → CCTree⊥ ChanEff ℕ i
getNum (Num n) = return n
getNum _ = stuck

getClo : ∀ {i} → Value → CCTree⊥ ChanEff (Expr × Env) i
getClo (Clo x e) = return (x , e)
getClo _ = stuck


mutual
  eval : ∀ {i} → Expr → Env → CCTree⊥ ChanEff Value i
  eval (Val x)     e = return (Num x)
  eval (Add x y)   e = do n ← eval x e >>= getNum
                          m ← eval y e >>= getNum
                          return (Num (n + m))
  eval (Fork x)    e = do ch ← newChan
                          eval x (Num ch ∷ e) ∥⃗ return (Num ch)
  eval (Send x y)  e = do ch ← eval x e >>= getNum
                          n ← eval y e >>= getNum
                          send ch n
                          return (Num n)
  eval (Receive x) e = do ch ← eval x e >>= getNum
                          n ← receive ch
                          return (Num n)
  eval (Abs x)     e = return (Clo x e)
  eval (Var n)     e = lookup n e
  eval (App x y)   e = do x' , e' ← eval x e >>= getClo
                          v ← eval y e
                          later (∞eval x' (v ∷ e'))

  ∞eval : ∀ {i} → Expr → Env → ∞CCTree⊥ ChanEff Value i
  force (∞eval x e) = eval x e


hanChan : {B : Set} → Chan → ChanEff B → CCTree⊥ None (B × Chan) ∞
hanChan ch (SendInt _ _) = ∅
hanChan ch (ReceiveInt _) = ∅
hanChan ch NewChan = return (ch , suc ch)

evaluate : ∀ {i} → Expr → CCTree⊥ None Value i
evaluate x = interpSt⊥ 0 hanChan (eval x [])


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
  SEND : Code → Code
  RECEIVE : Code → Code
  FORK : Code → Code → Code
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

nil : Stack
nil = []

Conf : Set
Conf = Stack × Env'

{-# TERMINATING #-}
mutual
  exec : ∀ {i} → Code → Conf → CCTree⊥ ChanEff Conf i
  exec (PUSH n c)   (s , e)                                = exec c (VAL (Num' n) ∷ s , e)
  exec (ADD c)      (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e)  = exec c (VAL (Num' (m + n)) ∷ s , e)
  exec (LOOKUP n c) (s , e)                                = do v ← lookup n e; exec c (VAL v ∷ s , e)
  exec (ABS c' c)   (s , e)                                = exec c (VAL (Clo' c' e) ∷ s , e)
  exec RET          (VAL u ∷ CLO c e' ∷ s , _)             = exec c (VAL u ∷ s , e')
  exec (APP c)      (VAL v ∷ VAL (Clo' c' e') ∷ s , e)     = later (∞exec c' (CLO c e ∷ s , v ∷ e'))
  exec (SEND c)     (VAL (Num' n) ∷ VAL (Num' ch) ∷ s , e) = do send ch n; exec c (VAL (Num' n) ∷ s , e)
  exec (RECEIVE c)  (VAL (Num' ch) ∷ s , e)                = do n ← receive ch; exec c (VAL (Num' n) ∷ s , e)
  exec (FORK c' c)  (s , e)                                = do ch ← newChan
                                                                exec c' ([] , Num' ch ∷ e) ∥⃗ exec c (VAL (Num' ch) ∷ s , e)
  exec HALT         (s , e)                                = return (s , e)
  exec _            _                                      = stuck

  ∞exec : ∀ {i} → Code → Conf → ∞CCTree⊥ ChanEff Conf i
  force (∞exec c s) = exec c s


execute : ∀ {i} → Code → Stack → CCTree⊥ None Conf i
execute c s = interpSt⊥ 0 hanChan ( exec c (s , []))

--------------
-- Compiler --
--------------


comp : Expr → Code → Code
comp (Val n)     c =  PUSH n c
comp (Add x y)   c = comp x (comp y (ADD c))
comp (Var i)     c = LOOKUP i c
comp (App x y)   c = comp x (comp y (APP c))
comp (Abs x)     c = ABS (comp x RET) c
comp (Send x y)  c = comp x (comp y (SEND c))
comp (Receive x) c = comp x (RECEIVE c)
comp (Fork x)    c = FORK (comp x HALT) c

mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs

------------
-- Lemmas --
------------

lookup-conv : ∀ {i A} n e → (f : Value' → CCTree⊥ ChanEff A ∞) →
  (lookup n e >>= (λ x → f (conv x))) ⊥~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ⊥~itrans ⊥~ireturn->>= (~i-⊥~i (~isym ~ireturn->>=))
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f = ⊥~istuck->>=
lookup-conv zero [] f = ⊥~istuck->>=

-----------------
-- Calculation --
-----------------

open ⊥~i-Calculation

spec : ∀ i x {e s c} →
  (do v ← eval x e; exec c (VAL (conv v) ∷ s , convE e)) ⊥~[ i ] exec (comp x c) (s , convE e)
spec zero _ =  ⊥~izero
spec i (Val x) {e} {s} {c} =
  (do v ← eval (Val x) e; exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~ireturn->>= ⟩
  exec (comp (Val x) c) (s , convE e)
 ∎

spec i (Add x y) {e} {s} {c} =
  (do v ← eval (Add x y) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← (do n ← eval x e >>= getNum
              m ← eval y e >>= getNum
              return (Num (n + m)))
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do n ← eval x e >>= getNum
      v ← (do m ← eval y e >>= getNum
              return (Num (n + m)))
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-cong-r _ ( λ n → ~itrans (~i>>=-assoc (eval y e >>= getNum))
   (~i>>=-cong-r (eval y e >>= getNum) (λ m → ~ireturn->>=))) ⟩
  (do n ← eval x e >>= getNum
      m ← eval y e >>= getNum
      exec c (VAL (Num' (n + m)) ∷ s , convE e))
 ≡⟨⟩
  (do n ← eval x e >>= getNum
      m ← eval y e >>= getNum
      exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))
 ⊥~⟨  ⊥~i>>=-cong-r _ ( λ n →  ⊥~itrans (⊥~i>>=-assoc (eval y e))
   (( ⊥~i>>=-cong-r (eval y e) (λ {(Num m) → ⊥~ireturn->>=; (Clo _ _) → ⊥~istuck->>= })))) ⟩
  (do n ← (eval x e >>= getNum)
      m ← eval y e
      exec (ADD c) (VAL (conv m) ∷ VAL (Num' n) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ _ → spec i y) ⟩
  (do n ← (eval x e >>= getNum)
      exec (comp y (ADD c)) (VAL (Num' n) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do n' ← eval x e
      n ← getNum n'
      exec (comp y (ADD c)) (VAL (Num' n) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ { (Num _) → ⊥~ireturn->>= ; (Clo _ _) → ⊥~istuck->>=}) ⟩
  (do n' ← eval x e
      exec (comp y (ADD c)) (VAL (conv n') ∷ s , convE e))
 ⊥~⟨ spec i x ⟩
    (exec (comp x (comp y (ADD c))) (s , convE e))
 ∎



spec i (Var n) {e} {s} {c} =
  (do v ← eval (Var n) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← lookup n e; exec c (VAL (conv v) ∷ s , convE e))
 ⊥~⟨ lookup-conv n e _ ⟩
  (do v ← lookup n (convE e); exec c (VAL v ∷ s , convE e))
 ≡⟨⟩
  exec (LOOKUP n c) (s , convE e)
 ∎

spec i@(suc j) (App x y) {e} {s} {c} =
  (do v ← eval (App x y) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← do x' , e' ← eval x e >>= getClo
             v ← eval y e
             later (∞eval x' (v ∷ e'))
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-assoc ( eval x e >>= getClo) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← do v ← eval y e
             later (∞eval x' (v ∷ e'))
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ _ → ~i>>=-assoc (eval y e)) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec c (VAL (conv w) ∷ s , convE e))
 ≡⟨⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e')))
 ~⟨ ~i>>=-cong-r _ (λ _ → ~i>>=-cong-r _ (λ _ → ~i>>=-later)) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      later(∞eval x' (v ∷ e') ∞>>= λ w →
       exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e'))))
 ⊥~⟨ ⊥~i>>=-cong-r (eval x e >>= getClo) (λ (x' , e') → ⊥~i>>=-cong-r (eval y e)
                (λ v →  ⊥~ilater ( spec j x') )) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE (v ∷ e'))))
 ≡⟨⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      exec (APP c) (VAL (conv v) ∷ VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ _ → spec i y) ⟩
  (do x' , e' ← eval x e >>= getClo
      exec (comp y (APP c)) (VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do v ← eval x e
      x' , e' ← getClo v
      exec (comp y (APP c)) (VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ { (Num x) → ⊥~istuck->>= ; (Clo x x₁) → ⊥~ireturn->>=}) ⟩
  (do v ← eval x e
      exec (comp y (APP c)) (VAL (conv v) ∷ s , convE e))
 ⊥~⟨ spec i x ⟩
  exec (comp x (comp y (APP c))) (s , convE e)
 ∎

spec i (Abs x) {e} {s} {c} =
  (do v ← eval (Abs x) e; exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~ireturn->>= ⟩
  exec c (VAL (Clo' (comp x RET) (convE e)) ∷ s , convE e)
 ≡⟨⟩
  exec (ABS (comp x RET) c) (s , convE e)
 ∎


spec i (Send x y) {e} {s} {c} =
  (do v ← eval (Send x y) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← do ch ← eval x e >>= getNum
             n ← eval y e >>= getNum
             send ch n
             return (Num n)
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ (~i>>=-assoc' _ λ t → ~i>>=-assoc' _ (λ n → ~i>>=-assoc' _ (λ _ → ~ireturn->>=))) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      send ch n
      exec c (VAL (Num' n) ∷ s , convE e))
 ≡⟨⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      exec (SEND c) (VAL (Num' n) ∷ VAL (Num' ch) ∷ s , convE e))
 ~⟨ ~i>>=-cong-r _ (λ _ → ~i>>=-assoc _) ⟩
  (do ch ← eval x e >>= getNum
      v ← eval y e
      n ← getNum v
      exec (SEND c) (VAL (Num' n) ∷ VAL (Num' ch) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ _ →  ⊥~i>>=-cong-r _ λ { (Num x) → ⊥~ireturn->>= ; (Clo x x₁) → ⊥~istuck->>=}) ⟩
  (do ch ← eval x e >>= getNum
      v ← eval y e
      exec (SEND c) (VAL (conv v) ∷ VAL (Num' ch) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ _ → spec i y) ⟩
  (do ch ← eval x e >>= getNum
      exec (comp y (SEND c)) (VAL (Num' ch) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do v ← eval x e
      ch ← getNum v
      exec (comp y (SEND c)) (VAL (Num' ch) ∷ s , convE e))
 ⊥~⟨ (⊥~i>>=-cong-r _ λ { (Num x) → ⊥~ireturn->>= ; (Clo x x₁) → ⊥~istuck->>=}) ⟩
  (do v ← eval x e
      exec (comp y (SEND c)) (VAL (conv v) ∷ s , convE e))
 ⊥~⟨ spec i x ⟩
  exec (comp x (comp y (SEND c))) (s , convE e)
 ∎

spec i (Receive x) {e} {s} {c} =
  (do v ← eval (Receive x) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← do ch ← eval x e >>= getNum
             n ← receive ch
             return (Num n)
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-assoc' _ (λ _ → ~i>>=-assoc' _ (λ _ → ~ireturn->>=)) ⟩
  (do ch ← eval x e >>= getNum
      n ← receive ch
      exec c (VAL (Num' n) ∷ s , convE e))
 ≡⟨⟩
  (do ch ← eval x e >>= getNum
      exec (RECEIVE c) (VAL (Num' ch) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do v ← eval x e
      ch ← getNum v
      exec (RECEIVE c) (VAL (Num' ch) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ { (Num x) → ⊥~ireturn->>= ; (Clo x x₁) → ⊥~istuck->>=}) ⟩
  (do v ← eval x e
      exec (RECEIVE c) (VAL (conv v) ∷ s , convE e))
 ⊥~⟨ spec i x ⟩
  exec (comp x (RECEIVE c)) (s , convE e)
 ∎


spec i (Fork x) {e} {s} {c} =
  (do v ← eval (Fork x) e; exec c (VAL (conv v) ∷ s , convE e))
 ≡⟨⟩
  (do v ← do ch ← newChan
             eval x (Num ch ∷ e) ∥⃗ return (Num ch)
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-assoc _ ⟩
  (do ch ← newChan
      v ← eval x (Num ch ∷ e) ∥⃗ return (Num ch)
      exec c (VAL (conv v) ∷ s , convE e))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗->>=) ⟩
  (do ch ← newChan
      eval x (Num ch ∷ e) ∥⃗ (return (Num ch) >>= λ v → exec c (VAL (conv v) ∷ s , convE e)))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗-cong-r ~ireturn->>=) ⟩
  (do ch ← newChan
      eval x (Num ch ∷ e) ∥⃗ exec c (VAL (Num' ch) ∷ s , convE e))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗-map-l _ _) ⟩
  (do ch ← newChan
      (eval x (Num ch ∷ e) >>= λ v → exec HALT ([ VAL (conv v) ] , Num' ch ∷ convE e)) ∥⃗ exec c (VAL (Num' ch) ∷ s , convE e))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ ch' → ⊥~i∥⃗-cong-l (spec i x)) ⟩
  (do ch ← newChan
      exec (comp x HALT) ([] , Num' ch ∷ convE e) ∥⃗ exec c (VAL (Num' ch) ∷ s , convE e))
 ≡⟨⟩
  exec (FORK (comp x HALT) c) (s , convE e)
 ∎


------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT

specCompile : ∀ s x →
  (do v ← evaluate x; return (VAL (conv v) ∷ s , []))  ⊥~ execute (compile x) s
specCompile s x = ⊥~i-⊥~ λ i →
  (do v ← evaluate x; return (VAL (conv v) ∷ s , []))
 ≡⟨⟩
  (do v ← interpSt⊥ 0 hanChan (eval x []); return (VAL (conv v) ∷ s , []))
 ⊥~⟨ ⊥~iinterpSt⊥-map {f = hanChan} _ ⟩
  interpSt⊥ 0 hanChan (do v ← eval x []; return (VAL (conv v) ∷ s , []))
 ⊥~⟨ ⊥~iinterpSt⊥-cong {f = hanChan} (spec i x {_} {s}) ⟩
  execute (compile x) s
 ∎



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
  ⊢send : ∀ {Γ x y} → Γ ⊢ x ∶ N → Γ ⊢ y ∶ N → Γ ⊢ Send x y ∶ N
  ⊢receive : ∀ {Γ x} → Γ ⊢ x ∶ N → Γ ⊢ Receive x ∶ N
  ⊢fork : ∀ {Γ x τ} → N ∷ Γ ⊢ x ∶ τ → Γ ⊢ Fork x ∶ N


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
  eval-safe {i} ⊢val E = spnow {i} ⊢num
  eval-safe {i} {γ = γ} (⊢add  T₁ T₂) E =
               safeP->>= (safeP->>= (eval-safe {i} T₁ E)  λ {⊢num → spnow tt})
               λ _ → safeP->>= ((safeP->>= (eval-safe {i} T₂ E)  λ {⊢num → spnow tt}))
               λ _ → spnow ⊢num
  eval-safe {i} (⊢var x) E = lookup⊢ E x
    where lookup⊢ : ∀ {Γ v τ γ} → ⊢c γ ∶ Γ → Γ ⊢x v ∶ τ → safeP {i} (λ v → ⊢v v ∶ τ) (lookup v γ)
          lookup⊢ (⊢ccons x _) ⊢zero = spnow x
          lookup⊢ (⊢ccons x xs) (⊢succ T) = lookup⊢ xs T

  eval-safe (⊢abs T) E = spnow (⊢clo T E)
  eval-safe {γ = γ} (⊢app {x = x} {y} {τ} {τ'} T1 T2) E =  safeP->>= {p = eval x γ >>= getClo}
    (safeP->>= {p = eval x γ} {λ v → ⊢v v ∶ τ' ⇒ τ} (eval-safe T1 E) (λ {(⊢clo x' e') → spnow ((⊢clo x' e'))} ) )
    λ { {v} (⊢clo x' e') → safeP->>= {p = eval y γ} (eval-safe T2 E)
    λ {v'} T' → splater ( ∞eval-safe x' (⊢ccons T' e')) }
  eval-safe {i} {γ = γ} (⊢send  T₁ T₂) E =
               safeP->>= (safeP->>= (eval-safe {i} T₁ E)  λ {⊢num → spnow tt})
               λ _ → safeP->>= ((safeP->>= (eval-safe {i} T₂ E)  λ {⊢num → spnow tt}))
               λ _ → safeP->>= (speff (λ _ → spnow tt)) λ _ → spnow ⊢num
  eval-safe {i} {γ = γ} (⊢receive  T) E =
    safeP->>= (safeP->>= (eval-safe {i} T E)
      (λ { ⊢num → spnow tt}))
      λ x₁ → safeP->>= (speff (λ r → spnow tt))
      (λ x₂ → spnow ⊢num)
  eval-safe {i}  {γ = γ}  (⊢fork {Γ} {x} {τ} T) E = safeP->>= (speff (λ r → spnow tt))
    (λ x₁ → safeP-∥⃗ (safeP-weaken (λ _ → tt) (eval-safe {i} T (⊢ccons ⊢num E))) (spnow ⊢num))

  ∞eval-safe : ∀ {i Γ t τ γ} → (Γ ⊢ t ∶ τ) → (⊢c γ ∶ Γ) → ∞safeP {i} (λ v → ⊢v v ∶ τ ) (∞eval t γ)
  spforce (∞eval-safe T G) = eval-safe T G


hanChan-safe : ∀ {B ch} (e : ChanEff B) → safe (hanChan ch e)
hanChan-safe (SendInt x x₁) = spempty
hanChan-safe (ReceiveInt x) = spempty
hanChan-safe NewChan = spnow tt

evaluate-safe : ∀ {i t τ} → [] ⊢ t ∶ τ → safe {i} (evaluate t)
evaluate-safe T = safeP-interpSt⊥ (safeP-safe (eval-safe T ⊢cnil)) λ {B} {st} {e} → hanChan-safe e

-- stronger version of the compiler correctness property for
-- well-typed terms

specCompileTyped : ∀ s x τ →
  [] ⊢ x ∶ τ →
  (do v ← evaluate x
      return (VAL (conv v) ∷ s , []))
  ~
  (execute (compile x) s)
specCompileTyped s x τ T = ⊥~-~' (safeP->>= (evaluate-safe T) (λ _ → spnow tt)) (specCompile s x)
