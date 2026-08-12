{-# OPTIONS --sized-types #-}

-- Here we give a separate proof that the register machine exec for
-- the lambda calculus is indeed well-defined.

module Calculations.Terminating.Memory.Lambda where

open import Calculations.Memory.Lambda

open import CTree hiding (τ)
open import Data.Nat
open import Data.Nat.Properties

open import Data.Product hiding (map)
open import Data.List hiding (map ; lookup)

-- Define the measure that is used to show that exec is well-founded.
--
-- Unlike the stack machine, the register machine keeps its return
-- address in a register rather than on a stack, so we cannot bound
-- the size of the code that `exec RET` jumps to: the memory is an
-- abstract map and the code stored in it is arbitrary. What we can
-- bound is how often such a jump can happen, because `RET` pops the
-- top-most memory off the lambda stack `l`. Every other instruction
-- leaves `l` unchanged and makes the code argument structurally
-- smaller. So `length l` is the only measure we need; the code
-- argument takes care of the rest.

lsize : Conf → ℕ
lsize (a , e , l , m) = length l

-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalent to exec. The size measure defined above defines an upper
-- bound for how much fuel we have to provide.
mutual
  exec' : ∀ {i} → ℕ → Code → Conf → CTree⊥ None Conf i
  exec' k (CONST n c)  (a , e , l , m)      = exec' k c (Num' n , e , l , m)
  exec' k (ADD r c)    (Num' a , e , l , m) = do b ← get r m >>= getNum'
                                                 exec' k c (Num' (b + a) , e , l , m)
  exec' k (STORE r c)  (a , e , l , m)      = exec' k c (a , e , l , set r a m)
  exec' k (LOOKUP n c) (a , e , l , m)      = do v ← lookup n e
                                                 exec' k c (v , e , l , m)
  exec' k (APP r c)    (a , e , l , m)      = do c' , e' ← get r m >>= getClo'
                                                 later (∞exec' c' (a , a ∷ e' , m ∷ l , set first (Clo' c e) empty))
  exec' k (ABS c' c)   (a , e , l , m)      = exec' k c (Clo' c' e , e , l , m)
  exec' k RET          (a , e , [] , m)     = stuck
  exec' (suc k) RET    (a , e , m' ∷ l , m) = do c' , e' ← get first m >>= getClo'
                                                 exec' k c' (a , e' , l , m')
  exec' zero RET       (a , e , m' ∷ l , m) = ∅
  exec' k HALT         s                    = return s
  exec' k _            _                    = stuck

  ∞exec' : ∀ {i} → Code → Conf → ∞CTree⊥ None Conf i
  force (∞exec' c s) = exec' (lsize s) c s


-- Finally we show that exec' is equivalent to exec.

mutual
  execBisim : ∀ c s i → (k : ℕ) → (lsize s ≤ k) → exec c s ~[ i ] exec' k c s
  execBisim c s zero k le = ~izero
  execBisim (CONST n c) (a , e , l , m) (suc i) k le = execBisim c _ _ k le
  execBisim (ADD r c) (Num' a , e , l , m) (suc i) k le =
    ~i>>=-cong-r (get r m >>= getNum') (λ b → execBisim c _ _ k le)
  execBisim (ADD r c) (Clo' c' e' , _ , l , m) (suc i) k le = ~irefl
  execBisim (STORE r c) (a , e , l , m) (suc i) k le = execBisim c _ _ k le
  execBisim (LOOKUP n c) (a , e , l , m) (suc i) k le =
    ~i>>=-cong-r (lookup n e) (λ v → execBisim c _ _ k le)
  execBisim (APP r c) (a , e , l , m) (suc i) k le =
    ~i>>=-cong-r (get r m >>= getClo') (λ (c' , e') → ~ilater (∞execBisim c' _ _))
  execBisim (ABS c' c) (a , e , l , m) (suc i) k le = execBisim c _ _ k le
  execBisim RET (a , e , [] , m) (suc i) k le = ~irefl
  execBisim RET (a , e , m' ∷ l , m) (suc i) (suc k) (s≤s le) =
    ~i>>=-cong-r (get first m >>= getClo') (λ (c' , e') → execBisim c' _ _ k le)
  execBisim HALT s (suc i) k le = ~irefl

  ∞execBisim : ∀ c s i → force (∞exec c s) ~[ i ] force (∞exec' c s)
  ∞execBisim c s i = execBisim c s i (lsize s) ≤-refl


-- This shows that exec is bisimilar to exec'
bisimilar : DNE → ∀ c s → exec c s ~ exec' (lsize s) c s
bisimilar dne c s = ~i-~ dne λ i → execBisim c s i (lsize s) ≤-refl
