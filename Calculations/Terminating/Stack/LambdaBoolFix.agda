{-# OPTIONS --sized-types #-}

-- Here we give a separate proof that the virtual machine exec for the
-- lambda calculus extended with fixed points and Boolean is indeed
-- well-defined.

module Calculations.Terminating.Stack.LambdaBoolFix where

open import Calculations.Stack.LambdaBoolFix

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Nat

open import Data.Product 
open import Data.List hiding (lookup)
open import Data.Bool hiding (_≤_)

-- Define the measure that is used to show that exec is well-founded

csize : Code → ℕ
csize (PUSH x c) =  suc (csize c)
csize (ADD c) =  suc (csize c)
csize (LOOKUP x c) = suc (csize c)
csize RET = 1
csize (APP c) = suc (csize c)
csize (ABS c c') = suc (csize c + csize c')
csize (BPUSH b c) = suc (csize c)
csize (EQ c) = suc (csize c)
csize (IF c c') = suc (csize c + csize c')
csize (FIX c) = suc (csize c)
csize HALT = 1


ssize : Stack → ℕ
ssize [] = 0
ssize (VAL x ∷ s) =  ssize s
ssize (CLO c e ∷ s) =  csize c + ssize s


fsize : Conf → ℕ
fsize (s , e) =  ssize s

-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalen to exec. The size measure defined above defines an upper
-- bound for how much fuel we have to provide.
mutual
  exec' : ∀ {i} → ℕ → Code → Conf → CTree⊥ None Conf i
  exec' 0 _ _ = ∅
  exec' (suc j) (PUSH n c)   (s , e)                                = exec' j c (VAL (Num' n) ∷ s , e)
  exec' (suc j) (BPUSH b c)  (s , e)                                = exec' j c (VAL (B' b) ∷ s , e)
  exec' (suc j) (ADD c)      (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e)  = exec' j c (VAL (Num' (m + n)) ∷ s , e)
  exec' (suc j) (EQ c)       (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e)  = exec' j c (VAL (B' (m ≡ᵇ n)) ∷ s , e)
  exec' (suc j) (IF c c')    (VAL (B' true) ∷ s , e)                = exec' j c (s , e)
  exec' (suc j) (IF c c')    (VAL (B' false) ∷ s , e)               = exec' j c' (s , e)
  exec' (suc j) (LOOKUP n c) (s , e)                                = do v ← lookup n e; exec' j c (VAL v ∷ s , e)
  exec' (suc j) (ABS c' c)   (s , e)                                = exec' j c (VAL (Clo' c' e) ∷ s , e)
  exec' (suc j) (FIX c)      (s , e)                                = exec' j c (VAL (Clo' (LOOKUP 0 (FIX (LOOKUP 0 (APP (APP RET))))) e) ∷ s , e)
  exec' (suc j) RET          (VAL u ∷ CLO c e' ∷ s , _)             = exec' j c (VAL u ∷ s , e')
  exec' _ (APP c)      (VAL v ∷ VAL (Clo' c' e') ∷ s , e)           = later (∞exec' c' (CLO c e ∷ s , v ∷ e'))
  exec' _ HALT         (s , e)                                      = return (s , e)
  exec' _ _            _                                            = stuck

  ∞exec' : ∀ {i} → Code → Conf → ∞CTree⊥ None Conf i
  force (∞exec' c e) = exec' (csize c + fsize e) c e

open ≤-Reasoning


lemma : ∀ a b c j → c + a + b ≤ j → a + b ≤ j
lemma a b c j le = begin
                   a + b
                   ≤⟨ m≤n+m (a + b) c ⟩
                   c + (a + b)
                   ≡˘⟨  +-assoc c a b ⟩
                   c + a + b
                   ≤⟨  le ⟩
                   j 
                   ∎

lemma' : ∀ a b c j → a + b + c ≤ j → a + 0 ≤ j
lemma' a b c j le = begin
                    a + 0
                    ≤⟨ +-mono-≤ ≤-refl (z≤n) ⟩
                    a + (b + c) 
                    ≡˘⟨  +-assoc a b c ⟩
                    a + b + c
                    ≤⟨ le ⟩
                    j
                    ∎

lemmaIF : ∀ a b c j → a + b + c ≤ j → a + c ≤ j
lemmaIF a b c j le = begin
                     a + c
                     ≤⟨ +-mono-≤ ≤-refl (m≤n+m c b) ⟩
                     a + (b + c)
                     ≡˘⟨ +-assoc a b c ⟩
                     a + b + c
                     ≤⟨ le ⟩
                     j
                     ∎


-- Finally we show that exec' is equivalent to exec.

mutual
  execBisim : ∀ c e i → (j : ℕ) → (csize c + fsize e ≤ j) → exec c e ~[ i ] exec' j c e
  execBisim c e zero j le = ~izero
  execBisim (PUSH x c) (s , e) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (BPUSH x c) (s , e) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (ADD c) ([] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ [] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Num' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = execBisim c _ _ _ le
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (B' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Clo' x₁ x₂) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ CLO x₁ x₂ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (B' x) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (VAL (Clo' x x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ADD c) (CLO x x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) ([] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (Num' x) ∷ [] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (Num' x) ∷ VAL (Num' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = execBisim c _ _ _ le
  execBisim (EQ c) (VAL (Num' x) ∷ VAL (B' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (Num' x) ∷ VAL (Clo' x₁ x₂) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (Num' x) ∷ CLO x₁ x₂ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (B' x) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (VAL (Clo' x x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (EQ c) (CLO x x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (LOOKUP x c) (s , e) (suc i) .(suc _) (s≤s le) = ~i>>=-cong-r (lookup x e) (λ a → execBisim c _ _ _ le)
  execBisim RET ([] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ [] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ VAL x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ CLO c x₂ ∷ s , e) (suc i) .(suc _) (s≤s le) = execBisim c _ _ _ le
  execBisim RET (CLO x x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) ([] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ [] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ VAL (Num' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ VAL (B' x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ VAL (Clo' c' x₂) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~ilater (∞execBisim c' _ _)
  execBisim (APP c) (VAL x ∷ CLO x₁ x₂ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (APP c) (CLO x x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (ABS c' c) (s , e) (suc i) (suc j) (s≤s le) = execBisim c _ _ j (lemma (csize c) (ssize s) (csize c') j le)  
  execBisim (IF c c') ([] , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (IF c c') (VAL (Num' x) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (IF c c') (VAL (B' true) ∷ s , e) (suc i) (suc j) (s≤s le) = execBisim c _ _ j (lemmaIF (csize c) (csize c') (ssize s) j le)
  execBisim (IF c c') (VAL (B' false) ∷ s , e) (suc i) (suc j) (s≤s le) = execBisim c' _ _ j (lemma (csize c') (ssize s) (csize c) j le)
  execBisim (IF c c') (VAL (Clo' x x₁) ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (IF c c') (CLO x x₁ ∷ s , e) (suc i) .(suc _) (s≤s le) = ~irefl
  execBisim (FIX c) (s , e) (suc i) .(suc _) (s≤s le) = execBisim c _ _ _ le
  execBisim HALT (s , e) (suc i) _ (s≤s le) =  ~irefl
  
  ∞execBisim : ∀ c e i → force (∞exec c e) ~[ i ] force (∞exec' c e)
  ∞execBisim c e i =  execBisim c _ _ (csize c + fsize e) ≤-refl



-- This shows that exec is bisimilar to exec'
bisimilar : DNE → ∀ c e →  exec c e ~ exec' (csize c + fsize e) c e
bisimilar dne c e = ~i-~ dne λ i → execBisim c e i (csize c + fsize e) ≤-refl
