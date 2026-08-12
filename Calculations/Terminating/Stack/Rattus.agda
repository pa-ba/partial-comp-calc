{-# OPTIONS --sized-types #-}

-- Here we give a separate proof that the virtual machine exec for the
-- RaTT language is indeed well-defined.

module Calculations.Terminating.Stack.Rattus where

open import Calculations.Stack.Rattus

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Nat

open import Data.Product 
open import Data.List hiding (lookup)

-- Define the measure that is used to show that exec is well-founded

csize : Code → ℕ
csize (PUSH x c)    = suc (csize c)
csize (ADD c)       = suc (csize c)
csize (PAIR c)      = suc (csize c)
csize (PR1 c)       = suc (csize c)
csize (PR2 c)       = suc (csize c)
csize (IN1 c)       = suc (csize c)
csize (IN2 c)       = suc (csize c)
csize (ENDCASE c)   = suc (csize c)
csize (CASE c1 c2)  = suc (csize c1 + csize c2)
csize (LOOKUP x c)  = suc (csize c)
csize RET           = 1
csize (APP c)       = suc (csize c)
csize (ABS c c')    = suc (csize c + csize c')
csize (ADV c)       = suc (csize c)
csize (ENDADV c)    = suc (csize c)
csize (DELAY c c')  = suc (csize c + csize c')
csize (UNBOX c)     = suc (csize c)
csize (BOX c c')    = suc (csize c + csize c')
csize (FIX c)       = suc (csize c)
csize (INTO c)      = suc (csize c)
csize (OUT c)       = suc (csize c)
csize (UNIT c)      = suc (csize c)
csize HALT          = 1


ssize : Stack → ℕ
ssize []             = 0
ssize (VAL x ∷ s)   = ssize s
ssize (CLO c e ∷ s) = csize c + ssize s
ssize (HEAP η ∷ s)  = ssize s


fsize : Conf → ℕ
fsize (s , e , σ) = ssize s

-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalent to exec. The size measure defined above defines an upper
-- bound for how much fuel we have to provide.
mutual
  exec' : ∀ {i} → ℕ → Code → Conf → CTree⊥ None Conf i
  exec' 0 _ _ = ∅
  exec' (suc j) (PUSH n c)    (s , e , σ)                               = exec' j c (VAL (Num' n) ∷ s , e , σ)
  exec' (suc j) (ADD c)       (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e , σ) = exec' j c (VAL (Num' (m + n)) ∷ s , e , σ)
  exec' (suc j) (PAIR c)      (VAL v2 ∷ VAL v1 ∷ s , e , σ)             = exec' j c (VAL (Pair' v1 v2) ∷ s , e , σ)
  exec' (suc j) (PR1 c)       (VAL (Pair' v1 v2) ∷ s , e , σ)           = exec' j c (VAL v1 ∷ s , e , σ)
  exec' (suc j) (PR2 c)       (VAL (Pair' v1 v2) ∷ s , e , σ)           = exec' j c (VAL v2 ∷ s , e , σ)
  exec' (suc j) (IN1 c)       (VAL v ∷ s , e , σ)                       = exec' j c (VAL (In1' v) ∷ s , e , σ)
  exec' (suc j) (IN2 c)       (VAL v ∷ s , e , σ)                       = exec' j c (VAL (In2' v) ∷ s , e , σ)
  exec' (suc j) (LOOKUP n c)  (s , e , σ)                               = do v ← lookup n e; exec' j c (VAL v ∷ s , e , σ)
  exec' (suc j) (ABS c' c)    (s , e , σ)                               = exec' j c (VAL (Clo' c' e) ∷ s , e , σ)
  exec' (suc j) RET           (VAL u ∷ CLO c e' ∷ s , _ , σ)            = exec' j c (VAL u ∷ s , e' , σ)
  exec' _ (APP c)       (VAL v ∷ VAL (Clo' c' e') ∷ s , e , σ)          = later (∞exec' c' (CLO c e ∷ s , v ∷ e' , σ))
  exec' (suc j) (ADV c)       (s , e , ⟨ ηN ✓ ηL ⟩)                     = exec' j c (HEAP ηL ∷ s , e , ⟨ ηN ⟩)
  exec' _ (ENDADV c)    (VAL (Loc' l) ∷ HEAP ηL ∷ s , e , ⟨ ηN ⟩)       = do c' , e' ← lookup l ηN; later (∞exec' c' (CLO c e ∷ s , e' , ⟨ ηN ✓ ηL ⟩))
  exec' (suc j) (DELAY c' c)  (s , e , σ)                               = let l , σ' = allocS σ (c' , e) in exec' j c (VAL (Loc' l) ∷ s , e , σ')
  exec' _ (UNBOX c)     (VAL (Box' c' e') ∷ s , e , σ)                  = later (∞exec' c' (CLO c e ∷ s , e' , σ))
  exec' (suc j) (BOX c' c)    (s , e , σ)                               = exec' j c (VAL (Box' c' e) ∷ s , e , σ)
  exec' (suc j) (FIX c)       (s , e , σ)                               = exec' j c (VAL (Clo' (LOOKUP 0 (BOX (DELAY (FIX (LOOKUP 0 (APP RET))) RET) (APP RET))) e) ∷ s , e , σ)
  exec' (suc j) (ENDCASE c)   (s , v ∷ e , σ)                           = exec' j c (s , e , σ)
  exec' (suc j) (CASE c1 c2)  (VAL (In1' v) ∷ s , e , σ)                = exec' j c1 (s , v ∷ e , σ)
  exec' (suc j) (CASE c1 c2)  (VAL (In2' v) ∷ s , e , σ)                = exec' j c2 (s , v ∷ e , σ)
  exec' (suc j) (INTO c)      (VAL v ∷ s , e , σ)                       = exec' j c (VAL (Into' v) ∷ s , e , σ)
  exec' (suc j) (OUT c)       (VAL (Into' v) ∷ s , e , σ)               = exec' j c (VAL v ∷ s , e , σ)
  exec' (suc j) (UNIT c)      (s , e , σ)                               = exec' j c (VAL Unit' ∷ s , e , σ)
  exec' _ HALT          (s , e , σ)                                     = return (s , e , σ)
  exec' _ _             _                                               = stuck

  ∞exec' : ∀ {i} → Code → Conf → ∞CTree⊥ None Conf i
  force (∞exec' c conf) = exec' (csize c + fsize conf) c conf

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

lemma-l : ∀ a b c j → a + b + c ≤ j → a + c ≤ j
lemma-l a b c j le = begin
                     a + c
                     ≤⟨ +-mono-≤ (m≤n+m a b) ≤-refl ⟩
                     b + a + c
                     ≡⟨ cong (_+ c) (+-comm b a) ⟩
                     a + b + c
                     ≤⟨ le ⟩
                     j
                     ∎


-- Finally we show that exec' is equivalent to exec.

mutual
  execBisim : ∀ c e i → (j : ℕ) → (csize c + fsize e ≤ j) → exec c e ~[ i ] exec' j c e
  execBisim c e zero j le = ~izero
  execBisim (PUSH x c)    (s , e , σ) (suc i) _ (s≤s le)             = execBisim c _ _ _ le
  execBisim (ADD c)       (VAL (Num' x) ∷ VAL (Num' x₁) ∷ s , e , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (PAIR c)      (VAL v2 ∷ VAL v1 ∷ s , e , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (PR1 c)       (VAL (Pair' v1 v2) ∷ s , e , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (PR2 c)       (VAL (Pair' v1 v2) ∷ s , e , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (IN1 c)       (VAL v ∷ s , e , σ) (suc i) _ (s≤s le)    = execBisim c _ _ _ le
  execBisim (IN2 c)       (VAL v ∷ s , e , σ) (suc i) _ (s≤s le)    = execBisim c _ _ _ le
  execBisim (LOOKUP x c)  (s , e , σ) (suc i) _ (s≤s le)            = ~i>>=-cong-r (lookup x e) (λ a → execBisim c _ _ _ le)
  execBisim (ABS c' c)    (s , e , σ) (suc i) (suc j) (s≤s le)      = execBisim c _ _ j (lemma (csize c) (ssize s) (csize c') j le)
  execBisim RET           (VAL x ∷ CLO c e' ∷ s , _ , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (APP c)       (VAL x ∷ VAL (Clo' c' x₂) ∷ s , e , σ) (suc i) .(suc _) (s≤s le) = ~ilater (∞execBisim c' _ _)
  execBisim (ADV c)       (s , e , ⟨ ηN ✓ ηL ⟩) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (ENDADV c)    (VAL (Loc' l) ∷ HEAP ηL ∷ s , e , ⟨ ηN ⟩) (suc i) .(suc _) (s≤s le) = ~i>>=-cong-r (lookup l ηN) (λ (c' , e') → ~ilater (∞execBisim c' _ _))
  execBisim (DELAY c' c)  (s , e , σ) (suc i) (suc j) (s≤s le)      = execBisim c _ _ j (lemma (csize c) (ssize s) (csize c') j le)
  execBisim (UNBOX c)     (VAL (Box' c' e') ∷ s , e , σ) (suc i) .(suc _) (s≤s le) = ~ilater (∞execBisim c' _ _)
  execBisim (BOX c' c)    (s , e , σ) (suc i) (suc j) (s≤s le)      = execBisim c _ _ j (lemma (csize c) (ssize s) (csize c') j le)
  execBisim (FIX c)       (s , e , σ) (suc i) _ (s≤s le)            = execBisim c _ _ _ le
  execBisim (ENDCASE c)   (s , v ∷ e , σ) (suc i) _ (s≤s le)        = execBisim c _ _ _ le
  execBisim (CASE c1 c2)  (VAL (In1' v) ∷ s , e , σ) (suc i) (suc j) (s≤s le) = execBisim c1 _ _ j (lemma-l (csize c1) (csize c2) (ssize s) j le)
  execBisim (CASE c1 c2)  (VAL (In2' v) ∷ s , e , σ) (suc i) (suc j) (s≤s le) = execBisim c2 _ _ j (lemma (csize c2) (ssize s) (csize c1) j le)
  execBisim (INTO c)      (VAL v ∷ s , e , σ) (suc i) _ (s≤s le)    = execBisim c _ _ _ le
  execBisim (OUT c)       (VAL (Into' v) ∷ s , e , σ) (suc i) _ (s≤s le) = execBisim c _ _ _ le
  execBisim (UNIT c)      (s , e , σ) (suc i) _ (s≤s le)            = execBisim c _ _ _ le
  execBisim (ADD c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                        = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ [] , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)       = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)       = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)         = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)      = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)         = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)         = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)        = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)            = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)              = ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)               = ~irefl
  execBisim (ADD c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (ADD c) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (ADD c) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (ADD c) (VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (ADD c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (ADD c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (ADD c) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                       = ~irefl
  execBisim (ADD c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (ADD c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (ADD c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (PAIR c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                      = ~irefl
  execBisim (PAIR c) (VAL _ ∷ [] , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (PAIR c) (VAL _ ∷ CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                    = ~irefl
  execBisim (PAIR c) (VAL _ ∷ HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (PAIR c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                            = ~irefl
  execBisim (PAIR c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (PR1 c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (PR1 c) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR1 c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (PR1 c) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (PR1 c) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR1 c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR1 c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR1 c) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                       = ~irefl
  execBisim (PR1 c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (PR1 c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (PR1 c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (PR2 c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (PR2 c) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR2 c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (PR2 c) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (PR2 c) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR2 c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR2 c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (PR2 c) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                       = ~irefl
  execBisim (PR2 c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (PR2 c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (PR2 c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (IN1 c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (IN1 c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (IN1 c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (IN2 c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (IN2 c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (IN2 c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim RET ([] , e , σ) (suc i) .(suc _) (s≤s le)                                           = ~irefl
  execBisim RET (VAL _ ∷ [] , e , σ) (suc i) .(suc _) (s≤s le)                                  = ~irefl
  execBisim RET (VAL _ ∷ VAL _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim RET (VAL _ ∷ HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                          = ~irefl
  execBisim RET (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                                 = ~irefl
  execBisim RET (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                                  = ~irefl
  execBisim (APP c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (APP c) (VAL _ ∷ [] , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)              = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)             = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)               = ~irefl
  execBisim (APP c) (VAL _ ∷ VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (APP c) (VAL _ ∷ CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (APP c) (VAL _ ∷ HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (APP c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (APP c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim (ADV c) (s , e , ⟨ _ ⟩) (suc i) .(suc _) (s≤s le)                                   = ~irefl
  execBisim (ENDADV c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                    = ~irefl
  execBisim (ENDADV c) (VAL (Loc' _) ∷ [] , e , σ) (suc i) .(suc _) (s≤s le)                    = ~irefl
  execBisim (ENDADV c) (VAL (Loc' _) ∷ VAL _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)             = ~irefl
  execBisim (ENDADV c) (VAL (Loc' _) ∷ CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)           = ~irefl
  execBisim (ENDADV c) (VAL (Loc' _) ∷ HEAP _ ∷ s , e , ⟨ _ ✓ _ ⟩) (suc i) .(suc _) (s≤s le)   = ~irefl
  execBisim (ENDADV c) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (ENDADV c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (ENDADV c) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (ENDADV c) (VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                  = ~irefl
  execBisim (ENDADV c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (ENDADV c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (ENDADV c) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                    = ~irefl
  execBisim (ENDADV c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (ENDADV c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                          = ~irefl
  execBisim (ENDADV c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (UNBOX c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                     = ~irefl
  execBisim (UNBOX c) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (UNBOX c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                    = ~irefl
  execBisim (UNBOX c) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (UNBOX c) (VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (UNBOX c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (UNBOX c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (UNBOX c) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (UNBOX c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                         = ~irefl
  execBisim (UNBOX c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (UNBOX c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                            = ~irefl
  execBisim (ENDCASE c) (s , [] , σ) (suc i) .(suc _) (s≤s le)                                   = ~irefl
  execBisim (CASE c1 c2) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                  = ~irefl
  execBisim (CASE c1 c2) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (CASE c1 c2) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                 = ~irefl
  execBisim (CASE c1 c2) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                 = ~irefl
  execBisim (CASE c1 c2) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                   = ~irefl
  execBisim (CASE c1 c2) (VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                = ~irefl
  execBisim (CASE c1 c2) (VAL (Into' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                  = ~irefl
  execBisim (CASE c1 c2) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (CASE c1 c2) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (CASE c1 c2) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                         = ~irefl
  execBisim (INTO c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                      = ~irefl
  execBisim (INTO c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                            = ~irefl
  execBisim (INTO c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (OUT c) ([] , e , σ) (suc i) .(suc _) (s≤s le)                                       = ~irefl
  execBisim (OUT c) (VAL (Num' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (OUT c) (VAL (Clo' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (OUT c) (VAL (Box' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                      = ~irefl
  execBisim (OUT c) (VAL (Loc' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (OUT c) (VAL (Pair' _ _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                     = ~irefl
  execBisim (OUT c) (VAL (In1' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (OUT c) (VAL (In2' _) ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                        = ~irefl
  execBisim (OUT c) (VAL Unit' ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                           = ~irefl
  execBisim (OUT c) (CLO _ _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                             = ~irefl
  execBisim (OUT c) (HEAP _ ∷ s , e , σ) (suc i) .(suc _) (s≤s le)                              = ~irefl
  execBisim HALT          (s , e , σ) (suc i) _ (s≤s _)                                          = ~irefl

  ∞execBisim : ∀ c e i → force (∞exec c e) ~[ i ] force (∞exec' c e)
  ∞execBisim c e i = execBisim c _ _ (csize c + fsize e) ≤-refl



-- This shows that exec is bisimilar to exec'
bisimilar : DNE → ∀ c e →  exec c e ~ exec' (csize c + fsize e) c e
bisimilar dne c e = ~i-~ dne λ i → execBisim c e i (csize c + fsize e) ≤-refl
