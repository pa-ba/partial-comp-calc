{-# OPTIONS --safe #-}


------------------------------------------------------------------------
-- Calculation for arithmetic expressions extended with conditionals,
-- using the `Maybe` monad to model unsafe behaviour. This is the
-- calculation of section 2 of the paper, and the resulting definitions
-- are those of Figure 1.
--
-- Calculations.Stack.Cond redoes the same calculation with choice
-- trees, which is what section 4.1 of the paper does for the language
-- extended with a print effect.
------------------------------------------------------------------------

module Calculations.Maybe.Cond where


open import Maybe public
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.List

---------------------
-- Source language --
---------------------

data Value : Set where
  N : ℕ → Value
  B : Bool → Value


data Expr : Set where
  Val : Value → Expr
  Add : Expr → Expr → Expr
  If : Expr → Expr → Expr → Expr


-- The following two functions are used instead of the partial pattern
-- matching that the paper writes as `do N m ← eval x; ...`. They make
-- the `fail` case of the MonadFail instance for `Maybe` explicit.

getN : Value → Maybe ℕ
getN (N n) = return n
getN _ = nothing

getB : Value → Maybe Bool
getB (B b) = return b
getB _ = nothing


eval : Expr → Maybe Value
eval (Val x) = return x
eval (Add x y) =
  do n ← eval x >>= getN
     m ← eval y >>= getN
     return (N (n + m))
eval (If c x y) =
  do b ← eval c >>= getB
     if b then eval x else eval y

---------------------
-- Target language --
---------------------

data Code : Set where
  PUSH : Value → Code → Code
  ADD : Code → Code
  JPC : Code → Code → Code
  HALT : Code

Stack : Set
Stack = List Value


--------------
-- Compiler --
--------------

comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (If b x y) c = comp b (JPC (comp x c) (comp y c))


-----------------
-- Calculation --
-----------------

exec : Code → Stack → Maybe Stack
exec (PUSH v c) s = exec c (v ∷ s)
exec (ADD c) (N n ∷ N m ∷ s) = exec c (N (m + n) ∷ s)
exec (JPC c' c) (B b ∷ s) = if b then exec c' s else exec c s
exec HALT s = return s
exec _ _ = nothing


open ⊥=-Calculation

-- This is the compiler correctness property (equation 5 in the
-- paper). This is where the calculation happens. Steps written with
-- ≡⟨_⟩ are equalities, i.e. they use only the definitions and the
-- monad laws; steps written with ⊥=⟨_⟩ are where unsafe behaviour is
-- disregarded, i.e. where the (⊥=-Nothing) law is used.

spec : ∀ x {s c} →
  (do v ← eval x
      exec c (v ∷ s))
  ⊥=
  (exec (comp x c) s)

spec (Val x) {s} {c} =
  (do v ← eval (Val x)
      exec c (v ∷ s))
  ≡⟨⟩
  (exec (PUSH x c) s)
  ∎

spec (Add x y) {s} {c} =
  (do v ← eval (Add x y)
      exec c (v ∷ s))
  ≡⟨⟩
  (do v ← (do n ← eval x >>= getN
              m ← eval y >>= getN
              return (N (n + m)))
      exec c (v ∷ s))
  ≡⟨ >>=-assoc (eval x >>= getN) ⟩
  (do n ← eval x >>= getN
      v ← (do m ← eval y >>= getN
              return (N (n + m)))
      exec c (v ∷ s))
  ≡⟨ >>=-cong-r (eval x >>= getN) (λ n → >>=-assoc (eval y >>= getN)) ⟩
  (do n ← eval x >>= getN
      m ← eval y >>= getN
      exec c (N (n + m) ∷ s))
  ≡⟨⟩
  (do n ← eval x >>= getN
      m ← eval y >>= getN
      exec (ADD c) (N m ∷ N n ∷ s))
  ⊥=⟨ ⊥=->>=-cong-r (eval x >>= getN) (λ n →
        ⊥=-trans (≡-⊥= (>>=-assoc (eval y))) (⊥=->>=-cong-r (eval y)
        (λ {(N m) → ⊥=-refl;
            (B _) → ⊥=-nothing }))) ⟩
  (do n ← eval x >>= getN
      m ← eval y
      exec (ADD c) (m ∷ N n ∷ s))
  ⊥=⟨ ⊥=->>=-cong-r (eval x >>= getN) (λ n → spec y ) ⟩
  (do n ← eval x >>= getN
      exec (comp y (ADD c)) (N n ∷ s))
  ⊥=⟨ ⊥=-trans (≡-⊥= (>>=-assoc (eval x))) (⊥=->>=-cong-r (eval x)
     (λ {(N n) → ⊥=-refl
       ; (B _) → ⊥=-nothing})) ⟩
  (do v ← eval x
      exec (comp y (ADD c)) (v ∷ s))
  ⊥=⟨ spec x ⟩
  (exec (comp x (comp y (ADD c))) s)
  ∎

spec (If b x y) {s} {c} =
  (do v ← eval (If b x y)
      exec c (v ∷ s))
  ≡⟨⟩
  (do v ← do b' ← eval b >>= getB
             if b' then eval x else eval y
      exec c (v ∷ s))
  ≡⟨ trans (>>=-assoc (eval b >>= getB))
           (>>=-cong-r (eval b >>= getB) (λ { true → refl ; false → refl})) ⟩
  (do b' ← eval b >>= getB
      (if b'
        then (eval x >>= λ v → exec c (v ∷ s))
        else (eval y >>= λ v → exec c (v ∷ s))))
  ⊥=⟨ ⊥=->>=-cong-r (eval b >>= getB) (λ { true → spec x ; false → spec y}) ⟩
  (do b' ← eval b >>= getB
      (if b'
        then (exec (comp x c) s)
        else (exec (comp y c) s)))
  ≡⟨ >>=-assoc (eval b) ⟩
  (do v ← eval b
      b' ← getB v
      (if b'
        then (exec (comp x c) s)
        else (exec (comp y c) s)))
  ⊥=⟨ ⊥=->>=-cong-r (eval b) (λ {(N _) → ⊥=-nothing
                              ; (B _) → ⊥=-refl}) ⟩
  (do v ← eval b
      exec (JPC (comp x c) (comp y c)) (v ∷ s))
  ⊥=⟨ spec b ⟩
  (exec (comp b (JPC (comp x c) (comp y c))) s)
  ∎


------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT


specCompile : ∀ s x →
  (do v ← eval x
      return (v ∷ s))
  ⊥=
  (exec (compile x) s)
specCompile s x = spec x
