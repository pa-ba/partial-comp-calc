{-# OPTIONS --copatterns --sized-types --guardedness #-}


------------------------------------------------------------------------
-- Calculation for arithmetic expressions extended with conditionals
-- and a print effect.
------------------------------------------------------------------------

module Calculations.Stack.CondPrint where


open import CTree hiding (τ) public
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Agda.Builtin.Nat
open import Data.Bool 
open import Data.Product
open import Data.List hiding (lookup)
open import Function


-------------
-- Effects --
-------------

data PrintEff : Set → Set where
  PrintInt : ℕ → PrintEff ⊤


print : ∀ {i} → ℕ → CTree⊥ PrintEff ⊤ i
print n = eff (notStuck (PrintInt n)) return

---------------------
-- Source language --
---------------------


data Value : Set where
  N : ℕ → Value
  B : Bool → Value


data Expr : Set where
  Val   : Value → Expr
  Add   : Expr → Expr → Expr
  If    : Expr → Expr → Expr → Expr
  Print : Expr → Expr

-- The following two functions are used instead of partial pattern
-- matching. Agda supports an Idris-style pattern matching syntax
-- within the do notation, but that is useless for reasoning (see
-- https://agda.readthedocs.io/en/v2.6.2/language/lambda-abstraction.html)

getN : ∀ {i e} → Value → CTree⊥ e ℕ i
getN (N n) = return n
getN _ = stuck

getB : ∀ {i e} → Value → CTree⊥ e Bool i
getB (B b) = return b
getB _ = stuck


eval : ∀ {i} → Expr → CTree⊥ PrintEff Value i
eval (Val x) = return x
eval (Add x y) =
  do n ← eval x >>= getN
     m ← eval y >>= getN
     return (N (n + m))
eval (If c x y) =
  do b ← eval c >>= getB
     if b then eval x else eval y
eval (Print x) = 
  do n ← eval x >>= getN
     print n
     return (N n)

---------------------
-- Target language --
---------------------

data Code : Set where
  PUSH : Value → Code → Code
  ADD : Code → Code
  JPC : Code → Code → Code
  PRINT : Code → Code
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
comp (Print x) c = comp x (PRINT c)




-----------------
-- Calculation --
-----------------


mutual
  exec : ∀ {i} → Code → Stack → CTree⊥ PrintEff Stack i
  exec (PUSH v c) s = exec c (v ∷ s)
  exec (ADD c) (N n ∷ N m ∷ s) = exec c (N (m + n) ∷ s)
  exec (JPC c' c) (B b ∷ s) = if b then exec c' s else exec c s
  exec (PRINT c) (N n ∷ s) = print n >> exec c (N n ∷ s)
  exec HALT s = return s
  exec _ _ = stuck



open ⊥~i-Calculation

-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.

spec : ∀ i x {s c} →
  (do v ← eval x
      exec c (v ∷ s))
  ⊥~[ i ]
  (exec (comp x c) (s))
spec zero _ =  ⊥~izero
spec i (Val x) {s} {c} =
  (do v ← eval (Val x)
      exec c (v ∷ s))
  ≡⟨⟩
  (exec (PUSH x c) s )
  ∎
  
spec i (Add x y) {s} {c} =
  (do v ← eval (Add x y)
      exec c (v ∷ s))
  ≡⟨⟩
  (do v <- (do n ← eval x >>= getN
               m ← eval y >>= getN
               return (N (n + m)))
      exec c (v ∷ s))
  ~⟨ ~i>>=-assoc (eval x >>= getN) ⟩
  (do n ← eval x >>= getN
      v <- (do m ← eval y >>= getN
               return (N (n + m)))
      exec c (v ∷ s))
  ~⟨ ~i>>=-cong-r (eval x >>= getN) (\ n -> ~i>>=-assoc (eval y >>= getN))⟩
  (do n ← eval x >>= getN
      m ← eval y >>= getN
      exec c (N (n + m) ∷ s))
  ≡⟨⟩
  (do n ← eval x >>= getN
      m ← eval y >>= getN
      exec (ADD c) (N m ∷ N n ∷ s))
  ⊥~⟨  ⊥~i>>=-cong-r (eval x >>= getN) ( λ n →
        ⊥~itrans (⊥~i>>=-assoc (eval y)) ( ⊥~i>>=-cong-r (eval y) 
        (λ {(N m) → ⊥~irefl;
        (B _) → ⊥~istuck })))⟩
  (do n ← eval x >>= getN
      m ← eval y
      exec (ADD c) (m ∷ N n ∷ s))
  ⊥~⟨  ⊥~i>>=-cong-r (eval x >>= getN) (λ n → spec i y ) ⟩
  (do n ← eval x >>= getN
      exec (comp y (ADD c)) (N n ∷ s))
  ⊥~⟨  ⊥~itrans (⊥~i>>=-assoc (eval x)) (⊥~i>>=-cong-r (eval x)
     λ {(N x) → ⊥~irefl
      ; (B x) → ⊥~istuck}) ⟩
  (do v ← eval x
      exec (comp y (ADD c)) (v ∷ s))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (comp y (ADD c))) (s))
  ∎

spec i (If b x y) {s} {c} =
  (do v ← eval (If b x y)
      exec c (v ∷ s))
  ≡⟨⟩
  (do v ← do b' ← eval b >>= getB
             if b' then eval x else eval y
      exec c (v ∷ s))
  ~⟨ ~i>>=-assoc' (eval b >>= getB) (λ { true → ~irefl ; false → ~irefl}) ⟩
  (do b' ← eval b >>= getB
      (if b'
        then (eval x >>= λ v → exec c (v ∷ s))
        else (eval y >>= λ v → exec c (v ∷ s))))
  ⊥~⟨ ⊥~i>>=-cong-r (eval b >>= getB) (λ { true → spec i x ; false → spec i y}) ⟩
  (do b' ← eval b >>= getB
      (if b'
        then (exec (comp x c) s)
        else (exec (comp y c) s)))
  ~⟨ ~i>>=-assoc (eval b) ⟩
  (do v ← eval b
      b' ← getB v
      (if b'
        then (exec (comp x c) s)
        else (exec (comp y c) s)))
  ⊥~⟨ ⊥~i>>=-cong-r (eval b) (λ {(N x) → ⊥~istuck
                             ; (B x) → ⊥~irefl}) ⟩
  (do v ← eval b
      exec (JPC (comp x c) (comp y c)) (v ∷ s))
  ⊥~⟨ spec i b ⟩
  (exec (comp b (JPC (comp x c) (comp y c))) s)
  ∎  

spec i (Print x) {s} {c} =
  (do v ← eval (Print x)
      exec c (v ∷ s))
  ≡⟨⟩
  (do v <- (do n ← eval x >>= getN
               print n
               return (N n))
      exec c (v ∷ s))
  ~⟨ ~i>>=-assoc (eval x >>= getN) ⟩
  (do n ← eval x >>= getN
      print n
      exec c (N n ∷ s))
  ≡⟨⟩
  (do n ← eval x >>= getN
      exec (PRINT c) (N n ∷ s))
  ⊥~⟨ ⊥~itrans (⊥~i>>=-assoc (eval x)) (⊥~i>>=-cong-r (eval x)
     λ {(N x) → ⊥~irefl
      ; (B x) → ⊥~istuck}) ⟩
  (do v ← eval x
      exec (PRINT c) (v ∷ s))
  ⊥~⟨ spec i x ⟩
  (exec (comp x (PRINT c)) s)
  ∎


-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).
spec' : ∀ s c x →
  (do v ← eval x
      exec c (v ∷ s))
  ⊥~
  (exec (comp x c) s)
spec' s c x =  ⊥~i-⊥~  (λ i → spec i x)

------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT


specCompile : ∀ s x →
  (do v ← eval x
      return (v ∷ s))
  ⊥~
  (exec (compile x) s)
specCompile s x = spec' s HALT x


-- Well-typed terms never go wrong and are thus strongly bisimilar to
-- their compiled code.

-----------------
-- Type system --
-----------------

data type : Set where
  N : type
  B : type


infix 3 ⊢_∶_

mutual
  data ⊢v_∶_ : Value → type → Set where
    ⊢N : ∀ {n} → ⊢v N n ∶ N
    ⊢B : ∀ {b} → ⊢v B b ∶ B

data ⊢_∶_ : Expr → type → Set where
  ⊢val : ∀ {v τ} → ⊢v v ∶ τ → ⊢ Val v ∶ τ
  ⊢add : ∀ {x y} → ⊢ x ∶ N → ⊢ y ∶ N → ⊢ Add x y ∶ N
  ⊢if : ∀ {τ b x y} → ⊢ b ∶ B → ⊢ x ∶ τ → ⊢ y ∶ τ → ⊢ If b x y ∶ τ
  ⊢print : ∀ {x} → ⊢ x ∶ N → ⊢ Print x ∶ N




-- Well-typed terms are safe

eval-safe : ∀ {i t τ} → ⊢ t ∶ τ → safeP {i} (λ v → ⊢v v ∶ τ ) (eval t)
eval-safe (⊢val ⊢N) = spnow ⊢N
eval-safe (⊢val ⊢B) = spnow ⊢B
eval-safe (⊢add T1 T2) = safeP->>= (safeP->>= (eval-safe T1) λ { ⊢N → spnow tt}) 
                        λ _ → safeP->>= (safeP->>= (eval-safe T2) λ {⊢N → spnow tt})
                        λ _ → spnow ⊢N
eval-safe (⊢if Tb Tx Ty) = safeP->>= (safeP->>= (eval-safe Tb) λ {⊢B → spnow tt}) 
                        λ { {v = false} - → eval-safe Ty
                          ; {v = true} _ → eval-safe Tx}
eval-safe (⊢print Tx) = safeP->>= (safeP->>= (eval-safe Tx) (λ { ⊢N → spnow tt}))
                         λ {n} _ → (speff {e = PrintInt n} (λ _ → spnow ⊢N ))


-- stronger version of the compiler correctness property for
-- well-typed terms

specCompileTyped : ∀ s x τ →
  ⊢ x ∶ τ →
  (do v ← eval x
      return (v ∷ s))
  ~
  (exec (compile x) s)
specCompileTyped s x τ T = ⊥~-~ (safeP->>= (eval-safe T) λ _ → spnow _) (specCompile s x)
    