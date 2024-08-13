{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for the simple arithmetic language with a print
-- instruction.
------------------------------------------------------------------------

module Calculations.Memory.Print where

open import Relation.Binary.PropositionalEquality
open import CTree
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Unit


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

data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Print : Expr → Expr


mutual
  eval : ∀ {i} → Expr → CTree⊥ PrintEff ℕ i
  eval (Val n) = return n
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval (Print x)  = 
    do n ← eval x
       print n 
       return n

  ∞eval : ∀ {i} → Expr → ∞CTree⊥ PrintEff ℕ i
  force (∞eval x) = eval x
  
---------------------
-- Target language --
---------------------

data Code : Set where
  LOAD : ℕ → Code → Code
  STORE : Reg → Code → Code
  ADD : Reg → Code → Code
  PRINT : Code → Code
  HALT : Code


Conf : Set
Conf = ℕ × (Memory ℕ)


mutual
  exec : ∀ {i} → Code → Conf → CTree⊥ PrintEff Conf i
  exec (LOAD n c) (a , m) = exec c (n , m)
  exec (STORE r c) (a , m) = exec c (a , m #[ r ← a ])
  exec (ADD r c) (a , m) = do b ← get m r
                              exec c (b + a , m)
  exec (PRINT c) (n , m) = do print n
                              exec c (n , m)
  exec HALT s = return s


  ∞exec : ∀ {i} → Code → Conf → ∞CTree⊥ PrintEff Conf i
  force (∞exec e x) = exec e x

--------------
-- Compiler --
--------------


comp : Expr → Reg → Code → Code
comp (Val n) r c =  LOAD n c
comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))
comp (Print x) r c = comp x r (PRINT c)



exec-mono : ∀ {i}  {a} {m m' : Memory ℕ} c → m ⊑ m' → exec c (a , m) ⊥≲[ i ] exec c (a , m')
exec-mono {i = zero} _ l = ⊥≲izero
exec-mono (LOAD x c) l =  exec-mono c l
exec-mono (STORE x c) l = exec-mono c (set-monotone l)
exec-mono (ADD x c) l = ⊥≲i>>=-cong (⊥≲iget l)  λ {refl → exec-mono c l}
exec-mono {i} {a} (PRINT c) l = ⊥≲i>>=-cong-r (print a) λ {_ → exec-mono c l} 
-- ⊥≲i>>=-cong (⊥≲ieff (notStuck (PrintInt _)) λ _ → ⊥≲irefl) λ {refl → exec-mono c l}
-- ⊥≲i>>=-cong (⊥≲iget l)  λ {refl → exec-mono c l}
exec-mono HALT l = ⊥≲i⊑ (refl , l)


-----------------
-- Calculation --
-----------------

open ⊥≲i-Calculation

-- This is the compiler correctness property in its i-bisimilarity
-- form. This is where the calculation happens.


spec : ∀ i x r {a m c} →
  freeFrom r m →
  (do v ← eval x
      exec c (v , m))
  ⊥≲[ i ]
  (exec (comp x r c) (a , m))
spec zero _ _ _ =  ≲izero
spec i (Val x) r {a} {m} {c} F =
   (do v ← return x
       exec c (v , m))
   ≡⟨⟩
   exec c (x , m)
   ≡⟨⟩
   (exec (LOAD x c) (a , m))
  ∎

spec i (Add x y) r {a} {m} {c} F = 
  (do v ← (do n1 ← eval x
              n2 ← eval y
              return (n1 + n2))
      exec c (v , m))
  ~⟨  ~i>>=-assoc (eval x) ⟩
  (do n1 ← eval x
      v ← (do n2 ← eval y
              return (n1 + n2))
      exec c (v , m))
  ~⟨ ~i>>=-cong-r (eval x) (λ _ → ~i>>=-assoc (eval y)) ⟩
  (do n1 ← eval x
      n2 ← eval y
      exec c (n1 + n2 , m))
  ⊥≲⟨ ⊥≲i>>=-cong-r (eval x) (λ n1 →  ⊥≲i>>=-cong-r (eval y)
     (λ n2 → exec-mono c (⊑-set F))) ⟩
  (do n1 ← eval x
      n2 ← eval y
      exec c (n1 + n2 , m #[ r ← n1 ]))
  ~⟨  ~i>>=-cong-r (eval x) (λ n1 →  ~i>>=-cong-r (eval y)
     (λ n2 →  ~isym (~iset-get->>= {r = r}))) ⟩
  (do n1 ← eval x
      n2 ← eval y
      exec (ADD r c) (n2 , m #[ r ← n1 ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x) (λ n1 → spec i y (next r) (freeFromSet F)) ⟩
  (do n1 ← eval x
      exec (comp y (next r) (ADD r c)) (n1 , m #[ r ← n1 ]))
  ≡⟨⟩
    (do n1 ← eval x
        exec (STORE r (comp y (next r) (ADD r c))) (n1 , m))
  ⊥≲⟨ spec i x r F ⟩
  exec (comp x r (STORE r (comp y (next r) (ADD r c)))) (a , m)
  ∎



spec i (Print x) r {a} {m} {c} F = 
  (do v ← (do n ← eval x
              print n
              return n)
      exec c (v , m))
  ~⟨  ~i>>=-assoc (eval x) ⟩
  (do n ← eval x
      print n
      exec c (n , m))
  ≡⟨⟩
  (do n ← eval x
      exec (PRINT c) (n , m))
  ⊥≲⟨ spec i x r F ⟩
  (exec (comp x r (PRINT c)) (a , m))
  ∎

-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).

spec' : ∀ x r {a m c} → freeFrom r m →
  (do v ← eval x
      exec c (v , m))
  ⊥≲
  (exec (comp x r c) (a , m))
spec' x r F =  ⊥≲i-⊥≲  (λ i → spec i  x  r F)




mutual
  eval-safe : ∀ {i} t → safe {i} (eval t)
  eval-safe (Val x) = spnow _
  eval-safe (Add x y) = safeP->>= (eval-safe x) (λ m → safeP->>= (eval-safe y) (λ n → spnow _))
  eval-safe (Print x ) = safeP->>= (eval-safe x) (λ m → speff (λ r → spnow tt))


  ∞eval-safe : ∀ {i} t → ∞safe {i} (∞eval t)
  spforce (∞eval-safe t) = eval-safe t


------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e first HALT

specCompile : ∀ a x →
  eval x
  ~
  (map proj₁ (exec (compile x) (a , empty)))
specCompile a x =  ~i-~ λ i → ≲i-~i (λ e → e) (⊥≲i-≲i (eval-safe x)(
  eval x
    ~⟨ ~isym (~i>>=-return) ⟩
  (do v ← eval x
      return v)
    ≡⟨⟩
  (do v ← eval x
      map {A = Conf} proj₁ (return (v , empty)))
    ~⟨ ~isym (~i>>=-assoc (eval x)) ⟩
  (map proj₁ (do v ← eval x
                 return (v , empty)))
    ⊥≲⟨ ⊥≲imap-cong (spec i x first emptyMemFree) (λ { (refl , x) → refl}) ⟩
  map proj₁ (exec (compile x) (a , empty))
  ∎
  ))

 