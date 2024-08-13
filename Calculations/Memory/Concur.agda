{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for the simple arithmetic language with a degenerate
-- loop primitive and concurrency
------------------------------------------------------------------------

module Calculations.Memory.Concur where

open import CCTree
open import Data.Nat
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Data.Unit 
open import Relation.Binary.PropositionalEquality


data PrintEff : Set → Set where
  printEff : ℕ → PrintEff ⊤

instance
  printEffPar : Concurrent PrintEff
  printEffPar = defaultPar

M : Set → Size → Set₁
M A i = CCTree⊥ PrintEff A i

∞M : Set → Size → Set₁
∞M A i = ∞CCTree⊥ PrintEff A i

print : ∀ {i} → ℕ → M ⊤ i
print n = eff (notStuck (printEff n)) now


---------------------
-- Source language --
---------------------

data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Print : Expr → Expr
  Fork : Expr → Expr
  Loop : Expr


mutual
  eval : ∀ {i} → Expr → M ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval Loop = later (∞eval Loop)
  eval (Print x) = do n ← eval x
                      print n
                      return n
  eval (Fork x) = eval x ∥⃗ return 0

  ∞eval : ∀ {i} → Expr → ∞M ℕ i
  force (∞eval x) = eval x
  
---------------------
-- Target language --
---------------------


data Code : Set where
  LOAD : ℕ -> Code -> Code
  STORE : Reg -> Code -> Code
  ADD : Reg → Code -> Code
  LOOP : Code
  HALT : Code
  PRINT : Code → Code
  FORK : Code → Code → Code
  


Conf : Set
Conf = ℕ × (Memory ℕ)


mutual
  exec : ∀ {i} → Code → Conf → M Conf i
  exec (LOAD n c) (a , m) = exec c (n , m)
  exec (STORE r c) (a , m) = exec c (a , m #[ r ← a ])
  exec (ADD r c) (a , m) = do b ← get m r
                              exec c (b + a , m)
  exec LOOP s = later (∞exec LOOP s)
  exec HALT s = return s
  exec (PRINT c) (n , m) = print n >> exec c (n , m)
  exec (FORK c' c) (a , m)  = (exec c' (a , empty) ∥⃗ exec c (0 , m))

  ∞exec : ∀ {i} → Code → Conf → ∞M Conf i
  force (∞exec e x) = exec e x

--------------
-- Compiler --
--------------


comp : Expr → Reg → Code → Code
comp (Val n) r c =  LOAD n c
comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))
comp Loop r c = LOOP
comp (Print x) r c = comp x r (PRINT c)
comp (Fork x) r c = FORK (comp x first HALT) c




exec-mono : ∀ {i}  {a} {m m' : Memory ℕ} c → m ⊑ m' → exec c (a , m) ⊥≲[ i ] exec c (a , m')
exec-mono {i = zero} _ _ = ⊥≲izero
exec-mono (LOAD x c) l = exec-mono c l
exec-mono (STORE x c) l = exec-mono c (set-monotone l)
exec-mono (ADD x c) l = ⊥≲itrans (⊥≲iget->>= l) (⊥≲i>>=-cong-r _ λ _ → exec-mono c l) 
exec-mono {suc j} LOOP l = ⊥≲ilater (exec-mono LOOP l)
exec-mono HALT l = ⊥≲i⊑ (refl , l)
exec-mono (PRINT c) l = ⊥≲i>>-cong-r _ (exec-mono c l)
exec-mono (FORK c1 c2) l = ⊥≲i∥⃗-cong (exec-mono c1 ⊑-refl) (exec-mono c2 l)


-----------------
-- Calculation --
-----------------

-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.

open ⊥≲i-Calculation

spec : ∀ i x r {a m c} →
  freeFrom r m →
  (do v ← eval x
      exec c (v , m))
  ⊥≲[ i ]
  (exec (comp x r c) (a , m))
spec zero _ _ _ =  ⊥≲izero
spec i (Val x) r {a} {m} {c} F =
   (do v ← return x
       exec c (v , m))
   ~⟨ ~ireturn->>= ⟩
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
      v ← return (n1 + n2)
      exec c (v , m))
  ~⟨ ~i>>=-cong-r (eval x) (λ n1 → ~i>>=-cong-r (eval y) λ n2 → ~ireturn->>=) ⟩
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


spec (suc j) Loop r {a} {m} {c} F = 
  (eval Loop >>= \ v → exec c (v , m))
  ~⟨ ~i>>=-later ⟩
  (later (∞eval Loop ∞>>= \ v → exec c (v , m)))
  ⊥≲⟨ ⊥≲ilater (spec j Loop r {c = c} F) ⟩
  later (∞exec (comp Loop r c) (a , m))
  ≡⟨⟩
  exec LOOP (a , m)
  ∎

spec i (Print x) r {a} {m} {c} F =
  (do v ← eval (Print x)
      exec c (v , m))
  ≡⟨⟩
  (do v ← do n ← eval x
             print n
             return n
      exec c (v , m))
  ~⟨ (~i>>=-assoc' _ λ n → ~i>>-assoc' _ ~ireturn->>=) ⟩
  (do n ← eval x
      print n
      exec c (n , m))
  ≡⟨⟩
  (do n ← eval x
      exec (PRINT c) (n , m))
  ⊥≲⟨ spec i x r F ⟩
  (exec (comp x r (PRINT c)) (a , m))
  ∎


spec i (Fork x) r {a} {m} {c} F =
  (do v ← eval x ∥⃗ return 0
      exec c (v , m))
  ~⟨ ~i∥⃗->>= ⟩ 
  (eval x ∥⃗ (return 0 >>= λ v → exec c (v , m)))
  ~⟨ ~i∥⃗-cong-r ~ireturn->>= ⟩
  (eval x ∥⃗ exec c (0 , m))
  ~⟨ ~i∥⃗-map-l (eval x) _ ⟩
  ((eval x >>= λ v → exec HALT (v , empty)) ∥⃗ exec c (0 , m))
  ⊥≲⟨ ⊥≲i∥⃗-cong-l (spec i x first emptyMemFree) ⟩
  ((exec (comp x first HALT) (a , empty)) ∥⃗ exec c (0 , m))
  ≡⟨⟩
  (exec (FORK (comp x first HALT) c) (a , m))
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
  eval-safe Loop = splater (∞eval-safe Loop)
  eval-safe (Print x) = safeP->>= (eval-safe x) λ _ → safeP->>= (speff (λ _ → spnow tt)) λ _ → spnow _ 
  eval-safe (Fork x) = safeP-∥⃗ (eval-safe x) (spnow _)
  
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
    ~⟨ ~i>>=-cong-r (eval x) (λ v → ~isym (~imap-return)) ⟩
  (do v ← eval x
      map {A = Conf} proj₁ (return (v , empty)))
    ~⟨ ~isym (~i>>=-assoc (eval x)) ⟩
  (map proj₁ (do v ← eval x
                 return (v , empty)))
    ⊥≲⟨ ⊥≲imap-cong (spec i x first emptyMemFree) (λ { (refl , x) → refl}) ⟩
  map proj₁ (exec (compile x) (a , empty))
  ∎
  ))

