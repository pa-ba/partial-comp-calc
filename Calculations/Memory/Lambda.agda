{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for the lambda calculus
------------------------------------------------------------------------

module Calculations.Memory.Lambda where

open import Relation.Binary.PropositionalEquality
open import CTree hiding (τ)
open import Data.Nat
open import Data.Unit
open import Data.Product hiding (map)
open import Data.List hiding (map ; lookup)
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


lookup : ∀ {a i} → ℕ → List a → CTree⊥ None a i
lookup 0 (x ∷ xs) = return x
lookup (suc i) (x ∷ xs) = lookup i xs
lookup _ _ = stuck


-- The following two functions are used instead of partial pattern
-- matching. Agda supports an Idris-style pattern matching syntax
-- within the do notation, but that is useless for reasoning (see
-- https://agda.readthedocs.io/en/v2.6.2/language/lambda-abstraction.html)

getNum : ∀ {i} → Value → CTree⊥ None ℕ i
getNum (Num n) = return n
getNum _ = stuck

getClo : ∀ {i} → Value → CTree⊥ None (Expr × Env) i
getClo (Clo x e) = return (x , e)
getClo _ = stuck


mutual
  eval : ∀ {i} → Expr → Env → CTree⊥ None Value i
  eval (Val x) e = return (Num x)
  eval (Add x y) e =
    do n ← eval x e >>= getNum
       m ← eval y e >>= getNum
       return (Num (n + m))
  eval (Var i) e = lookup i e
  eval (Abs x)   e = return (Clo x e)
  eval (App x y) e = do x' , e' ← eval x e >>= getClo
                        v ← eval y e
                        later (∞eval x' (v ∷ e'))

  ∞eval : ∀ {i} → Expr → Env → ∞CTree⊥ None Value i
  force (∞eval x e) = eval x e
  
---------------------
-- Target language --
---------------------

data Code : Set where
  LOAD : ℕ -> Code -> Code
  STORE : Reg -> Code -> Code
  ADD : Reg → Code -> Code
  LOOKUP : ℕ → Code → Code
  RET : Code
  APP : Reg → Code → Code
  ABS : Code → Code → Code    
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'

  Env' : Set
  Env' = List Value'



getNum' : ∀ {i} → Value' → CTree⊥ None ℕ i
getNum' (Num' n) = return n
getNum' _ = stuck

getClo' : ∀ {i} → Value' → CTree⊥ None (Code × Env') i
getClo' (Clo' x e) = return (x , e)
getClo' _ = stuck


~iset-getNum'->>= : ∀ {A i} {m : Memory Value'} {r : Reg} {v : ℕ} {f : ℕ → CTree⊥ None A ∞}
  → (get (m #[ r ← Num' v ]) r >>= getNum' >>= f) ~[ i ] f v
~iset-getNum'->>= {m = m} {r} {v} rewrite getSet {r = r} {Num' v} {m} = ~irefl

~iset-getClo'->>= : ∀ {A i} {m : Memory Value'} {r : Reg} {c e} {f : Code × Env' → CTree⊥ None A ∞}
  → (get (m #[ r ← Clo' c e ]) r >>= getClo' >>= f) ~[ i ] f (c , e)
~iset-getClo'->>= {m = m} {r} {c} {e} rewrite getSet {r = r} {Clo' c e} {m} = ~irefl


Lam : Set
Lam = List (Memory Value')

Conf : Set
Conf = Value' × Env' × Lam × Memory Value'


mutual
  {-# TERMINATING #-}
  exec : ∀ {i} → Code → Conf → CTree⊥ None Conf i
  exec (LOAD n c) (a , e , l , m) = exec c (Num' n , e , l , m)
  exec (ADD r c) (Num' a , e , l , m) = do b ← get m r >>= getNum'
                                           exec c (Num' (b + a) , e , l , m)
  exec (STORE r c) (a , e , l , m) = exec c (a , e , l , m #[ r ← a ])
  exec (LOOKUP n c) (a , e , l , m) = do v ← lookup n e
                                         exec c (v , e , l , m)
  exec (APP r c) (a , e , l , m) = do c' , e' ← get m r >>= getClo'
                                      later (∞exec c' (a , a ∷ e' , m ∷ l , empty #[ first ← Clo' c e ]))
  exec (ABS c' c) (a , e , l , m) = exec c (Clo' c' e  , e , l , m)
  exec RET (a , e , m' ∷ l , m) = do c' , e' ← get m first >>= getClo'
                                     exec c' (a , e' , l , m')
  exec HALT s = return s
  exec _ _ = stuck

  ∞exec : ∀ {i} → Code → Conf → ∞CTree⊥ None Conf i
  force (∞exec e x) = exec e x


--------------
-- Compiler --
--------------


comp : Expr → Reg → Code → Code
comp (Val n) r c =  LOAD n c
comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))
comp (Var n) r c = LOOKUP n c
comp (App x y) r c = comp x r (STORE r (comp y (next r) (APP r c)))
comp (Abs x) r c = ABS (comp x (next first) RET) c

instance
  OrdValue' : Ord Value'
  OrdValue' = ≡-Ord
  
instance
  OrdEnv' : Ord Env'
  OrdEnv' = ≡-Ord
  
instance
  OrdLam : Ord Lam
  OrdLam = ListOrd _


exec-mono : ∀ {i} c {a e l l' m m'} → l ⊑ l' → m ⊑ m' → exec c (a , e , l , m) ⊥≲[ i ] exec c (a , e , l' , m')
exec-mono {i = zero} _ _ _ = ⊥≲izero
exec-mono (LOAD x c) ⊑l ⊑m = exec-mono c ⊑l ⊑m
exec-mono (STORE x c) ⊑l ⊑m = exec-mono c ⊑l (set-monotone ⊑m)
exec-mono (ADD x c) {Num' x₁} ⊑l ⊑m = ⊥≲itrans (⊥≲i>>=-assoc (get _ x))
                                      (⊥≲itrans (⊥≲iget->>= ⊑m)
                                      (⊥≲itrans (~i-⊥≲i (~isym (~i>>=-assoc (get _ x))))
                                        (⊥≲i>>=-cong-r (get _ x >>= getNum') (λ _ →
                                          exec-mono c ⊑l ⊑m))))
exec-mono (ADD x c) {Clo' x₁ x₂} ⊑l ⊑m = ⊥≲irefl
exec-mono (LOOKUP x c) ⊑l ⊑m = ⊥≲i>>=-cong-r (lookup x _) λ _ → exec-mono c ⊑l ⊑m
exec-mono RET {l = .[]} ⊑L-nil ⊑m = ⊥≲irefl
exec-mono RET {l = .(_ ∷ _)} (⊑L-cons x ⊑l) ⊑m = ⊥≲itrans (⊥≲i>>=-assoc (get _ first))
                                      (⊥≲itrans (⊥≲iget->>= ⊑m)
                                      ((⊥≲itrans (~i-⊥≲i (~isym (~i>>=-assoc (get _ first))))
                                        ((⊥≲i>>=-cong-r (get _ first >>= getClo') (λ (c' , e') → 
                                          exec-mono c' ⊑l x))))))
exec-mono {i = suc i} (APP x c) ⊑l ⊑m = ⊥≲itrans (⊥≲i>>=-assoc (get _ x))
                                      (⊥≲itrans (⊥≲iget->>= ⊑m)
                                      ((⊥≲itrans (~i-⊥≲i (~isym (~i>>=-assoc (get _ x))))
                                        ((⊥≲i>>=-cong-r (get _ x >>= getClo') (λ (c' , e') → 
                                          ⊥≲ilater (exec-mono c' (⊑L-cons ⊑m ⊑l) (⊑-refl {{MemoryOrd}}))))))))
exec-mono (ABS c c') ⊑l ⊑m = exec-mono c' ⊑l ⊑m
exec-mono HALT ⊑l ⊑m = ⊥≲i⊑ (refl , refl , ⊑l , ⊑m)

mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' (next first) RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs



-----------------
-- Calculation --
-----------------

-- This is the lookup lemma that is used in the `Var` case.
lookup-conv : ∀ {i A} n e → (f : Value' → CTree⊥ None A ∞) →
  (lookup n e >>= (f ∘ conv)) ~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ~irefl
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f = ~istuck-refl
lookup-conv zero [] f = ~istuck-refl


open ⊥≲i-Calculation


-- This is the compiler correctness property in its i-bisimilarity
-- form. This is where the calculation happens.


spec : ∀ i x {e} {l} {r} {a m c} →
  freeFrom r m →
  (do v ← eval x e
      exec c (conv v , convE e , l , m))
  ⊥≲[ i ]
  (exec (comp x r c) (a , convE e , l , m))
spec zero _ _  =  ≲izero
spec i (Val x) {e} {l} {r} {a} {m} {c} F =
   (do v ← return (Num x)
       exec c (conv v , convE e , l , m))
   ≡⟨⟩
   exec c (Num' x , convE e , l , m)
   ≡⟨⟩
   (exec (LOAD x c) (a , convE e , l  , m))
  ∎

spec i (Add x y) {e} {l} {r} {a} {m} {c} F = 
  (do v ← (do n1 ← eval x e >>= getNum
              n2 ← eval y e >>= getNum
              return (Num (n1 + n2)))
      exec c (conv v , convE e , l , m))
  ~⟨  ~i>>=-assoc (eval x e >>= getNum) ⟩
  (do n1 ← eval x e >>= getNum
      v ← (do n2 ← eval y e >>= getNum
              return (Num (n1 + n2)))
      exec c (conv v , convE e , l , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ _ → ~i>>=-assoc (eval y e >>= getNum)) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum
      exec c (Num' (n1 + n2) , convE e , l  , m))
  ⊥≲⟨ ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 →  ⊥≲i>>=-cong-r (eval y e >>= getNum)
     (λ n2 → exec-mono c (⊑-refl {{OrdLam}}) (⊑-set F))) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum 
      exec c (Num' (n1 + n2) , convE e , l , m #[ r ← Num' n1 ]))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ n1 → ~i>>=-cong-r (eval y e >>= getNum)
      (λ n2 → ~isym ~iset-getNum'->>=  )) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum
      exec (ADD r c) (Num' n2 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨ ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → 
      ⊥≲itrans (⊥≲i>>=-assoc (eval y e)) (⊥≲i>>=-cong-r (eval y e)
        (λ {(Num m) → ⊥≲irefl ;
        (Clo _ _) → ⊥≲istuck }))
     ) ⟩
  (do n1 ← eval x e >>= getNum
      v2 ← eval y e
      exec (ADD r c) (conv v2 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → spec i y (freeFromSet F)) ⟩
  (do n1 ← eval x e >>= getNum
      exec (comp y (next r) (ADD r c)) (Num' n1 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨ ⊥≲itrans (⊥≲i>>=-assoc (eval x e)) (⊥≲i>>=-cong-r (eval x e)
        (λ {(Num m) → ⊥≲irefl ;
        (Clo _ _) → ⊥≲istuck })) ⟩
  (do v1 ← eval x e
      exec (comp y (next r) (ADD r c)) (conv v1 , convE e , l , m #[ r ← conv v1 ]))
  ≡⟨⟩
    (do v1 ← eval x e
        exec (STORE r (comp y (next r) (ADD r c))) (conv v1 , convE e , l , m))
  ⊥≲⟨ spec i x F ⟩
    exec (comp x r (STORE r (comp y (next r) (ADD r c)))) (a , convE e , l , m)
  ∎

spec i (Var n) {e} {l} {r} {a} {m} {c} F =
   (do v ← lookup n e
       exec c (conv v , convE e , l , m))
   ~⟨ lookup-conv n e _ ⟩
   (do v ← lookup n (convE e)
       exec c (v , convE e , l , m))
   ≡⟨⟩
   (exec (LOOKUP n c) (a , convE e , l , m))
  ∎

spec (suc i) (App x y) {e} {l} {r} {a} {m} {c} F =
  (do v ← (do x' , e' ← eval x e >>= getClo
              v ← eval y e
              later (∞eval x' (v ∷ e')))
      exec c (conv v , convE e , l , m))
  ~⟨ ~i>>=-assoc (eval x e >>= getClo) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← do v ← eval y e
             later (∞eval x' (v ∷ e'))
      exec c (conv v , convE e , l , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ _ → ~i>>=-assoc (eval y e)) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec c (conv w , convE e , l , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getClo) (λ (x' , e') →
     ~i>>=-cong-r (eval y e) λ v → ~i>>=-cong-r (later (∞eval x' (v ∷ e'))) λ w →
       ~isym ~iset-getClo'->>= ) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      w ← later (∞eval x' (v ∷ e'))
      exec RET (conv w , conv v ∷ convE e' , m ∷ l , empty #[ first ← Clo' c (convE e)]))
  ⊥≲⟨ ( ⊥≲i>>=-cong-r (eval x e >>= getClo) λ (x' , e') → 
    ⊥≲i>>=-cong-r (eval y e) λ v → ⊥≲ilater (spec i x' (freeFromSet emptyMemFree))) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      later (∞exec (comp x' (next first) RET) (conv v , conv v ∷ convE e' , m ∷ l , empty #[ first ← Clo' c (convE e)])))
  ⊥≲⟨ (⊥≲i>>=-cong-r (eval x e >>= getClo) λ (x' , e') → 
    ⊥≲i>>=-cong-r (eval y e) λ v → ⊥≲ilater (exec-mono (comp x' (next first) RET)
      (⊑L-cons (⊑-set F) (⊑-refl {{OrdLam}})) (⊑-refl {{MemoryOrd}}))) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      later (∞exec (comp x' (next first) RET) (conv v , conv v ∷ convE e' , (m #[ r ← Clo' (comp x' (next first) RET) (convE e') ]) ∷ l , empty #[ first ← Clo' c (convE e)])))
  ~⟨ ( ~i>>=-cong-r (eval x e >>= getClo) λ (x' , e') → 
    ~i>>=-cong-r (eval y e) λ v → ~isym ~iset-getClo'->>= ) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      exec (APP r c) (conv v , convE e , l , m #[ r ← Clo' (comp x' (next first) RET) (convE e')]))
  ⊥≲⟨ (⊥≲i>>=-cong-r (eval x e >>= getClo) λ (x' , e') → spec (suc i) y (freeFromSet F)) ⟩
  (do x' , e' ← eval x e >>= getClo
      exec (comp y (next r) (APP r c)) (conv (Clo x' e') , convE e , l , m #[ r ← Clo' (comp x' (next first) RET) (convE e')]))
  ⊥≲⟨  ⊥≲itrans (⊥≲i>>=-assoc (eval x e)) (⊥≲i>>=-cong-r (eval x e)
        (λ {(Num m) → ⊥≲istuck ;
        (Clo _ _) → ⊥≲irefl }))
      ⟩
  (do v ← eval x e
      exec (comp y (next r) (APP r c)) (conv v , convE e , l , m #[ r ← conv v ]))
  ≡⟨⟩
    (do v ← eval x e
        exec (STORE r (comp y (next r) (APP r c))) (conv v , convE e , l , m))
  ⊥≲⟨ spec (suc i) x F ⟩
    (exec (comp x r (STORE r (comp y (next r) (APP r c)))) (a , convE e , l , m))
  ∎

spec (suc i) (Abs x) {e} {l} {r} {a} {m} {c} F =
  (do v ← return (Clo x e)
      exec c (conv v , convE e , l , m))
  ≡⟨⟩
  (exec c (Clo' (comp x (next first) RET) (convE e) , convE e , l , m))
  ≡⟨⟩
  (exec (ABS (comp x (next first) RET) c) (a , convE e , l , m))
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



------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e first HALT


specCompile : ∀ a x →
  map conv (eval x [])
  ⊥~
  (map proj₁ (exec (compile x) (a , [] , [] , empty)))
specCompile a x =  ⊥~i-⊥~ λ i → ⊥≲i-⊥~i (λ e → e) (
  map conv (eval x [])
    ≡⟨⟩
  (do v ← eval x []
      return (conv v))
    ≡⟨⟩
  (do v ← eval x []
      map {A = Conf} proj₁ (return (conv v , [] , [] , empty)))
    ~⟨ ~isym (~i>>=-assoc (eval x [])) ⟩
  (map proj₁ (do v ← eval x []
                 return (conv v , [] , [] , empty)))
    ⊥≲⟨ ⊥≲imap-cong (spec i x emptyMemFree) (λ { (refl , x) → refl})⟩
  map proj₁ (exec (compile x) (a , [] , [] , empty))
  ∎
  )

specCompileTyped : ∀ a x τ →
  [] ⊢ x ∶ τ →
  map conv (eval x [])
  ~
  (map proj₁ (exec (compile x) (a , [] , [] , empty)))
specCompileTyped a x τ T = ⊥~-~ (safeP->>= (eval-safe T ⊢cnil) λ _ → spnow _) (specCompile a x)
