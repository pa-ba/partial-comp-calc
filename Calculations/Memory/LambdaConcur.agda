{-# OPTIONS --copatterns --sized-types --guardedness #-}

------------------------------------------------------------------------
-- Calculation for lambda calculus + fork/send/receive + channels 
------------------------------------------------------------------------

module Calculations.Memory.LambdaConcur where

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
  LOAD : ℕ → Code → Code
  STORE : Reg → Code → Code
  ADD : Reg → Code → Code
  LOOKUP : ℕ → Code → Code
  RET : Code
  APP : Reg → Code → Code
  ABS : Code → Code → Code
  SEND : Reg → Code → Code
  RECEIVE : Code → Code
  FORK : Code → Code → Code
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'

  Env' : Set
  Env' = List Value'


Lam : Set
Lam = List (Memory Value')

Conf : Set
Conf = Value' × Env' × Lam × Memory Value'


getNum' : ∀ {i} → Value' → CCTree⊥ ChanEff ℕ i
getNum' (Num' n) = return n
getNum' _ = stuck

getClo' : ∀ {i} → Value' → CCTree⊥ ChanEff (Code × Env') i
getClo' (Clo' x e) = return (x , e)
getClo' _ = stuck


~iset-getNum'->>= : ∀ {A i} {m : Memory Value'} {r : Reg} {v : ℕ} {f : ℕ → CCTree⊥ ChanEff A ∞}
  → (get (m #[ r ← Num' v ]) r >>= getNum' >>= f) ~[ i ] f v
~iset-getNum'->>= {m = m} {r} {v} rewrite getSet {r = r} {Num' v} {m}
  = ~itrans (~i>>=-assoc _) (~itrans ~ireturn->>= ~ireturn->>=)

~iset-getClo'->>= : ∀ {A i} {m : Memory Value'} {r : Reg} {c e} {f : Code × Env' → CCTree⊥ ChanEff A ∞}
  → (get (m #[ r ← Clo' c e ]) r >>= getClo' >>= f) ~[ i ] f (c , e)
~iset-getClo'->>= {m = m} {r} {c} {e} rewrite getSet {r = r} {Clo' c e} {m}
  = ~itrans (~i>>=-assoc _) (~itrans ~ireturn->>= ~ireturn->>=)


{-# TERMINATING #-}
mutual
  exec : ∀ {i} → Code → Conf → CCTree⊥ ChanEff Conf i
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
  exec (SEND r c) (Num' n , e , l , m) = do ch ← get m r >>= getNum'
                                            send ch n
                                            exec c (Num' n , e , l , m)                                     
  exec (RECEIVE c)  (Num' ch , e , l , m) = do n ← receive ch; exec c (Num' n , e , l , m)
  exec (FORK c' c)  (a , e , l , m)  = do ch ← newChan
                                          exec c' (Num' 0 , Num' ch ∷ e , [] , empty)
                                            ∥⃗ exec c (Num' ch , e , l , m)
  exec HALT s = return s
  exec _ _ = stuck
  
  ∞exec : ∀ {i} → Code → Conf → ∞CCTree⊥ ChanEff Conf i
  force (∞exec c s) = exec c s


execute : ∀ {i} → Code → Value' → CCTree⊥ None Conf i
execute c a = interpSt⊥ 0 hanChan ( exec c (a , [] , [] , empty))

--------------
-- Compiler --
--------------


comp : Expr → Reg → Code → Code
comp (Val n) r c =  LOAD n c
comp (Add x y) r c = comp x r (STORE r (comp y (next r) (ADD r c)))
comp (Var n) r c = LOOKUP n c
comp (App x y) r c = comp x r (STORE r (comp y (next r) (APP r c)))
comp (Abs x) r c = ABS (comp x (next first) RET) c
comp (Send x y) r c = comp x r (STORE r (comp y (next r) (SEND r c)))
comp (Receive x) r c = comp x r (RECEIVE c)
comp (Fork x) r c = FORK (comp x first HALT) c

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
exec-mono (LOOKUP x c) {e = e} ⊑l ⊑m = ⊥≲i>>=-cong-r (lookup x e) λ _ → exec-mono c ⊑l ⊑m
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
                                          ⊥≲ilater (exec-mono c' (⊑L-cons ⊑m ⊑l) ⊑-refl)))))))
exec-mono (SEND r c) {Num' x} ⊑l ⊑m = ⊥≲itrans (⊥≲i>>=-assoc (get _ r))
                                      (⊥≲itrans (⊥≲iget->>= ⊑m)
                                      (⊥≲itrans (~i-⊥≲i (~isym (~i>>=-assoc (get _ r))))
                                        (⊥≲i>>=-cong-r (get _ r >>= getNum') (λ _ →
                                          ⊥≲i>>-cong-r _ (exec-mono c ⊑l ⊑m)))))
exec-mono (SEND r c) {Clo' x x₁} ⊑l ⊑m = ⊥≲irefl
exec-mono (FORK c' c) ⊑l ⊑m = ⊥≲i>>=-cong-r _ λ ch → ⊥≲i∥⃗-cong-r (exec-mono c ⊑l ⊑m)
exec-mono (RECEIVE c) {Num' x} ⊑l ⊑m = ⊥≲i>>=-cong-r _ λ _ → exec-mono c ⊑l ⊑m
exec-mono (RECEIVE c) {Clo' x x₁} ⊑l ⊑m = ⊥≲irefl
exec-mono (ABS c c') ⊑l ⊑m = exec-mono c' ⊑l ⊑m
exec-mono HALT ⊑l ⊑m = ⊥≲i⊑ (refl , refl , ⊑l , ⊑m)


mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' (next first) RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs

------------
-- Lemmas --
------------

lookup-conv : ∀ {i A} n e → (f : Value' → CCTree⊥ ChanEff A ∞) →
  (lookup n e >>= (λ x → f (conv x))) ~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ~itrans ~ireturn->>= (~isym ~ireturn->>=)
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f = ~istuck->>=
lookup-conv zero [] f = ~istuck->>=
 
-----------------
-- Calculation --
-----------------

open ⊥≲i-Calculation

spec : ∀ i x {e l r a m c} →
  freeFrom r m →
  (do v ← eval x e
      exec c (conv v , convE e , l , m))
   ⊥≲[ i ] exec (comp x r c) (a , convE e , l , m)
spec zero _ _ =  ⊥≲izero
spec i (Val x) {e} {l} {r} {a} {m} {c} F =
   (do v ← return (Num x)
       exec c (conv v , convE e , l , m))
   ~⟨ ~ireturn->>= ⟩
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
      v ← return (Num (n1 + n2))
      exec c (conv v , convE e , l  , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ _ → ~i>>=-cong-r (eval y e >>= getNum)
     λ _ → ~ireturn->>= ) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum
      exec c (Num' (n1 + n2) , convE e , l  , m))
  ⊥≲⟨ ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 →  ⊥≲i>>=-cong-r (eval y e >>= getNum)
     (λ n2 → exec-mono c ⊑-refl (⊑-set F))) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum 
      exec c (Num' (n1 + n2) , convE e , l , m #[ r ← Num' n1 ]))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ n1 → ~i>>=-cong-r (eval y e >>= getNum)
      (λ n2 → ~isym ~iset-getNum'->>=  )) ⟩
  (do n1 ← eval x e >>= getNum
      n2 ← eval y e >>= getNum
      exec (ADD r c) (Num' n2 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → 
      ⊥≲itrans (⊥≲i>>=-assoc (eval y e)) (⊥≲i>>=-cong-r (eval y e)
        (λ {(Num m) → ⊥≲ireturn->>= ;
        (Clo _ _) → ⊥≲istuck->>= }))
     )  ⟩
  (do n1 ← eval x e >>= getNum
      v2 ← eval y e
      exec (ADD r c) (conv v2 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → spec i y (freeFromSet F)) ⟩
  (do n1 ← eval x e >>= getNum
      exec (comp y (next r) (ADD r c)) (Num' n1 , convE e , l , m #[ r ← Num' n1 ]))
  ⊥≲⟨ ⊥≲itrans (⊥≲i>>=-assoc (eval x e)) (⊥≲i>>=-cong-r (eval x e)
        (λ {(Num m) → ⊥≲ireturn->>= ;
        (Clo _ _) → ⊥≲istuck->>= })) ⟩
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
    ⊥≲i>>=-cong-r (eval y e) λ v → ⊥≲itrans ⊥≲i>>=-later (⊥≲ilater (spec i x' (freeFromSet emptyMemFree)))) ⟩
  (do x' , e' ← eval x e >>= getClo
      v ← eval y e
      later (∞exec (comp x' (next first) RET) (conv v , conv v ∷ convE e' , m ∷ l , empty #[ first ← Clo' c (convE e)])))
  ⊥≲⟨ (⊥≲i>>=-cong-r (eval x e >>= getClo) λ (x' , e') → 
    ⊥≲i>>=-cong-r (eval y e) λ v → ⊥≲ilater (exec-mono (comp x' (next first) RET)
      (⊑L-cons (⊑-set F) ⊑-refl) ⊑-refl)) ⟩
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
        (λ {(Num m) → ⊥≲istuck->>= ;
        (Clo _ _) → ⊥≲itrans ⊥≲ireturn->>= ⊥≲irefl }))
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
  ~⟨ ~ireturn->>= ⟩
  (exec c (Clo' (comp x (next first) RET) (convE e) , convE e , l , m))
  ≡⟨⟩
  (exec (ABS (comp x (next first) RET) c) (a , convE e , l , m))
  ∎

spec i (Send x y) {e} {l} {r} {a} {m} {c} F = 
  (do v ← (do ch ← eval x e >>= getNum
              n ← eval y e >>= getNum
              send ch n
              return (Num n))
      exec c (conv v , convE e , l , m))
  ~⟨  ~i>>=-assoc (eval x e >>= getNum) ⟩
  (do ch ← eval x e >>= getNum
      v ← (do n ← eval y e >>= getNum
              send ch n
              return (Num n))
      exec c (conv v , convE e , l , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ _ → ~i>>=-assoc (eval y e >>= getNum)) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      v ← do send ch n
             return (Num n)
      exec c (conv v , convE e , l  , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ _ → ~i>>=-cong-r (eval y e >>= getNum) λ v → ~i>>=-assoc _) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      send ch n
      v ← return (Num n)
      exec c (conv v , convE e , l  , m))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ _ → ~i>>=-cong-r (eval y e >>= getNum)
     λ _ → ~i>>=-cong-r _ λ _ → ~ireturn->>= ) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      send ch n
      exec c (Num' n , convE e , l  , m))
  ⊥≲⟨ ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ ch →  ⊥≲i>>=-cong-r (eval y e >>= getNum)
     (λ n → ⊥≲i>>=-cong-r _ λ _ → exec-mono c ⊑-refl (⊑-set F))) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      send ch n
      exec c (Num' n , convE e , l , m #[ r ← Num' ch ]))
  ~⟨ ~i>>=-cong-r (eval x e >>= getNum) (λ n1 → ~i>>=-cong-r (eval y e >>= getNum)
      (λ n2 → ~isym ~iset-getNum'->>=)) ⟩
  (do ch ← eval x e >>= getNum
      n ← eval y e >>= getNum
      exec (SEND r c) (Num' n , convE e , l , m #[ r ← Num' ch ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → 
      ⊥≲itrans (⊥≲i>>=-assoc (eval y e)) (⊥≲i>>=-cong-r (eval y e)
        (λ {(Num m) → ⊥≲ireturn->>= ;
        (Clo _ _) → ⊥≲istuck->>= }))
     )  ⟩
  (do ch ← eval x e >>= getNum
      v ← eval y e
      exec (SEND r c) (conv v , convE e , l , m #[ r ← Num' ch ]))
  ⊥≲⟨  ⊥≲i>>=-cong-r (eval x e >>= getNum) (λ n1 → spec i y (freeFromSet F)) ⟩
  (do ch ← eval x e >>= getNum
      exec (comp y (next r) (SEND r c)) (Num' ch , convE e , l , m #[ r ← Num' ch ]))
  ⊥≲⟨ ⊥≲itrans (⊥≲i>>=-assoc (eval x e)) (⊥≲i>>=-cong-r (eval x e)
        (λ {(Num m) → ⊥≲ireturn->>= ;
        (Clo _ _) → ⊥≲istuck->>= })) ⟩
  (do v ← eval x e
      exec (comp y (next r) (SEND r c)) (conv v , convE e , l , m #[ r ← conv v ]))
  ≡⟨⟩
    (do v1 ← eval x e
        exec (STORE r (comp y (next r) (SEND r c))) (conv v1 , convE e , l , m))
  ⊥≲⟨ spec i x F ⟩ 
    exec (comp x r (STORE r (comp y (next r) (SEND r c)))) (a , convE e , l , m)
  ∎

spec i (Receive x) {e} {l} {r} {a} {m} {c} F =
  (do v ← do ch ← eval x e >>= getNum
             n ← receive ch
             return (Num n)
      exec c (conv v , convE e , l , m))
 ~⟨ ~i>>=-assoc' _ (λ _ → ~i>>=-assoc' _ (λ _ → ~ireturn->>=)) ⟩
  (do ch ← eval x e >>= getNum
      n ← receive ch
      exec c (Num' n , convE e , l , m))
 ≡⟨⟩
  (do ch ← eval x e >>= getNum
      exec (RECEIVE c) (Num' ch , convE e , l , m))
 ~⟨ ~i>>=-assoc _ ⟩
  (do v ← eval x e
      ch ← getNum v
      exec (RECEIVE c) (Num' ch , convE e , l , m))
 ⊥~⟨ ⊥~i>>=-cong-r _ (λ { (Num x) → ⊥~ireturn->>= ; (Clo x x₁) → ⊥~istuck->>=}) ⟩
  (do v ← eval x e
      exec (RECEIVE c) (conv v , convE e , l , m))
  ⊥≲⟨ spec i x F ⟩
   exec (comp x r (RECEIVE c)) (a , convE e , l , m)
 ∎


spec i (Fork x) {e} {l} {r} {a} {m} {c} F = 
  (do v ← do ch ← newChan
             eval x (Num ch ∷ e) ∥⃗ return (Num ch)
      exec c (conv v , convE e , l , m))
 ~⟨ ~i>>=-assoc _ ⟩
  (do ch ← newChan
      v ← eval x (Num ch ∷ e) ∥⃗ return (Num ch)
      exec c (conv v , convE e , l , m))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗->>=) ⟩
  (do ch ← newChan
      eval x (Num ch ∷ e) ∥⃗ (return (Num ch) >>= λ v → exec c (conv v , convE e , l , m)))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗-cong-r ~ireturn->>=) ⟩
  (do ch ← newChan
      eval x (Num ch ∷ e) ∥⃗ exec c (Num' ch , convE e , l , m))
 ~⟨ ~i>>=-cong-r _ (λ ch' → ~i∥⃗-map-l _ _) ⟩
  (do ch ← newChan
      (eval x (Num ch ∷ e) >>= λ v → exec HALT (conv v , Num' ch ∷ convE e , [] , empty))
        ∥⃗ exec c (Num' ch , convE e , l , m))
 ⊥≲⟨ ⊥≲i>>=-cong-r _ (λ ch' → ⊥≲i∥⃗-cong-l (spec i x emptyMemFree)) ⟩
  (do ch ← newChan
      exec (comp x first HALT) (Num' 0 , Num' ch ∷ convE e , [] , empty) ∥⃗ exec c (Num' ch , convE e , l , m))
 ≡⟨⟩
   exec (FORK (comp x first HALT) c) (a , convE e , l , m) 
 ∎


------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e first HALT

specCompile' : ∀ {i} a x →
  (do v ← evaluate x; return (conv v , [] , [] , empty))  ⊥≲[ i ] execute (compile x) a
specCompile' {i} a x = 
  (do v ← evaluate x; return (conv v , [] , [] , empty))
 ≡⟨⟩
  (do v ← interpSt⊥ 0 hanChan (eval x []); return (conv v , [] , [] , empty))
 ⊥~⟨ ⊥~iinterpSt⊥-map {f = hanChan} _ ⟩
  interpSt⊥ 0 hanChan (do v ← eval x []; return (conv v , [] , [] , empty))
 ⊥≲⟨ ⊥≲iinterpSt⊥-cong {f = hanChan} (spec i x emptyMemFree) ⟩
  execute (compile x) a
 ∎

specCompile : ∀ a x →
  map conv (evaluate x)  ⊥~ map proj₁ (execute (compile x) a)
specCompile a x = ⊥~i-⊥~ λ i → ⊥≲i-⊥~i (λ e → e) (
  map conv (evaluate x)
 ≡⟨⟩
   (do v ← evaluate x; return (conv v))
 ~⟨ (~i>>=-cong-r _ λ _ → ~isym ~imap-return ) ⟩
   (do v ← evaluate x; map {A = Conf} proj₁ (return (conv v , [] , [] , empty )))
 ~⟨ ~isym (~i>>=-assoc _) ⟩
   map {A = Conf} proj₁ (do v ← evaluate x; return (conv v , [] , [] , empty ))
  ⊥≲⟨ ⊥≲imap-cong (specCompile' a x) proj₁ ⟩
 map proj₁ (execute (compile x) a)
 ∎
  )


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

specCompileTyped : ∀ a x τ →
  [] ⊢ x ∶ τ →
  map conv (evaluate x)
  ~
  map proj₁ (execute (compile x) a)
specCompileTyped a x τ T = ⊥~-~' (safeP->>= (evaluate-safe T) (λ _ → spnow tt)) (specCompile a x)
