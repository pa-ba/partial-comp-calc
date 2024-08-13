module Memory where


open import Relation.Binary.PropositionalEquality

open import Preorder public
open import Data.Product
open import Data.Maybe hiding (_>>=_ ; map) public
open import Data.List
open import Data.Nat
open import Agda.Builtin.Nat
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Bool.Properties hiding (≤-refl)
open import Data.Nat.Properties
open import Relation.Nullary


abstract

  Reg : Set
  Reg = ℕ
  
  first : Reg
  first = zero
  
  
  next : Reg → Reg
  next = suc
  
  Memory : (A : Set) → Set
  Memory A = ℕ → Maybe A
  
  
  instance
    MemoryOrd : {A : Set} → Ord (Memory A)
    MemoryOrd = record {
      _⊑_ = λ m m' → (∀ r e → m r ≡ just e → m' r ≡ just e);
      ⊑-refl = λ r e z → z;
      ⊑-trans = λ z z₁ r e z₂ → z₁ r e (z r e z₂)
      }
  
  
  infixl 10 _#[_←_]
  infixl 10 _#[_]
    
  empty : ∀ {A} → Memory A
  empty _ = nothing
  
  _#[_←_] : ∀ {E} → Memory E → Reg → E → Memory E
  _#[_←_] = λ m r e → λ r' → if r' == r then just e else m r'
  _#[_] : ∀ {E} → Memory E → Reg → Maybe E
  _#[_] = λ m r → m r
  freeFrom : ∀ {E} → Reg → Memory E → Set
  freeFrom = λ r m → (∀ r' → r ≤ r' → m r' ≡ nothing)
  
  
  T-true : ∀ {b} → T b → b ≡ true
  T-true {true} t = refl
  
  T-false : ∀ {b} → ¬ (T b) → b ≡ false
  T-false {false} t = refl
  T-false {true} t with t _
  ... | ()
  
  
  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x
  
  insp : ∀ {a} {A : Set a} (x : A) → Singleton x
  insp x = x with≡ refl
  
  

  emptyMemFree : ∀ {E} → freeFrom first (empty {E})
  emptyMemFree _ _ = refl
  
  getSet : ∀ {E} {r : Reg} {v : E} {m : Memory E} → (m #[ r ← v ]) #[ r ] ≡ just v
  getSet {r = r} rewrite T-true (≡⇒≡ᵇ r r refl) = refl
  
  ⊑-set : ∀ {E} {r : Reg} {m : Memory E} {v : E} → freeFrom r m → m ⊑ m #[ r ← v ]
  ⊑-set {r = r} f r' e eq with T? (r' == r)
  ... | .false because ofⁿ p rewrite T-false p  =  eq
  ... | .true because ofʸ p rewrite ≡ᵇ⇒≡ r' r p rewrite f r ≤-refl with eq
  ... | ()
  
  
  freeFromSet : ∀ {E} {r : Reg} {m : Memory E} {v : E}
    → freeFrom r m →  freeFrom (next r) (m #[ r ← v ])
  freeFromSet {r = r} ff r' le with T? (r' == r)
  ... | .false because ofⁿ p rewrite T-false p =  ff r' (<⇒≤ le)
  ... | .true because ofʸ p rewrite ≡ᵇ⇒≡ r' r p with Data.Nat.Properties.<-irrefl refl le
  ... | ()
  
  
  set-monotone : ∀ {E} {r : Reg} {m m' : Memory E} {v : E}
    → m ⊑ m' → m #[ r ← v ] ⊑ m' #[ r ← v ]
  set-monotone {r = r} l r' e eq  with T? (r' == r)
  ... | .true because ofʸ p rewrite T-true p = eq
  ... | .false because ofⁿ p rewrite T-false p = l r' e eq
  
  ⊑-get : ∀ {E} {r : Reg} {m m' : Memory E} {v : E}
    → m ⊑ m' → m #[ r ] ≡ just v → m' #[ r ] ≡ just v
  ⊑-get {r = r} {v = v} l eq = l r v eq
  


data _⊑M_  {A : Set} {{_ : Ord A}} : (Maybe A) → (Maybe A) → Set where
  ⊑M-nothing : ∀ {m} → nothing ⊑M m
  ⊑M-just : ∀ {x y} → x ⊑ y → just x ⊑M just y



⊑M-refl : ∀ {A : Set} {{_ : Ord A}} {m : Maybe A} → m ⊑M m
⊑M-refl {m = nothing} = ⊑M-nothing
⊑M-refl {m = just x} = ⊑M-just ⊑-refl

⊑M-trans : ∀ {A : Set} {{_ : Ord A}}  {m n u : Maybe A} → m ⊑M n → n ⊑M u → m ⊑M u
⊑M-trans ⊑M-nothing K =  ⊑M-nothing
⊑M-trans (⊑M-just x) (⊑M-just y) =  ⊑M-just (⊑-trans x y)
    
