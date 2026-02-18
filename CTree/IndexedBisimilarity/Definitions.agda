{-# OPTIONS --sized-types --large-indices #-}

------------------------------------------------------
-- Definition of step-indexed (strong) bisimilarity
------------------------------------------------------


module CTree.IndexedBisimilarity.Definitions where

open import CTree.Definitions public
open import CTree.Transitions public
open import Preorder public

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


lsuc : ∀ {E A} → label E A → ℕ → ℕ
lsuc ⟨ x ⟩ i = suc i
lsuc τ i = i

lpred : (Set → Set) → Set → Set₁
lpred E A = label E A → Set


data Eff (E : Set → Set) : Set₁ where
  MkEff : ∀ {A} → (E A) → Eff E

epred : (Set → Set) → Set₁
epred E = Eff E → Set

data _??_ {E A} (ep : epred E) : lpred E A where
  isEffPredτ : ep ?? τ
  isEffPredρ : ∀ v → ep ?? ⟨ ρ v ⟩
  isEffPredι : ∀ {B} (v : B) → ep ?? ⟨ ι v ⟩
  isEffPredε : ∀ {B} (e : E B) → ep (MkEff e) → ep ?? ⟨ ε e ⟩


-- locally safe
lsafe : ∀ {E A} → epred E → (p : CTree' E A) → Set₁
lsafe L p = ∀ {p' l} → p [ l ]⇒ p' → L ?? l




data _⊑lab_  {A E} {{_ : Ord A}} : (label E A) → (label E A) → Set₁ where
  ⊑τ : τ ⊑lab τ
  ⊑ε : ∀ {B} → (e : E B) → ⟨ ε e ⟩ ⊑lab ⟨ ε e ⟩
  ⊑ι : ∀ {B} → (r : B) → ⟨ ι r ⟩ ⊑lab ⟨ ι r ⟩
  ⊑ρ : ∀ {v1 v2 : A} → v1 ⊑ v2 → ⟨ ρ v1 ⟩ ⊑lab ⟨ ρ v2 ⟩

⊑lab-rev : ∀ {A E} {{O : Ord A}} {l l' : label E A} →
  _⊑lab_ {{O}} l l' → _⊑lab_ {{Ord-rev O}} l' l
⊑lab-rev ⊑τ = ⊑τ
⊑lab-rev (⊑ε e) = ⊑ε e
⊑lab-rev (⊑ι r) = ⊑ι r
⊑lab-rev (⊑ρ x) = ⊑ρ x

⊑lab-rev' : ∀ {A E} {{O : Ord A}} {l l' : label E A} →
  _⊑lab_ {{Ord-rev O}} l l' → _⊑lab_ {{O}} l' l
⊑lab-rev' ⊑τ = ⊑τ
⊑lab-rev' (⊑ε e) = ⊑ε e
⊑lab-rev' (⊑ι r) = ⊑ι r
⊑lab-rev' (⊑ρ x) = ⊑ρ x


instance 
  LabOrd : ∀ {E} {A : Set} {{M : Ord A}} → Ord (label E A)
  _⊑_ {{LabOrd}} = _⊑lab_
  ⊑-refl ⦃ LabOrd ⦄ {⟨ ε x ⟩} = ⊑ε x
  ⊑-refl ⦃ LabOrd ⦄ {⟨ ι x ⟩} = ⊑ι x
  ⊑-refl  ⦃ LabOrd ⦃ M = M ⦄ ⦄ {⟨ ρ x ⟩} = ⊑ρ (⊑-refl {{M}})
  ⊑-refl ⦃ LabOrd ⦄ {τ} = ⊑τ
  ⊑-trans ⦃ LabOrd ⦄ ⊑τ r = r
  ⊑-trans ⦃ LabOrd ⦄ (⊑ε e) r = r
  ⊑-trans ⦃ LabOrd ⦄ (⊑ι r₁) r = r
  ⊑-trans ⦃ LabOrd ⦃ M = M ⦄ ⦄ (⊑ρ l) (⊑ρ r) = ⊑ρ (⊑-trans ⦃ M ⦄ l r)


infix 3 _≲̂_[_]_

data _≲̂_[_]_  {E A} {{_ : Ord A}} : CTree' E A → epred E → ℕ → CTree' E A → Set₁ where
  ≲izero : ∀ {p q} {L} →  p ≲̂ L [ 0 ] q
  ≲istep : ∀ {p q i} {L} →
    (left :  lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')) → 
    (right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q')) →
    p ≲̂ L [ suc i ] q

infix 3 _~̂_[_]_ 



_~̂_[_]_ : ∀ {E A} → CTree' E A → epred E → ℕ → CTree' E A → Set₁
p ~̂ L [ i ] q = _≲̂_[_]_ {{≡-Ord}} p  L i q 


_⊑≡_ : ∀ {E A} → label E A → label E A → Set₁
l ⊑≡ l' =  _⊑_ {{LabOrd {{≡-Ord}}}} l l'

⊑≡-≡ : ∀ {E A} {l l' : label E A} → l ⊑≡ l' → l ≡ l'
⊑≡-≡ ⊑τ = refl
⊑≡-≡ (⊑ε e) = refl
⊑≡-≡ (⊑ι r) = refl
⊑≡-≡ (⊑ρ refl) = refl

⊑-≡ : ∀ {E A} {{_ : Ord A}} {l l' : label E A} → (∀ {x y : A} → x ⊑ y → x ≡ y) → l ⊑ l' → l ≡ l'
⊑-≡ eq ⊑τ = refl
⊑-≡ eq (⊑ε e) = refl
⊑-≡ eq (⊑ι r) = refl
⊑-≡ eq (⊑ρ x) rewrite eq x = refl

⊑≡-refl : ∀ {E A} {l : label E A} → l ⊑≡ l
⊑≡-refl = ⊑-refl {{LabOrd {{≡-Ord}}}}



~izero : ∀ {E A L} → {p q : CTree' E A}→  p ~̂ L [ 0 ] q
~izero = ≲izero

~istep : ∀ {E A i L} {p q : CTree' E A} →
    (left :  lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂ L [ lsuc l i ] q')) → 
    (right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂ L [ lsuc l i ] q')) →
    p ~̂ L [ suc i ] q
~istep {E} {A} {i} {L} {p} {q} left right = ≲istep left' right' where
    left' :  lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑≡ l' × q [ l' ]⇒ q' × p' ~̂ L [ lsuc l i ] q')
    left' ls tr with q' , tr' , b ← left ls tr = _ , q' , ⊑≡-refl , tr' , b
    right' : lsafe L p → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑≡ l × p [ l' ]⇒ p' × p' ~̂ L [ lsuc l i ] q')
    right' ls tr with q' , tr' , b ← right ls tr = _ , q' , ⊑≡-refl , tr' , b

≲ilsafe : ∀ {E A L i} {{_ : Ord A}} {p q : CTree' E A} → ¬ lsafe L p → p ≲̂ L [ i ] q
≲ilsafe {i = zero} ¬ls = ≲izero
≲ilsafe {i = suc i} ¬ls = ≲istep (λ ls tr → ⊥-elim (¬ls ls)) (λ ls tr → ⊥-elim (¬ls ls))

~ilsafe : ∀ {E A L i} {p q : CTree' E A} → ¬ lsafe L p → p ~̂ L [ i ] q
~ilsafe = ≲ilsafe {{≡-Ord}}

data AnyEff  {E : Set → Set} (e : Eff E) : Set where
  MkAnyEff : AnyEff e

AnyLab : ∀ {E A} {e : label E A} → AnyEff ?? e
AnyLab {e = ⟨ ε x ⟩} = isEffPredε x MkAnyEff
AnyLab {e = ⟨ ι x ⟩} = isEffPredι x
AnyLab {e = ⟨ ρ x ⟩} = isEffPredρ x
AnyLab {e = τ} = isEffPredτ

AnyEff-lsafe : ∀ {E A} {p : CTree' E A} → lsafe AnyEff p
AnyEff-lsafe tr = AnyLab

retFree-lpred : ∀ {E A B L} {l : label E A} {l' : label E B}  → retFree l l' → L ?? l → L ?? l'
retFree-lpred retFreeε (isEffPredε e x) = isEffPredε e x
retFree-lpred retFreeι (isEffPredι r) = isEffPredι r
retFree-lpred retFreeτ isEffPredτ = isEffPredτ

infix 3 _≲̂[_]_
_≲̂[_]_ : ∀ {E A} {{_ : Ord A}} → CTree' E A → ℕ → CTree' E A → Set₁
p ≲̂[ i ] q = p ≲̂ (AnyEff) [ i ] q


infix 3 _~̂[_]_ 

_~̂[_]_ : ∀ {E A} → CTree' E A → ℕ → CTree' E A → Set₁
p ~̂[ i ] q = p ~̂ AnyEff [ i ] q

≲istep' : ∀ {E A i} {{_ : Ord A}} {p q : CTree' E A} →
    (left :  ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂[ lsuc l i ] q')) → 
    (right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂[ lsuc l i ] q')) →
    p ≲̂[ suc i ] q
≲istep' left right = ≲istep (λ _ → left) (λ _ → right)

~istep' : ∀ {E A i} {p q : CTree' E A} →
    (left :  ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂[ lsuc l i ] q')) → 
    (right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂[ lsuc l i ] q')) →
    p ~̂[ suc i ] q
~istep' left right = ~istep (λ _ → left) (λ _ → right)


infix 3 _≲_[_]_

_≲_[_]_ : ∀ {E A} {{_ : Ord A}}  → CTree E A ∞ → epred E → ℕ → CTree E A ∞ → Set₁
p ≲ L [ i ] q = p ↑ ≲̂ L [ i ] q ↑

infix 3 _~_[_]_

_~_[_]_ : ∀ {E A} → CTree E A ∞ → epred E → ℕ → CTree E A ∞ → Set₁
p ~ L [ i ] q = p ↑ ~̂ L [ i ] q ↑


infix 3 _≲[_]_
_≲[_]_ : ∀ {E A}  {{_ : Ord A}}  → CTree E A ∞ → ℕ → CTree E A ∞ → Set₁
p ≲[ i ] q = p ↑ ≲̂[ i ] q ↑

infix 3 _~[_]_ 

_~[_]_ : ∀ {E A} → CTree E A ∞ → ℕ → CTree E A ∞ → Set₁
p ~[ i ] q = p ↑ ~̂[ i ] q ↑


≲ileft : ∀ {E A L i}  {{_ : Ord A}}  {p q : CTree' E A} → p ≲̂ L [ suc i ] q → lsafe L p
  → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')
≲ileft (≲istep left right) = left

~ileft : ∀ {E A L i} {p q : CTree' E A} → p ~̂ L [ suc i ] q → lsafe L p
  → ∀ {l p'} → p [ l ]⇒ p' → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂ L [ lsuc l i ] q')
~ileft (≲istep left right) ls tr
  with _ , q , leq , tr' , b ← left ls tr
  rewrite ⊑≡-≡ leq = q , tr' , b

≲ileft' : ∀ {E A i} {{_ : Ord A}}  {p q : CTree' E A} → p ≲̂[ suc i ] q
  → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂[ lsuc l i ] q')
≲ileft' (≲istep left right) = left AnyEff-lsafe

≲iright : ∀ {E A L i} {{_ : Ord A}} {p q : CTree' E A} → p ≲̂ L [ suc i ] q → lsafe L p
  → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q')
≲iright (≲istep left right) = right


~iright : ∀ {E A L i} {p q : CTree' E A} → p ~̂ L [ suc i ] q → lsafe L p
  → ∀ {l q'} → q [ l ]⇒ q' → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂ L [ lsuc l i ] q')
~iright (≲istep left right)  ls tr
  with _ , q , leq , tr' , b ← right ls tr
  rewrite ⊑≡-≡ leq = q , tr' , b


≲iright' : ∀ {E A i} {{_ : Ord A}} {p q : CTree' E A} → p ≲̂[ suc i ] q
  → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂[ lsuc l i ] q')
≲iright' (≲istep left right) = right AnyEff-lsafe


wait-lsafe : ∀ {E L A B} {c : B → CTree E A ∞} → lsafe L (wait B c)
wait-lsafe (⇒-inp r _) = isEffPredι r

_>>='_ : ∀ {A B E} → CTree' E A → (A → CTree E B ∞) → CTree' E B
wait _ c >>=' f = wait _ (λ r → c r >>= f)
(p ↑) >>=' f = (p >>= f) ↑

⊕-lsafe-l : ∀ {E L A} {p q : CTree E A ∞} → lsafe L ((p ⊕ q) ↑) → lsafe L (p ↑)
⊕-lsafe-l ls tr = ls (⇒-⊕-l tr)

⊕-lsafe-r : ∀ {E L A} {p q : CTree E A ∞} → lsafe L ((p ⊕ q) ↑) → lsafe L (q ↑)
⊕-lsafe-r ls tr = ls (⇒-⊕-r tr)


lsafe-⊑ : ∀ {E A L} {l l' : label E A} {{_ : Ord A}} → l ⊑ l' →  L ?? l →  L ?? l'
lsafe-⊑ ⊑τ isEffPredτ = isEffPredτ
lsafe-⊑ (⊑ρ x) (isEffPredρ v) = isEffPredρ _
lsafe-⊑ (⊑ι .v) (isEffPredι v) = isEffPredι v
lsafe-⊑ (⊑ε .e) (isEffPredε e x) = isEffPredε e x

lsafe-≲i : ∀ {i E A L} {{_ : Ord A}} {p q : CTree' E A} → lsafe L p → p ≲̂ L [ suc i ] q → lsafe L q
lsafe-≲i ls b tr with l' , p' , leq , tr' , b' ← ≲iright b ls tr = lsafe-⊑ leq (ls tr')

lsuc-mono : ∀ {E A j n} (l : label E A) → j ≤ n → lsuc l j ≤ lsuc l n
lsuc-mono ⟨ x ⟩ le = s≤s le
lsuc-mono τ le = le

lsuc-lmap : ∀ {E A B i} {f : A → B} (l : label E A) → lsuc (lmap f l) i ≡ lsuc l i
lsuc-lmap ⟨ ε x ⟩ = refl
lsuc-lmap ⟨ ι x ⟩ = refl
lsuc-lmap ⟨ ρ x ⟩ = refl
lsuc-lmap τ = refl

lsuc≤suc :  ∀ {E A} (l : label E A) i → lsuc l i ≤ suc i
lsuc≤suc ⟨ x ⟩ i = ≤-refl
lsuc≤suc τ i = n≤1+n i

lsuc-retFree : ∀ {E A B} {l : label E A} {l' : label E B} → retFree l l' → (i : ℕ) → lsuc l i ≡ lsuc l' i
lsuc-retFree retFreeε _ = refl
lsuc-retFree retFreeι _ = refl
lsuc-retFree retFreeτ _ = refl
