{-# OPTIONS --copatterns --sized-types --guardedness #-}

----------------------------------
-- Bisimilarity of choice trees --
----------------------------------


module CTree.Bisimilarity where

open import CTree.IndexedBisimilarity
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_ ; _<_)
open import Data.List hiding ([_])
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
open import Induction.WellFounded
open import Data.Product.Relation.Binary.Lex.Strict

--------------------------------------------------------------------
-- This is the definition of (strong) bisimilarity of (generalised)
-- choice trees in terms of their LTS semantics.
--------------------------------------------------------------------

infix 3 _≲̂_!_

record _≲̂_!_  {E A} {{_ : Ord A}} (p : CTree' E A) (L : epred E) (q : CTree' E A) {i : Size} : Set₁ where
  coinductive
  constructor bisim
  field
    ≲left : lsafe L p → ∀ {l p'} {j : Size< i}  → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × (p' ≲̂ L ! q') {j})
    ≲right : lsafe L p → ∀ {l q'} {j : Size< i} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × (p' ≲̂ L ! q') {j})

open _≲̂_!_ public

infix 3 _≲_!_

_≲_!_ : ∀ {E A} {{_ : Ord A}} → CTree E A ∞ → epred E → CTree E A ∞ → Set₁
p ≲ L ! q = p ↑ ≲̂ L ! q ↑

infix 3 _≲̂_

_≲̂_ : ∀ {E A} {{_ : Ord A}} → CTree' E A → CTree' E A → Set₁
p ≲̂ q = p ≲̂ AnyEff ! q

infix 3 _≲_

_≲_ : ∀ {E A} {{_ : Ord A}} → CTree E A ∞ → CTree E A ∞ → Set₁
p ≲ q = p ≲ AnyEff ! q

infix 3 _~̂_!_

_~̂_!_ : ∀ {E A} → CTree' E A → epred E → CTree' E A → {i : Size} → Set₁
_~̂_!_ p L q {i} = _≲̂_!_  {{≡-Ord}} p L q {i}

infix 3 _~_!_

_~_!_ : ∀ {E A} → CTree E A ∞ → epred E → CTree E A ∞ → Set₁
_~_!_ = _≲_!_ {{≡-Ord}}

infix 3 _~_

_~_ : ∀ {E A} → CTree E A ∞ → CTree E A ∞ → Set₁
_~_ = _≲_ {{≡-Ord}}

infix 3 _~̂_

_~̂_ : ∀ {E A} → CTree' E A → CTree' E A → Set₁
_~̂_ = _≲̂_  {{≡-Ord}}

---------------------------------------------------------------------
-- We show that indexed bisimilarity is (classically) equivalent to
-- bisimilarity.
---------------------------------------------------------------------



-- bisimilarity ⇒ indexed bisimilarity

≲-≲i : ∀ {E L A i} {{_ : Ord A}} {p q : CTree' E A} → (p ≲̂ L ! q) → p ≲̂ L [ i ] q
≲-≲i = prf (<×⇐-wf _) where
  prf : ∀ {E L A i} {{_ : Ord A}} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → (p ≲̂ L ! q) → p ≲̂ L [ i ] q
  prf {i = zero} _ b = ≲izero
  prf {L = L} {i = suc i} {p} {q} (acc rec) b = ≲istep left right where
    left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')
    left ls {p'} tr with l' , q' , leq , tr' , b' ← ≲left b ls tr
      = l' , q' , leq , tr' , prf (rec _ (recStep tr)) b'
    right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q'
    right ls {q'} tr with l' , p' , leq , tr' , b' ← ≲right b ls tr
      = l' , p' , leq , tr' , prf (rec _ (recStep⊑ leq tr')) b'


~-~i : ∀ {E L A i} {p q : CTree' E A} → (p ~̂ L ! q) → p ~̂ L [ i ] q
~-~i = ≲-≲i {{≡-Ord}}

-- Next we show that indexed bisimilarity implies bisimilarity. To
-- this end we need a number of lemmas.

private
  ¬≲ileft : ∀ {E L A l i} {{_ : Ord A}} {p p' q : CTree' E A} → lsafe L p → p [ l ]⇒ p' → 
          (∀ {l' q'} → l ⊑ l' → q [ l' ]⇒ q' → ¬ (p' ≲̂ L [ i ] q')) → ¬ (p ≲̂ L [ suc i ] q)
  ¬≲ileft ls tr step bi
    with l' , q' , leq , tr' , bi' ← ≲ileft bi ls tr = step leq tr' (≲ilsuc bi')

  ¬≲iright : ∀ {E L A l i} {{_ : Ord A}} {q q' p : CTree' E A} → lsafe L p → q [ l ]⇒ q' → 
          (∀ {l' p'} → l' ⊑ l → p [ l' ]⇒ p' → ¬ (p' ≲̂ L [ i ] q')) → ¬ (p ≲̂ L [ suc i ] q)
  ¬≲iright ls tr step bi
    with l' , q' , leq , tr' , bi' ← ≲iright bi ls tr = step leq tr' (≲ilsuc bi')


module Classical where

  private 
    postulate ¬¬-elim : ∀ {l} {A : Set l} → ¬ ¬ A → A

    ¬∀-∃ : ∀ {l l'} → {A : Set l}  {P : A → Set l'} → ¬ (∀ i → P i) → (∃[ i ] ¬ P i)
    ¬∀-∃ ne =  ¬¬-elim λ f → ne (λ i → ¬¬-elim λ g → f (i , g))

    lem : ∀ {l} (A : Set l) → A ⊎ ¬ A
    lem _ = ¬¬-elim (λ f → f (inj₂ (λ a → f (inj₁ a))))

    mutual
      fin-nondet : ∀ {E A l l'} {{_ : Ord A}} (p : CTree' E A) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {l' p'} → l ⊑ l' → p [ l' ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {l' p'} → l ⊑ l' → p [ l' ]⇒ p' → P p' i
      fin-nondet (p ↑) = fin-nondet↑ p
      fin-nondet (wait B c) = fin-nondet-wait c

      fin-nondet↑ : ∀ {E A l l'} {{_ : Ord A}} (p : CTree E A ∞) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {l' p'} → l ⊑ l' → p ↑ [ l' ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {l' p'} → l ⊑ l' → p ↑ [ l' ]⇒ p' → P p' i

      fin-nondet↑ {l = l} (now v) down step with lem (l ⊑ ⟨ ρ v ⟩)
      ... | inj₁ (⊑ρ leq) with i , Pp' ← step (⊑ρ leq) (⇒-now v) = i , λ { _ (⇒-now v) → Pp'}
      ... | inj₂ neq =  0 ,  λ { {l'} leq (⇒-now v') →  ⊥-elim (neq leq)}
      fin-nondet↑ {l = ⟨ a ⟩} (later p) down step = 0 ,  λ { (⊑ε e) () ; (⊑ι r) () ; (⊑ρ x) ()}

      fin-nondet↑ {l = τ} (later p) down step with i , Pp ← step ⊑τ ⇒-later = i ,  λ {_ ⇒-later → Pp}
      fin-nondet↑ (p1 ⊕ p2) down step
        with i1 , P1 ← fin-nondet↑ p1 down (λ leq tr → step leq (⇒-⊕-l tr))
        with i2 , P2 ← fin-nondet↑ p2 down (λ leq tr → step leq (⇒-⊕-r tr))
          = i1 ⊔ i2 ,  λ { leq (⇒-⊕-l tr) → down (m≤m⊔n i1 i2) (P1 leq tr) ;
                           leq (⇒-⊕-r tr) → down (m≤n⊔m i1 i2) (P2 leq tr)}
      fin-nondet↑ ∅ down step  = 0 , λ _ ()
      fin-nondet↑ {l = l} (eff {B = B} e c) down step with lem (l ≡ ⟨ ε e ⟩)
      ... | inj₁ (refl) with i , Pp' ← step (⊑ε e) (⇒-eff e c) = i , λ { _ (⇒-eff _ _)  → Pp' }
      ... | inj₂ neq = 0 ,  λ { (⊑ε _) (⇒-eff _ _) → ⊥-elim (neq refl)}

      fin-nondet-wait : ∀ {E A l l' B} {{_ : Ord A }} (c : B → CTree E A ∞) {P : CTree' E A → ℕ → Set l' } →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {l' p'} → l ⊑ l' → wait B c [ l' ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {l' p'} → l ⊑ l' → wait B c [ l' ]⇒ p' → P p' i
      
      fin-nondet-wait {l = l} {B = B} c down step with lem (Σ[ r ∈ B ] l ≡ ⟨ ι r ⟩)
      ... | inj₁ (r , refl) with i , Pp' ← step (⊑ι r) (⇒-inp r c) = i , λ { (⊑ι _) (⇒-inp _ _)  → Pp' }
      ... | inj₂ neq = 0 ,  λ {(⊑ι _ )(⇒-inp r _) → ⊥-elim (neq (r , refl))}


  fin-nondet' : ∀ {E A l l'} {{_ : Ord A}} (p : CTree' E A) {P : CTree' E A → ℕ → Set l'} →
        (∀ {i j p'} → i ≤ j → P p' i → P p' j) →
        (∀ {l' p'} → l' ⊑ l → p [ l' ]⇒ p' → ∃[ i ] P p' i) → ∃[ i ] ∀ {l' p'} → l' ⊑ l → p [ l' ]⇒ p' → P p' i
  fin-nondet' {l = l} {{O}} p {P = P} down step
    with i , st ← fin-nondet {{Ord-rev O}} p down (λ leq → step (⊑lab-rev' leq))
      = i , λ leq tr → st (⊑lab-rev leq) tr



-- indexed bisimilarity ⇒ bisimilarity

  ≲i-≲ : ∀ {E L A j} {{_ : Ord A}} {p q : CTree' E A} → (∀ i → p ≲̂ L [ i ] q) → (p ≲̂ L ! q) {j}
  ≲left (≲i-≲ {p = p} {q} ibi) ls {p' = p'} tr = ¬¬-elim  λ ¬left →
    ¬≲ileft ls tr (proj₂ (fin-nondet _ (λ le ¬Pi Pj → ¬Pi (≲idown le Pj))
    (λ {l' q'} leq tr' → ¬∀-∃ λ trs → ¬left (l' , q' , leq , tr' , ≲i-≲ trs)  ))) (ibi _) 
  ≲right (≲i-≲ {p = p} {q} ibi) ls {q' = q'} tr = ¬¬-elim  λ ¬right →
    ¬≲iright ls tr (proj₂ (fin-nondet' _ (λ le ¬Pi Pj → ¬Pi (≲idown le Pj))
    (λ {l' q'} leq tr' → ¬∀-∃ λ trs → ¬right (l' , q' , leq , tr' , ≲i-≲ trs)  ))) (ibi _) 

open Classical public

~i-~ : ∀ {E L A j} {p q : CTree' E A} → (∀ i → p ~̂ L [ i ] q) → (p ~̂ L ! q) {j}
~i-~ = ≲i-≲ {{≡-Ord}}
