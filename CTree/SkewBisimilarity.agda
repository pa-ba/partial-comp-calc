{-# OPTIONS --sized-types #-}



-- Skew strong bisimilarity is defined as strong bisimiliarity
-- that is conditional on the left-hand side term being safe (= does
-- not permit a transition that gets stuck).


module CTree.SkewBisimilarity where

open import CTree.Definitions
open import CTree.Stuck
open import CTree.Safe
open import CTree.IndexedBisimilarity
open import CTree.SkewIndexedBisimilarity
open import CTree.Bisimilarity
open import CTree.BisimilarityLaws
open import Preorder
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Unit

infix 3 _⊥~̂_

infix 3 _⊥~_

infix 3 _⊥≲̂_

infix 3 _⊥≲_

_⊥~̂_ : ∀ {E A} → CTree⊥' E A → CTree⊥' E A → Set₁
p ⊥~̂ q = p ~̂ NotStuckEff ! q

_⊥~_ : ∀ {E A} → CTree⊥ E A ∞ → CTree⊥ E A ∞ → Set₁
p ⊥~ q = p ~ NotStuckEff ! q

_⊥≲_ : ∀ {E A} {{_ : Ord A}} → CTree⊥ E A ∞ → CTree⊥ E A ∞ → Set₁
p ⊥≲ q = p ≲ NotStuckEff ! q

_⊥≲̂_ : ∀ {E A} {{_ : Ord A}} → CTree⊥' E A → CTree⊥' E A → Set₁
p ⊥≲̂ q = p ≲̂ NotStuckEff ! q




-- (skew) bisimilarity ⇒ step-indexed (skew) bisimilarity

⊥~-⊥~i : ∀ {i E A} {p q : CTree⊥ E A ∞} → p ⊥~ q → p ⊥~[ i ] q
⊥~-⊥~i = ~-~i

⊥≲-⊥≲i : ∀ {i E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊥≲ q → p ⊥≲[ i ] q
⊥≲-⊥≲i = ≲-≲i

-- The converse directions are the only results about skew
-- bisimilarity that need classical reasoning, and they take
-- double-negation elimination as an explicit assumption.

⊥~i-⊥~ : DNE → ∀ {E A} {p q : CTree⊥ E A ∞} → (∀ i → p ⊥~[ i ] q) → p ⊥~ q
⊥~i-⊥~ dne = ~i-~ dne

⊥≲i-⊥≲ : DNE → ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → (∀ i → p ⊥≲[ i ] q) → p ⊥≲ q
⊥≲i-⊥≲ dne = ≲i-≲ dne


⊥~stuck : ∀ {E A i} {p : CTree⊥ E A ∞} {f} → (eff stuckEff f ↑ ~̂ NotStuckEff ! p ↑) {i}
≲left  ⊥~stuck ls _ = ⊥-elim (stuck-lsafe ls)
≲right ⊥~stuck ls _ = ⊥-elim (stuck-lsafe ls)

⊥≲stuck : ∀ {E A i} {{_ : Ord A}} {p : CTree⊥ E A ∞} {f} → (eff stuckEff f ↑ ≲̂ NotStuckEff ! p ↑) {i}
≲left  ⊥≲stuck ls _ = ⊥-elim (stuck-lsafe ls)
≲right ⊥≲stuck ls _ = ⊥-elim (stuck-lsafe ls)


-- Coinductive counterpart of ⊥≲i-≲i: if the left-hand side is safe,
-- then the local safety side condition of skew bisimilarity is
-- vacuous, and skew bisimilarity coincides with bisimilarity.
⊥≲-≲' : ∀ {E A P i} {{_ : Ord A}} {p q : CTree⊥' E A}
  → safeP' P p → (p ≲̂ NotStuckEff ! q) {i} → (p ≲̂ AnyEff ! q) {i}
≲left  (⊥≲-≲' s b) _ tr with l' , q' , leq , tr' , b' ← ≲left b (safeP-lsafe s) tr
  = l' , q' , leq , tr' , ⊥≲-≲' (safeP⇒ s tr) b'
≲right (⊥≲-≲' s b) _ tr with l' , p' , leq , tr' , b' ← ≲right b (safeP-lsafe s) tr
  = l' , p' , leq , tr' , ⊥≲-≲' (safeP⇒ s tr') b'

-----------------------
-- Proposition 1 (i) --
-----------------------
~-⊥~ : ∀ {E A} {p q : CTree⊥ E A ∞} → p ~ q → p ⊥~ q
~-⊥~ = ~lift


------------------------
-- Proposition 1 (ii) --
------------------------

⊥~-~ : ∀ {E A } {p q : CTree⊥ E A ∞} → safe p → p ⊥~ q → p ~ q
⊥~-~ s = ⊥≲-≲' {{≡-Ord}} (safeP↑ s)


-----------------------
-- Proposition 2 (i) --
-----------------------

⊥~-⊥≲ : ∀ {E A } {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊥~ q → p ⊥≲ q
⊥~-⊥≲ {{O}} = ≲-weaken {{≡-Ord}} {{O}} λ {refl → ⊑-refl {{O}}}

------------------------
-- Proposition 2 (ii) --
------------------------

⊥≲-⊥~ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ⊥≲ q → p ⊥~ q
⊥≲-⊥~ = ≲-~


⊥≲-≲ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → safe p → p ⊥≲ q → p ≲ q
⊥≲-≲ s = ⊥≲-≲' (safeP↑ s)


-----------------
-- Corollary 3 --
-----------------


⊥≲-~ : ∀ {E A B P} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥ E A ∞} {f : A → B}
  → safeP P p → (∀ {x y : B} → x ⊑ y → x ≡ y) → (∀ {a b} → a ⊑ b → f a ⊑ f b) → p ⊥≲ q → map f p ~ map f q
⊥≲-~ S ⊑to≡ M b = ≲-~ ⊑to≡ (⊥≲-≲' (safeP↑ (safeP-map S (λ _ → tt))) (≲map-cong M b))


---------------------------------------------------------------------
-- The monad and functor laws and the congruence law for >>= (see
-- CTree.BisimilarityLaws) are parametric in the effect predicate L,
-- so they hold for skew bisimilarity by instantiating L to
-- NotStuckEff. We spell out the laws of section 3.3 of the paper in
-- the ⊥~ / ⊥≲ notation here.
---------------------------------------------------------------------

⊥~return->>= : ∀ {E A B} {x : A} {f : A → CTree⊥ E B ∞} → (return x >>= f) ⊥~ f x
⊥~return->>= = ~refl

⊥~>>=-return : ∀ {E A} {p : CTree⊥ E A ∞} → (p >>= return) ⊥~ p
⊥~>>=-return = ~>>=-return

⊥~>>=-assoc : ∀ {E A B C} (p : CTree⊥ E A ∞) {k : A → CTree⊥ E B ∞} {l : B → CTree⊥ E C ∞}
  → ((p >>= k) >>= l) ⊥~ (p >>= λ a → k a >>= l)
⊥~>>=-assoc = ~>>=-assoc

⊥~>>=-cong : ∀ {E A B} {p q : CTree⊥ E A ∞} {k k' : A → CTree⊥ E B ∞}
  → p ⊥~ q → (∀ a → k a ⊥~ k' a) → (p >>= k) ⊥~ (q >>= k')
⊥~>>=-cong b h = ~>>=-cong b h

⊥≲>>=-cong : ∀ {E A B} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥ E A ∞} {k k' : A → CTree⊥ E B ∞}
  → p ⊥≲ q → (∀ {a b} → a ⊑ b → k a ⊥≲ k' b) → (p >>= k) ⊥≲ (q >>= k')
⊥≲>>=-cong b h = ≲>>=-cong b h
