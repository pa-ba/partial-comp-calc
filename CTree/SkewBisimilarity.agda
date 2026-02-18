{-# OPTIONS --copatterns --sized-types --guardedness #-}



-- Skew strong bisimilarity is defined as strong bisimiliarity
-- that is conditional on the left-hand side term being safe (= does
-- not permit a transition that gets stuck).


module CTree.SkewBisimilarity where

open import CTree.Definitions
open import CTree.Stuck
open import CTree.Safe
open import CTree.SkewIndexedBisimilarity
open import CTree.Bisimilarity
open import Preorder
open import Relation.Binary.PropositionalEquality

open import Data.Nat
open import Data.Nat.Properties

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




⊥~i-⊥~ : ∀ {E A} {p q : CTree⊥ E A ∞} → (∀ i → p ⊥~[ i ] q) → p ⊥~ q
⊥~i-⊥~ = ~i-~


⊥~-⊥~i : ∀ {i E A} {p q : CTree⊥ E A ∞} → p ⊥~ q → p ⊥~[ i ] q
⊥~-⊥~i = ~-~i

⊥≲i-⊥≲ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → (∀ i → p ⊥≲[ i ] q) → p ⊥≲ q
⊥≲i-⊥≲ = ≲i-≲


⊥≲-⊥≲i : ∀ {i E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊥≲ q → p ⊥≲[ i ] q
⊥≲-⊥≲i = ≲-≲i

------------------------
-- Proposition 1 (ii) --
------------------------

⊥~-~ : ∀ {E A } {p q : CTree⊥ E A ∞} → safe p → p ⊥~ q → p ~ q
⊥~-~ s b = ~i-~ (λ i → ⊥~i-~i s (⊥~-⊥~i {i} b))


------------------------
-- Proposition 1 (i) --
------------------------
~-⊥~ : ∀ {E A} {p q : CTree⊥ E A ∞} → p ~ q → p ⊥~ q
~-⊥~ b = ~i-~ (λ i → ~i-⊥~i ((~-~i  b)))


-----------------------
-- Proposition 2 (i) --
-----------------------

⊥~-⊥≲ : ∀ {E A } {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊥~ q → p ⊥≲ q
⊥~-⊥≲ b = ⊥≲i-⊥≲ (λ i → ⊥~i-⊥≲i (⊥~-⊥~i b))

------------------------
-- Proposition 2 (ii) --
------------------------

⊥≲-⊥~ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ⊥≲ q → p ⊥~ q
⊥≲-⊥~ s b = ⊥~i-⊥~ (λ i → ⊥≲i-⊥~i s (⊥≲-⊥≲i b))

-----------------
-- Corollary 3 --
-----------------

⊥≲-~ : ∀ {E A B P} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥ E A ∞} {f : A → B} 
  → safeP P p → (∀ {x y : B} → x ⊑ y → x ≡ y) → (∀ {a b} → a ⊑ b → f a ⊑ f b) → p ⊥≲ q → map f p ~ map f q
⊥≲-~ S E M b = ~i-~ (λ i → ⊥≲i-~i S E M (⊥≲-⊥≲i b))

⊥≲-≲ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → safe p → p ⊥≲ q → p ≲ q
⊥≲-≲ s b = ≲i-≲ (λ i → ⊥≲i-≲i s (⊥≲-⊥≲i {i} b))
