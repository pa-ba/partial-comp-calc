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


⊥~-~ : ∀ {E A } {p q : CTree⊥ E A ∞} → safe p → p ⊥~ q → p ~ q
⊥~-~ s b = ~i-~ (λ i → ⊥~i-~i s (⊥~-⊥~i {i} b))


⊥≲-≲ : ∀ {E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → safe p → p ⊥≲ q → p ≲ q
⊥≲-≲ s b = ≲i-≲ (λ i → ⊥≲i-≲i s (⊥≲-⊥≲i {i} b))
