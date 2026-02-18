
{-# OPTIONS --copatterns --sized-types --guardedness --large-indices #-}

-- This module defines an effect that allows us to express a stuck
-- computation in choice trees. This is relevant for the formulation
-- of skew bisimilarity, i.e. bisimilarity of choice trees that
-- never get stuck.

module CTree.Stuck where

open import Size

open import CTree.Definitions
open import CTree.Parallel
open import CTree.Transitions
open import CTree.IndexedBisimilarity.Definitions
open import CTree.IndexedBisimilarity.Interp
open import CTree.IndexedBisimilarity.Bind
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum hiding (map)
open import Induction.WellFounded
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

open import Memory public

data Stuck (E : Set → Set) : Set → Set where
  stuckEff : Stuck E ⊥
  notStuck : ∀ {A} → E A → Stuck E A

CTree⊥ : (Set → Set) → Set → Size → Set₁
CTree⊥ E A i = CTree (Stuck E) A i

CTree⊥' : (Set → Set) → Set → Set₁
CTree⊥' E A = CTree' (Stuck E) A


∞CTree⊥ : (Set → Set) → Set → Size → Set₁
∞CTree⊥ E A i = ∞CTree (Stuck E) A i


stuck : ∀ {E A} → CTree⊥ E A ∞
stuck = eff stuckEff ⊥-elim

interpMap⊥ : ∀ {E F : Set → Set} {S} → (∀ {B} → S → E B → CTree⊥ F (B × S) ∞) → (∀ {B} → S → Stuck E B → CTree⊥ F (B × S) ∞)
interpMap⊥ f s stuckEff = eff stuckEff ⊥-elim
interpMap⊥ f s (notStuck x) = f s x


interpSt⊥ : ∀ {i E F A S} → S → (∀ {B} → S → E B → CTree⊥ F (B × S) ∞) → CTree⊥ E A i → CTree⊥ F A i
interpSt⊥ s f p = interpSt s (interpMap⊥ f) p

∞interpSt⊥ : ∀ {i E F A S} → S → (∀ {B} → S → E B → CTree⊥ F (B × S) ∞) → ∞CTree⊥ E A i → ∞CTree⊥ F A i
∞interpSt⊥ s f p = ∞interpSt s (interpMap⊥ f) p


get : ∀ {E A} → Memory A → Reg → CTree⊥ E A ∞
get m r with (m #[ r ])
... | (just v) = return v
... | nothing = stuck
