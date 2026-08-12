{-# OPTIONS --safe #-}

------------------------------------------------------------------------
-- The partial semantics of section 2 of the paper: the `Maybe` monad,
-- used to make unsafe behaviour explicit, and the relation ⊥= that the
-- compiler calculation of section 2 is based on.
--
-- This module and Calculations.Maybe.Cond form the only part of the
-- development that typechecks with --safe: they use neither sized
-- types nor coinduction. Section 3.4 of the paper claims that skew
-- bisimilarity ⊥~ on choice trees corresponds to ⊥= on `Maybe`; that
-- correspondence is made precise in CTree.Maybe.
------------------------------------------------------------------------

module Maybe where

open import Data.Maybe using (Maybe ; just ; nothing ; _>>=_) public
open import Relation.Binary.PropositionalEquality


-- The monadic return operator, written `Just` in the paper.

return : ∀ {A : Set} → A → Maybe A
return = just


---------------------------------------------------------------------
-- The relation ⊥= on `Maybe`
---------------------------------------------------------------------

-- `p ⊥= q` holds if p is `nothing`, i.e. if p exhibits unsafe
-- behaviour, or else p and q are equal. The two constructors are the
-- two defining clauses (⊥=-Nothing) and (⊥=-Just) of the paper.

infix 3 _⊥=_

data _⊥=_ {A : Set} : Maybe A → Maybe A → Set where
  ⊥=-nothing : ∀ {q : Maybe A} → nothing ⊥= q
  ⊥=-just : ∀ {v : A} → just v ⊥= just v


-- ⊥= is a preorder.

⊥=-refl : ∀ {A : Set} {p : Maybe A} → p ⊥= p
⊥=-refl {p = nothing} = ⊥=-nothing
⊥=-refl {p = just v} = ⊥=-just

⊥=-trans : ∀ {A : Set} {p q r : Maybe A} → p ⊥= q → q ⊥= r → p ⊥= r
⊥=-trans ⊥=-nothing _ = ⊥=-nothing
⊥=-trans ⊥=-just le = le


-- Equal computations are in particular related by ⊥=. This is how the
-- monad laws below, which hold on the nose for `Maybe`, enter a ⊥=
-- calculation.

≡-⊥= : ∀ {A : Set} {p q : Maybe A} → p ≡ q → p ⊥= q
≡-⊥= refl = ⊥=-refl


---------------------------------------------------------------------
-- The monad laws
---------------------------------------------------------------------

-- Unlike for choice trees, where the corresponding laws only hold up
-- to bisimilarity (see CTree.BisimilarityLaws), the monad laws hold
-- as propositional equalities for `Maybe`.

return->>= : ∀ {A B : Set} (x : A) {f : A → Maybe B} → (return x >>= f) ≡ f x
return->>= x = refl

>>=-return : ∀ {A : Set} (p : Maybe A) → (p >>= return) ≡ p
>>=-return nothing = refl
>>=-return (just v) = refl

>>=-assoc : ∀ {A B C : Set} (p : Maybe A) {f : A → Maybe B} {g : B → Maybe C}
  → ((p >>= f) >>= g) ≡ (p >>= λ x → f x >>= g)
>>=-assoc nothing = refl
>>=-assoc (just v) = refl


---------------------------------------------------------------------
-- Congruence laws for >>=
---------------------------------------------------------------------

-- ⊥= is a congruence for >>=. This is what makes ⊥= usable as the
-- basis of a compiler calculation.

⊥=->>=-cong : ∀ {A B : Set} {p q : Maybe A} {f g : A → Maybe B}
  → p ⊥= q → (∀ x → f x ⊥= g x) → (p >>= f) ⊥= (q >>= g)
⊥=->>=-cong ⊥=-nothing h = ⊥=-nothing
⊥=->>=-cong (⊥=-just {v}) h = h v

⊥=->>=-cong-l : ∀ {A B : Set} {p q : Maybe A} {f : A → Maybe B}
  → p ⊥= q → (p >>= f) ⊥= (q >>= f)
⊥=->>=-cong-l ⊥=-nothing = ⊥=-nothing
⊥=->>=-cong-l ⊥=-just = ⊥=-refl

⊥=->>=-cong-r : ∀ {A B : Set} (p : Maybe A) {f g : A → Maybe B}
  → (∀ x → f x ⊥= g x) → (p >>= f) ⊥= (p >>= g)
⊥=->>=-cong-r nothing h = ⊥=-nothing
⊥=->>=-cong-r (just v) h = h v

-- The corresponding congruence law for propositional equality, used
-- for the purely equational steps of a calculation.

>>=-cong-r : ∀ {A B : Set} (p : Maybe A) {f g : A → Maybe B}
  → (∀ x → f x ≡ g x) → (p >>= f) ≡ (p >>= g)
>>=-cong-r nothing h = refl
>>=-cong-r (just v) h = h v


---------------------------------------------------------------------
-- Reasoning combinators
---------------------------------------------------------------------

-- These allow ⊥= calculations to be written in the same equational
-- style as the choice tree calculations (cf. ⊥~i-Calculation in
-- CTree.SkewIndexedBisimilarity): steps that hold as equalities are
-- written with ≡⟨_⟩ resp. ≡⟨⟩, steps that only hold up to ⊥= with
-- ⊥=⟨_⟩.

module ⊥=-Calculation where

  _⊥=⟨_⟩_ : ∀ {A : Set} (x : Maybe A) {y z : Maybe A} → x ⊥= y → y ⊥= z → x ⊥= z
  _⊥=⟨_⟩_ x r eq = ⊥=-trans r eq

  _≡⟨_⟩_ : ∀ {A : Set} (x : Maybe A) {y z : Maybe A} → x ≡ y → y ⊥= z → x ⊥= z
  _≡⟨_⟩_ x r eq = ⊥=-trans (≡-⊥= r) eq

  _≡⟨⟩_ : ∀ {A : Set} (x : Maybe A) {y : Maybe A} → x ⊥= y → x ⊥= y
  _≡⟨⟩_ x eq = eq

  _∎ : ∀ {A : Set} (x : Maybe A) → x ⊥= x
  _∎ x = ⊥=-refl

  infix  3 _∎
  infixr 1 _⊥=⟨_⟩_
  infixr 1 _≡⟨_⟩_
  infixr 1 _≡⟨⟩_
