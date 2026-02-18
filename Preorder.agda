module Preorder where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List
open import Data.Nat
import Level as L

-- preorder
record Ord {a} (M : Set a) : Set (L.suc a) where
  infix 3 _⊑_
  field
    _⊑_ : M → M → Set a
    ⊑-refl : ∀ {m : M} → m ⊑ m
    ⊑-trans : ∀ {m n u : M} → m ⊑ n → n ⊑ u → m ⊑ u

open Ord {{...}} public

instance   
  ProdOrd : {A B : Set} → {{M : Ord A}} → {{N : Ord B}} → Ord (A × B)
  ProdOrd {A} {B} {{M}} {{N}} = record {
    _⊑_ = λ {(x1 , y1) (x2 , y2) → x1 ⊑ x2 × y1 ⊑ y2 };
    ⊑-refl =  ⊑-refl {{M}} , ⊑-refl {{N}};
    ⊑-trans =  λ {(x1 , y1) (x2 , y2) → ⊑-trans {{M}} x1 x2 , ⊑-trans {{N}} y1 y2 } 
    }

≡-Ord : ∀ {A : Set} → Ord A
≡-Ord = record {
    _⊑_ = _≡_;
    ⊑-refl = refl;
    ⊑-trans = trans } 


Ord-rev : ∀ {A : Set} → Ord A → Ord A
Ord-rev O = record {
    _⊑_ = λ x y → _⊑_ {{O}} y x;
    ⊑-refl = ⊑-refl {{O}};
    ⊑-trans = λ x y → ⊑-trans {{O}} y x } 

instance
  NatOrd : Ord ℕ
  NatOrd = record {
    _⊑_ = λ x y → x ≡ y;
    ⊑-refl =  refl;
    ⊑-trans =  trans 
    }


data _⊑L_  {A : Set} {{_ : Ord A}} : (List A) → (List A) → Set where
  ⊑L-nil : [] ⊑L []
  ⊑L-cons : ∀ {x y xs ys} → x ⊑ y → xs ⊑L ys → (x ∷ xs) ⊑L (y ∷ ys)


⊑L-refl : ∀ {A}  {{M : Ord A}} (m : List A) → m ⊑L m
⊑L-refl [] = ⊑L-nil
⊑L-refl {{M}} (x ∷ xs) = ⊑L-cons  (⊑-refl {{M}})  (⊑L-refl xs)

⊑L-trans : ∀ {A : Set} {{M : Ord A}} {m n u : List A} → m ⊑L n → n ⊑L u → m ⊑L u
⊑L-trans ⊑L-nil r = r
⊑L-trans {{M}} (⊑L-cons x l) (⊑L-cons y r) = ⊑L-cons (⊑-trans {{M}} x y) (⊑L-trans l r)


ListOrd : (A : Set) → {{_ : Ord A}} → Ord (List A)
ListOrd A = record {
    _⊑_ = _⊑L_;
    ⊑-refl =  ⊑L-refl _;
    ⊑-trans = ⊑L-trans } 
