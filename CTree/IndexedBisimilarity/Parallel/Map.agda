{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.Parallel.Map where

open import CTree.IndexedBisimilarity.BasicProperties
open import CTree.IndexedBisimilarity.Bind
open import CTree.IndexedBisimilarity.Interp
open import CTree.IndexedBisimilarity.Parallel.Congruence
open import CTree.Parallel
open import Data.Nat
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Function using (id; _∘_)

------------------------------
-- map distributes over par --
------------------------------

~i∥-map : ∀ {i A A' B B' E L} {{_ : Concurrent E}}
  (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
  → map (map× f g)  (p ∥ q) ~ L [ i ] map f p ∥ map g q
~i∥-map p q = ~i⊕-cong (~i⊕-cong (⦉-map p q) (⦊-map p q)) (⋈-map p q) where

  ⦉-map : ∀ {i A A' B B' E L} {{_ : Concurrent E}}
    (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⦉ q) ~ L [ i ] map f p ⦉ map g q
  ⦉-map (now v) q = ~irefl
  ⦉-map {zero} (later p) q = ~izero
  ⦉-map {suc i} (later p) q = ~ilater (~i∥-map (force p) q)
  ⦉-map (p1 ⊕ p2) q = ~i⊕-cong (⦉-map p1 q) (⦉-map p2 q)
  ⦉-map ∅ q = ~irefl
  ⦉-map (eff e c) q = ~ieff e (λ r → ~i∥-map (c r) q)

  ⦊-map : ∀ {i A A' B B' E L} {{_ : Concurrent E}}
    (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⦊ q) ~ L [ i ] map f p ⦊ map g q
  ⦊-map p (now v) = ~irefl
  ⦊-map {zero} p (later q) = ~izero
  ⦊-map {suc i} p (later q) = ~ilater (~i∥-map p (force q))
  ⦊-map p (q1 ⊕ q2) = ~i⊕-cong (⦊-map p q1) (⦊-map p q2)
  ⦊-map p ∅ = ~irefl
  ⦊-map p (eff e c) = ~ieff e (λ r → ~i∥-map p (c r))

  ⋈-map : ∀ {i A A' B B' E L}
    {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
    → map (map× f g)  (p ⋈ q) ~ L [ i ] map f p ⋈ map g q
  ⋈-map (now v) (now v₁) = ~irefl
  ⋈-map (now v) (later p) = ~irefl
  ⋈-map (now v) (q1 ⊕ q2) = ~i⊕-cong (⋈-map (now v) q1) (⋈-map (now v) q2)
  ⋈-map (now v) ∅ = ~irefl
  ⋈-map (now v) (eff e c) = ~irefl
  ⋈-map (later p) (now v) = ~irefl
  ⋈-map (later p) (later p₁) = ~irefl
  ⋈-map (later p) (q1 ⊕ q2) = ~i⊕-cong (⋈-map (later p) q1) (⋈-map (later p) q2)
  ⋈-map (later p) ∅ = ~irefl
  ⋈-map (later p) (eff e c) = ~irefl
  ⋈-map (p1 ⊕ p2) q =  ~i⊕-cong (⋈-map p1 q) (⋈-map p2 q)
  ⋈-map ∅ (now v) = ~irefl
  ⋈-map ∅ (later p) = ~irefl
  ⋈-map ∅ (q1 ⊕ q2) = ~i⊕-cong (⋈-map ∅ q1) (⋈-map ∅ q2)
  ⋈-map ∅ ∅ = ~irefl
  ⋈-map ∅ (eff e c) = ~irefl
  ⋈-map (eff e c) (now v) = ~irefl
  ⋈-map (eff e c) (later p) = ~irefl
  ⋈-map p@(eff e c) (q1 ⊕ q2) = ~i⊕-cong (⋈-map p q1) (⋈-map p q2)
  ⋈-map (eff e c) ∅ = ~irefl
  ⋈-map {zero} _ _ = ~izero
  ⋈-map {suc i} (eff e1 c1) (eff e2 c2) =
    ~itrans (~i>>=-assoc (e1 ⇄ e2)) (~i>>=-cong-r (e1 ⇄ e2) λ (r1 , r2) → ~i∥-map (c1 r1) (c2 r2))


≲i∥-map : ∀ {i A A' B B' E L} {{_ : Ord A'}} {{_ : Ord B'}} {{_ : Concurrent E}}
  (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'} {g : B → B'}
  → map (map× f g)  (p ∥ q) ≲ L [ i ] map f p ∥ map g q
≲i∥-map p q = ~i-≲i (~i∥-map p q)


------------------------------------
-- Corresponding properties for ∥ʳ --
------------------------------------


open ~i-Calculation

~i∥ʳ-map-r : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : B → C} 
  → map f (p ∥ʳ q) ~[ i ] p ∥ʳ (map f q)
~i∥ʳ-map-r p q {f} = 
  map f (map proj₂ (p ∥ q))
    ~⟨ ~imap-∘ (p ∥ q) ⟩
  map (λ (x , y) → proj₂ (x , f y)) (p ∥ q)
    ~⟨ ~isym (~imap-∘ (p ∥ q)) ⟩
  map proj₂ (map (λ (x , y) → (x , f y)) (p ∥ q))
    ~⟨ ~imap-cong (~i∥-map p q) ⟩
  map id p ∥ʳ map f q
    ~⟨ ~i∥ʳ-cong-l (~imap-id p) ⟩
  (p ∥ʳ map f q)
  ∎

≲i∥ʳ-map-r : ∀ {i A B C E} {{_ : Ord C}} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : B → C} 
  → map f (p ∥ʳ q) ≲[ i ] p ∥ʳ (map f q)
≲i∥ʳ-map-r p q = ~i-≲i (~i∥ʳ-map-r p q)

~i∥ʳ-map-r' : ∀ {i A B C D E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : B → C} {g : C → CTree E D ∞}
  → ((p ∥ʳ q) >>= (λ v → g (f v))) ~[ i ] ((p ∥ʳ (map f q)) >>= g)
~i∥ʳ-map-r' p q {f} {g} =
  (((p ∥ q) >>= λ x → return (proj₂ x)) >>= (λ v → g (f v)))
  ~⟨ ~i>>=-assoc (p ∥ q) ⟩
  ((p ∥ q) >>= (λ x → return (proj₂ x) >>= (λ v → g (f v))))
  ≡⟨⟩
  ((p ∥ q) >>= (λ x → g (f (proj₂ x))))
  ≡⟨⟩
  ((p ∥ q) >>= (λ x → return (f (proj₂ x)) >>= g))
  ~⟨ ~isym (~i>>=-assoc (p ∥ q)) ⟩
  ((p ∥ q) >>= (λ x → return (f (proj₂ x))) >>= g)
  ~⟨ ~i>>=-cong-l (~isym (~imap-∘ (p ∥ q))) ⟩
  ((map f (p ∥ʳ q)) >>= g)
  ~⟨ ~i>>=-cong-l (~i∥ʳ-map-r p q) ⟩
  ((p ∥ʳ map f q) >>= g)
  ∎

≲i∥ʳ-map-r' : ∀ {i A B C D E} {{_ : Ord D}} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
  {f : B → C} {g : C → CTree E D ∞} → ((p ∥ʳ q) >>= (λ v → g (f v))) ≲[ i ] ((p ∥ʳ (map f q)) >>= g)
≲i∥ʳ-map-r' p q = ~i-≲i (~i∥ʳ-map-r' p q)

~i∥ʳ-map-l : ∀ {i A A' B E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'}
  → p ∥ʳ q ~[ i ]  map f p ∥ʳ q
~i∥ʳ-map-l p q {f} =
  map proj₂ (p ∥ q)
  ≡⟨⟩
  map (λ (x , y) → proj₂ (f x , y)) (p ∥ q)
  ~⟨ ~isym (~imap-∘ (p ∥ q)) ⟩
  map proj₂ (map (map× f id) (p ∥ q))
  ~⟨ ~imap-cong (~i∥-map p q) ⟩
  map f p ∥ʳ map id q
  ~⟨ ~i∥ʳ-cong-r (~imap-id q) ⟩
  map f p ∥ʳ q
  ∎

≲i∥ʳ-map-l : ∀ {i A A' B E} {{_ : Ord B}} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) {f : A → A'}
  → p ∥ʳ q ≲[ i ]  map f p ∥ʳ q
≲i∥ʳ-map-l p q = ~i-≲i (~i∥ʳ-map-l p q)
