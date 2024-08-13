{-# OPTIONS --sized-types #-}

--------------------------
-- non-determinism laws --
--------------------------


module CTree.IndexedBisimilarity.NonDeterminism where

open import CTree.IndexedBisimilarity.BasicProperties public
open import Data.Nat
open import Data.Product


~i⊕-unit-l : ∀ {i E A L} {p : CTree E A ∞} → ∅ ⊕ p ~ L [ i ] p
~i⊕-unit-l {zero} = ~izero
~i⊕-unit-l {suc i} {p = p} = ~ilift (~istep' left right) where
  left : ∀ {l p'} → (∅ ⊕ p) ↑ [ l ]⇒ p' → ∃[ q' ] p ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-r trans') = _ , trans' , ~irefl
  right : ∀ {l q'} → p ↑ [ l ]⇒ q' → ∃[ p' ] (∅ ⊕ p) ↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right trans = _ , ⇒-⊕-r trans , ~irefl

 
~i⊕-assoc : ∀ {i E A L} {p q r : CTree E A ∞} → (p ⊕ q) ⊕ r ~ L [ i ] p ⊕ (q ⊕ r)
~i⊕-assoc {zero} = ~izero
~i⊕-assoc {suc i} {p = p} {q} {r} = ~ilift (~istep' left right) where
  left : ∀ {l p'} → (p ⊕ q ⊕ r)↑ [ l ]⇒ p' → ∃[ q' ] (p ⊕ (q ⊕ r))↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l (⇒-⊕-l tr)) =  _ , ⇒-⊕-l tr , ~irefl
  left (⇒-⊕-l (⇒-⊕-r tr)) = _ , ⇒-⊕-r (⇒-⊕-l tr) , ~irefl
  left (⇒-⊕-r tr) =  _ ,  ⇒-⊕-r (⇒-⊕-r tr) , ~irefl
  right : ∀ {l q'} → (p ⊕ (q ⊕ r))↑ [ l ]⇒ q' → ∃[ p' ] (p ⊕ q ⊕ r)↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right (⇒-⊕-r (⇒-⊕-r tr)) =  _ , ⇒-⊕-r tr , ~irefl
  right (⇒-⊕-r (⇒-⊕-l tr)) = _ , ⇒-⊕-l (⇒-⊕-r tr) , ~irefl
  right (⇒-⊕-l tr) =  _ ,  ⇒-⊕-l (⇒-⊕-l tr) , ~irefl

~i⊕-idem : ∀ {i E A L} {p : CTree E A ∞} → p ⊕ p ~ L [ i ] p
~i⊕-idem {zero} = ~izero
~i⊕-idem {suc i} {p = p} = ~ilift (~istep' left  λ tr →  _ , ⇒-⊕-l tr , ~irefl)  where
  left : ∀ {l p'} → (p ⊕ p)↑ [ l ]⇒ p' → ∃[ q' ] p ↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l tr) =  _ , tr , ~irefl
  left (⇒-⊕-r tr) = _ , tr , ~irefl

~i⊕-comm : ∀ {i E A L} {p q : CTree E A ∞} → p ⊕ q ~ L [ i ] q ⊕ p
~i⊕-comm {zero} = ~izero
~i⊕-comm {suc i} {p = p} {q} = ~ilift (~istep' left right) where
  left : ∀ {l p'} → (p ⊕ q)↑ [ l ]⇒ p' → ∃[ q' ] (q ⊕ p)↑ [ l ]⇒ q' × p' ~̂[ lsuc l i ] q'
  left (⇒-⊕-l tr) =  _ , ⇒-⊕-r tr , ~irefl
  left (⇒-⊕-r tr) = _ , ⇒-⊕-l tr , ~irefl
  right : ∀ {l q'} → (q ⊕ p)↑ [ l ]⇒ q' → ∃[ p' ] (p ⊕ q)↑ [ l ]⇒ p' × p' ~̂[ lsuc l i ] q'
  right (⇒-⊕-l tr) =  _ , ⇒-⊕-r tr , ~irefl
  right (⇒-⊕-r tr) = _ , ⇒-⊕-l tr , ~irefl

~i⊕-unit-r : ∀ {i E A L} {p : CTree E A ∞} → p ⊕ ∅ ~ L [ i ] p
~i⊕-unit-r = ~itrans ~i⊕-comm ~i⊕-unit-l

~i⊕-distr : ∀ {i E A B L} (p q : CTree E A ∞) {f : A → CTree E B ∞}
  → (p ⊕ q) >>= f ~ L [ i ] (p >>= f) ⊕ (q >>= f)
~i⊕-distr _ _ = ~irefl

≲i⊕-unit-l : ∀ {i E A L} {{_ : Ord A}} {p : CTree E A ∞} → ∅ ⊕ p ≲ L [ i ] p
≲i⊕-unit-l = ~i-≲i ~i⊕-unit-l
 
≲i⊕-assoc : ∀ {i E A L} {{_ : Ord A}} {p q r : CTree E A ∞} → (p ⊕ q) ⊕ r ≲ L [ i ] p ⊕ (q ⊕ r)
≲i⊕-assoc = ~i-≲i ~i⊕-assoc

≲i⊕-idem : ∀ {i E A L} {{_ : Ord A}} {p : CTree E A ∞} → p ⊕ p ≲ L [ i ] p
≲i⊕-idem = ~i-≲i ~i⊕-idem

≲i⊕-comm : ∀ {i E A L} {{_ : Ord A}} {p q : CTree E A ∞} → p ⊕ q ≲ L [ i ] q ⊕ p
≲i⊕-comm = ~i-≲i ~i⊕-comm


≲i⊕-unit-r : ∀ {i E A L} {{_ : Ord A}} {p : CTree E A ∞} → p ⊕ ∅ ≲ L [ i ] p
≲i⊕-unit-r = ~i-≲i ~i⊕-unit-r

≲i⊕-distr : ∀ {i E A B L} {{_ : Ord B}} (p q : CTree E A ∞) {f : A → CTree E B ∞}
  → (p ⊕ q) >>= f ≲ L [ i ] (p >>= f) ⊕ (q >>= f)
≲i⊕-distr p q = ~i-≲i (~i⊕-distr p q)
