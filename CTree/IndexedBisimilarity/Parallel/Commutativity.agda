{-# OPTIONS --sized-types --guardedness #-}


module CTree.IndexedBisimilarity.Parallel.Commutativity where

open import CTree.IndexedBisimilarity.BasicProperties
open import CTree.IndexedBisimilarity.Bind
open import CTree.IndexedBisimilarity.Parallel.Map
open import CTree.IndexedBisimilarity.Parallel.Decomposition
open import CTree.IndexedBisimilarity.Parallel.Congruence


open import Data.Nat
open import Relation.Nullary
open import Data.Sum hiding (map;swap)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map; symmetric)
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Function using (id)

------------------------------
-- commutativity for ∥ and ∥⃗ --
------------------------------

lmap-swap-swap : ∀ {E A B} (l : label E (A × B)) → lmap swap (lmap swap l) ≡ l
lmap-swap-swap ⟨ ε x ⟩ = refl
lmap-swap-swap ⟨ ι x ⟩ = refl
lmap-swap-swap ⟨ ρ (fst , snd) ⟩ = refl
lmap-swap-swap τ = refl

swap-bijection : ∀ {A B : Set} (x : A × B) → swap (swap x) ≡ x
swap-bijection (x , y) = refl

~i∥-comm : ∀ {i A B E L} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
  → p ∥ q ~ L [ i ] map swap (q ∥ p)
~i∥-comm p q = prf p q (<×⇐⁺×⇐⁺-wf _) where
  prf : ∀ {i A B E L} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
        (ac : Acc (×-Lex _≡_ _<_ (×-Lex _≡_ _⇐⁺_ _⇐⁺_)) (i , (p ↑ , q ↑)))
         → p ∥ q ~ L [ i ] map swap (q ∥ p)
  prf {zero} p q _  = ~izero
  prf {suc i} {L = L} p q (acc rec) = ~istep left right where
    left : lsafe L ((p ∥ q) ↑) → ∀ {l p' } → ((p ∥ q) ↑) [ l ]⇒ p' → ∃[ q' ] (map swap (q ∥ p) ↑) [ l ]⇒ q' × p' ~̂ L [ lsuc l i ] q'
    left _ {l} tr with ∥-step tr
    ... | inj₁ (inj₁ (LS rf tr')) = _ , map-step2 ((q ∥ p) ↑) swap (coerce-retFree rf)
      (∥-stepRight (RS (coerce-retFree' rf) tr')) , comml _ rf tr' where
        comml : ∀ {l'} p' → retFree l l' → p ↑ [ l' ]⇒ p' → p' ∥₁ q ~̂ L [ lsuc l i ] map' swap (q ∥₂ p')
        comml {⟨ a ⟩} (p' ↑) rf tr = prf p' q (rec (inj₂ (lsuc-retFree rf _ , inj₁ [ ( a , tr) ])))
        comml {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf (c v) q (rec (inj₂ (lsuc-retFree rf _
                                         , inj₁ (( ι v , ⇒-inp v c) ∷  [(a , tr)])))))
        comml {τ} (p' ↑) retFreeτ tr = prf p' q (rec (inj₁ ≤-refl))
        comml {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf (c v) q (rec (inj₁ ≤-refl)))
    ... | inj₁ (inj₂ (RS rf tr')) = _ , map-step2 ((q ∥ p) ↑) swap (coerce-retFree rf)
      (∥-stepLeft (LS (coerce-retFree' rf) tr')) , commr _ rf tr' where
        commr : ∀ {l'} q' → retFree l l' → q ↑ [ l' ]⇒ q' → p ∥₂ q' ~̂ L [ lsuc l i ] map' swap (q' ∥₁ p)
        commr {⟨ a ⟩} (q' ↑) rf tr = prf p q' (rec (inj₂ (lsuc-retFree rf _ , inj₂ (refl , [ ( a , tr) ]))))
        commr {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p (c v) (rec (inj₂ (lsuc-retFree rf _
                                         , inj₂ (refl , ( ι v , ⇒-inp v c) ∷  [(a , tr)])))))
        commr {τ} (q' ↑) retFreeτ tr = prf p q' (rec (inj₁ ≤-refl))
        commr {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p (c v) (rec (inj₁ ≤-refl)))
    ... | inj₂ (BSRet tr1 tr2) = _ , map-step1 swap (∥-stepBoth (BSRet tr2 tr1)) , ~irefl
    ... | inj₂ (BSSync {p' = p'} {q' = q'} {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr) =
      let b = prf (p' v1) (q' v2) (rec (inj₂ (refl ,  inj₁ ( ( -, ⇒-inp v1 p') ∷ [ -, tr1 ])))) in
       _ , map-step-lmap {l = lmap swap l} ((q ∥ p) ↑) swap (∥-stepBoth
            (BSSync tr2 tr1 (⇄-sym _ _ tr))) , ~isuc b
    right : lsafe L ((p ∥ q) ↑) → ∀ {l q' } → (map swap (q ∥ p) ↑) [ l ]⇒ q' → ∃[ p' ] ((p ∥ q) ↑) [ l ]⇒ p' × p' ~̂ L [ lsuc l i ] q'
    right _ {l} tr with map-step ((q ∥ p) ↑) swap tr
    right _ {l} tr_ | inj₁ (v , tr' , refl) with ∥-step tr'
    ... | inj₁ (inj₁ ls) with () ← leftStep-ρ ls
    ... | inj₁ (inj₂ rs) with () ← rightStep-ρ rs
    ... | inj₂ (BSRet tr1 tr2) rewrite ⇒-ρ-∅ tr_ = _ , ∥-stepBoth (BSRet tr2 tr1) , ~irefl
    right _ {l} tr | inj₂ (l' , rf , r , tr' , refl) with ∥-step tr'
    ... | inj₁ (inj₁ (LS rf' tr'')) = _ , ∥-stepRight (RS (retFree-trans rf rf') tr'')
                                      , commr _ (retFree-trans rf rf') tr'' where
        commr : ∀ {l'} q' → retFree l l' → q ↑ [ l' ]⇒ q' → p ∥₂ q' ~̂ L [ lsuc l i ] map' swap (q' ∥₁ p)
        commr {⟨ a ⟩} (q' ↑) rf tr = prf p q' (rec (inj₂ (lsuc-retFree rf _ , inj₂ (refl , [ ( a , tr) ]))))
        commr {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf p (c v) (rec (inj₂ (lsuc-retFree rf _
                                         , inj₂ (refl , ( ι v , ⇒-inp v c) ∷  [(a , tr)])))))
        commr {τ} (q' ↑) retFreeτ tr = prf p q' (rec (inj₁ ≤-refl))
        commr {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf p (c v) (rec (inj₁ ≤-refl)))
    ... | inj₁ (inj₂ (RS rf' tr'')) = _ , ∥-stepLeft (LS (retFree-trans rf rf') tr'')
                                      , comml _ (retFree-trans rf rf') tr'' where
        comml : ∀ {l'} p' → retFree l l' → p ↑ [ l' ]⇒ p' → p' ∥₁ q ~̂ L [ lsuc l i ] map' swap (q ∥₂ p')
        comml {⟨ a ⟩} (p' ↑) rf tr = prf p' q (rec (inj₂ (lsuc-retFree rf _ , inj₁ [ ( a , tr) ])))
        comml {⟨ a ⟩} (wait B c) rf tr = ~iwait (λ v → prf (c v) q (rec (inj₂ (lsuc-retFree rf _
                                         , inj₁ (( ι v , ⇒-inp v c) ∷  [(a , tr)])))))
        comml {τ} (p' ↑) retFreeτ tr = prf p' q (rec (inj₁ ≤-refl))
        comml {τ} (wait B c) retFreeτ tr = ~iwait (λ v → prf (c v) q (rec (inj₁ ≤-refl)))
    right _ _ | inj₂ (l' , retFreeτ , r , _ , refl)
                | inj₂ (BSSync {p' = p'} {q' = q'} {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr)
     = let b = prf (q' v2) (p' v1) (rec (inj₂ (refl , inj₁ ( (-, ⇒-inp v2 q') ∷ [ -, tr2 ]))))
       in _ , ∥-stepBoth (BSSync tr2 tr1 (⇄-sym _ _ tr)) , ~isuc b

≲i∥-comm : ∀ {i A B E L} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞)
  → p ∥ q ≲ L [ i ] map swap (q ∥ p)
≲i∥-comm p q = ~i-≲i (~i∥-comm p q)


open ~i-Calculation

~i∥⃗-comm : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (r : CTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] (q ∥⃗ p) ∥⃗ r
~i∥⃗-comm p q r =
  p ∥⃗ q ∥⃗ r
  ~⟨ ~i∥⃗-cong-l (~imap-cong (~i∥-comm p q)) ⟩
  map proj₂ (map swap (q ∥ p)) ∥⃗ r
  ~⟨ ~i∥⃗-cong-l (~imap-∘ (q ∥ p)) ⟩
  map proj₁ (q ∥ p) ∥⃗ r
  ~⟨ ~isym (~i∥⃗-map-l (q ∥ p) r) ⟩
  (q ∥ p) ∥⃗ r
  ~⟨ (~i∥⃗-map-l (q ∥ p) r) ⟩
  q ∥⃗ p ∥⃗ r ∎

≲i∥⃗-comm : ∀ {i A B C E} {{_ : Ord C}} {{_ : Concurrent E}} (p : CTree E A ∞) (q : CTree E B ∞) (r : CTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ≲[ i ] (q ∥⃗ p) ∥⃗ r
≲i∥⃗-comm p q r = ~i-≲i (~i∥⃗-comm p q r)
