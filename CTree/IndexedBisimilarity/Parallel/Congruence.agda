{-# OPTIONS --sized-types --guardedness #-}


module CTree.IndexedBisimilarity.Parallel.Congruence where

open import CTree.IndexedBisimilarity.Parallel.Decomposition
open import CTree.IndexedBisimilarity.Bind
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

------------------------
-- congruence for par --
------------------------


≲i∥-cong-gen : ∀ {i A B E L} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → (∀ {A B} {e1 : E A} {e2 : E B} {p} → (e1 ⇄ e2) [ τ ]=> p → L (MkEff e1))
  → p ≲ L [ i ] p' → q ≲ L [ i ] q' → p ∥ q ≲ L [ i ] p' ∥ q'
≲i∥-cong-gen Lcon  = prf Lcon (<×⇐⁺×⇐⁺-wf _) where

  ≲i-lsuc : ∀ {i E E' A A' L} {{_ : Ord A}} {l : label E' A'} {p q : CTree' E A} → p ≲̂ L [ suc i ] q → p ≲̂ L [ lsuc l i ] q
  ≲i-lsuc b = ≲idown (lsuc≤suc _ _) b

  prf : ∀ {i A B E L} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞} →
    (∀ {A B} {e1 : E A} {e2 : E B} {p} → (e1 ⇄ e2) [ τ ]=> p → L (MkEff e1)) →
    (ac : Acc (×-Lex _≡_ _<_ (×-Lex _≡_ _⇐⁺_ _⇐⁺_)) (i , (p ↑ , q ↑))) → p ≲ L [ i ] p' → q ≲ L [ i ] q'
      → p ∥ q ≲ L [ i ] p' ∥ q'
  prf {zero} _ _ ≲p ≲q = ≲izero
  prf {suc i} {L = L} {p = p} {p'} {q} {q'} Lcon (acc rec) ≲p ≲q = ≲istep left right where
    left : lsafe L ((p ∥ q) ↑) → ∀ {l p''} → (p ∥ q) ↑ [ l ]⇒ p'' → 
      ∃[ l' ] ∃[ q'' ] l ⊑ l' × (p' ∥ q') ↑ [ l' ]⇒ q'' × p'' ≲̂ L [ lsuc l i ] q''
    left ls tr with ∥-step tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with l'' , q'' , leq , tr'' , b ← ≲ileft ≲p (∥-lsafe-l ls) tr'
              rewrite sym (⊑-retFree rf leq)
               with p''' , refl ← ⇒-ε-wait tr' with q''' , refl ← ⇒-ε-wait tr''
                = -, -, ⊑ε _ , ∥-stepLeft (LS rf tr'') ,
                  ≲iwait λ r → prf Lcon (rec _ (inj₂ ( refl , inj₁ ( ( -, ⇒-inp r _) ∷ [ -, tr' ]))))
                    (≲iwait' b r) (≲i-lsuc {l = l'} ≲q)
    ... | inj₁ (inj₁ (LS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with l'' , q'' , ⊑τ , tr'' , b ← ≲ileft ≲p (∥-lsafe-l ls) tr'
        with p''' , refl ← ⇒-τ-↑ tr'  with q''' , refl ← ⇒-τ-↑ tr''
                = _ , _ , ⊑τ , ∥-stepLeft (LS rf tr'') ,
                    prf Lcon (rec _ (inj₁ ≤-refl)) b (≲i-lsuc {l = l'} ≲q)
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with l'' , p'' , leq , tr'' , b ← ≲ileft ≲q (∥-lsafe-r ls) tr'
               rewrite sym (⊑-retFree rf leq)
               with q''' , refl ← ⇒-ε-wait tr' with p''' , refl ← ⇒-ε-wait tr''
                = -, -, ⊑ε _ , ∥-stepRight (RS rf tr'') ,
                  ≲iwait λ r → prf Lcon (rec _ (inj₂ (refl , inj₂ (refl , ( -, ⇒-inp r _) ∷ [ -, tr' ]))))
                    (≲i-lsuc {l = l'} ≲p) (≲iwait' b r) 
    ... | inj₁ (inj₂ (RS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with l'' , p'' , ⊑τ , tr'' , b ← ≲ileft ≲q (∥-lsafe-r ls) tr'
        with q''' , refl ← ⇒-τ-↑ tr' with p''' , refl ← ⇒-τ-↑ tr''
                = _ , _ , ⊑τ , ∥-stepRight (RS rf tr'') ,
                    prf Lcon (rec _ (inj₁ ≤-refl)) (≲i-lsuc {l = l'} ≲p) b
    ... | inj₂ (BSRet tr1 tr2)
      with ⟨ ρ v1 ⟩ , _ , ⊑ρ leq1 , tr1' , b1 ← ≲ileft ≲p (∥-lsafe-l ls) tr1
        | ⟨ ρ v2 ⟩ ,  _ , ⊑ρ leq2 , tr2' , b2 ← ≲ileft ≲q (∥-lsafe-r ls) tr2
        =  _ , _ ,  ⊑ρ (leq1 , leq2) , ∥-stepBoth (BSRet tr1' tr2') , ≲irefl
    ... | inj₂ (BSSync {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr)
      with l1 , _ , ⊑ε _ ,  tr1' , b1 ← ≲ileft ≲p (∥-lsafe-l ls) tr1
               | l2 , _ , ⊑ε _ , tr2' , b2 ← ≲ileft ≲q (∥-lsafe-r ls) tr2
      with _ , refl ← ⇒-ε-wait tr1' | _ , refl ← ⇒-ε-wait tr2'
        = _ , _ , ⊑τ , ∥-stepBoth (BSSync tr1' tr2' tr) , ≲isuc (prf Lcon (rec _ (inj₂ (refl , inj₁ ( ( -, ⇒-inp _ _) ∷ [ -, tr1 ])))) (≲iwait' (b1) v1) (≲iwait' (b2) v2))



    right : lsafe L ((p ∥ q) ↑) → ∀ {l q''} → (p' ∥ q') ↑ [ l ]⇒ q'' → 
      ∃[ l' ] ∃[ p'' ] l' ⊑ l × (p ∥ q) ↑ [ l' ]⇒ p'' × p'' ≲̂ L [ lsuc l i ] q''
    right ls tr with ∥-step tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with l'' , q'' , leq , tr'' , b ← ≲iright ≲p (∥-lsafe-l ls) tr'
              rewrite ⊑-retFree' rf leq
               with p''' , refl ← ⇒-ε-wait tr' with q''' , refl ← ⇒-ε-wait tr''
                = -, -, ⊑ε _ , ∥-stepLeft (LS rf tr'') ,
                  ≲iwait λ r → prf Lcon (rec _ (inj₂ ( refl , inj₁ ( ( -, ⇒-inp r _) ∷ [ -, tr'' ]))))
                    (≲iwait' b r) (≲i-lsuc {l = l'} ≲q)
    ... | inj₁ (inj₁ (LS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₁ (LS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with τ , q'' , ⊑τ , tr'' , b ← ≲iright ≲p (∥-lsafe-l ls) tr'
        with p''' , refl ← ⇒-τ-↑ tr' with q''' , refl ← ⇒-τ-↑ tr''
                = -, -, ⊑τ , ∥-stepLeft (LS rf tr'') ,
                    prf Lcon (rec _ (inj₁ ≤-refl)) b (≲i-lsuc {l = l'} ≲q)
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeε tr'))
              rewrite lsuc-retFree rf i with l'' , p'' , leq , tr'' , b ← ≲iright ≲q (∥-lsafe-r ls) tr'
              rewrite ⊑-retFree' rf leq
               with q''' , refl ← ⇒-ε-wait tr' with p''' , refl ← ⇒-ε-wait tr''
                = -, -, ⊑ε _ , ∥-stepRight (RS rf tr'') ,
                  ≲iwait λ r → prf Lcon (rec _ (inj₂ (refl , inj₂ (refl , ( -, ⇒-inp r _) ∷ [ -, tr'' ]))))
                    (≲i-lsuc {l = l'} ≲p) (≲iwait' b r) 
    ... | inj₁ (inj₂ (RS retFreeι tr')) with () ← ⇒-ι-↑ tr
    ... | inj₁ (inj₂ (RS {l'} rf@retFreeτ tr'))
        rewrite lsuc-retFree rf i with τ , p'' , ⊑τ , tr'' , b ← ≲iright ≲q (∥-lsafe-r ls) tr'
        with q''' , refl ← ⇒-τ-↑ tr' with p''' , refl ← ⇒-τ-↑ tr''
                = -, -, ⊑τ ,  ∥-stepRight (RS rf tr'') ,
                    prf Lcon (rec _ (inj₁ ≤-refl)) (≲i-lsuc {l = l'} ≲p) b
    ... | inj₂ (BSRet tr1 tr2)
      with ⟨ ρ v1 ⟩ , _ , ⊑ρ leq1 , tr1' , b1 ← ≲iright ≲p (∥-lsafe-l ls) tr1
        | ⟨ ρ v2 ⟩ , _ , ⊑ρ leq2 , tr2' , b2 ← ≲iright ≲q (∥-lsafe-r ls) tr2
        =  -, -, ⊑ρ (leq1 , leq2) ,  ∥-stepBoth (BSRet tr1' tr2') , ≲irefl
    ... | inj₂ (BSSync {v1 = v1} {v2 = v2} {e1 = e1} {e2 = e2} tr1 tr2 tr)
      with l1 , _ , ⊑ε _ , tr1' , b1 ← ≲iright ≲p (∥-lsafe-l ls) tr1
         | l2 , _ , ⊑ε _ , tr2' , b2 ← ≲iright ≲q (∥-lsafe-r ls) tr2
           with _ , refl ← ⇒-ε-wait tr1' | _ , refl ← ⇒-ε-wait tr2'
        =  -, -, ⊑τ ,  ∥-stepBoth (BSSync tr1' tr2' tr) ,  ≲isuc (prf Lcon (rec _ (inj₂ (refl , inj₁ ( ( -, ⇒-inp _ _) ∷ [ -, tr1' ])))) (≲iwait' b1 v1) (≲iwait' b2 v2))
           

≲i∥-cong : ∀ {i A B E} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ≲[ i ] p' → q ≲[ i ] q' → p ∥ q ≲[ i ] p' ∥ q'
≲i∥-cong ≲p ≲q = ≲i∥-cong-gen ( λ tr → MkAnyEff)  ≲p ≲q

~i∥-cong : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥ q ~[ i ] p' ∥ q'
~i∥-cong ~p ~q = ≲i-weaken {{_}} {{≡-Ord}} (λ { (refl , refl) → refl}) (≲i∥-cong {{≡-Ord}} {{≡-Ord}} ~p ~q)


------------------------------------
-- Corresponding properties for ∥⃗ --
------------------------------------

≲i∥⃗-cong : ∀ {i A B E} {{_ : Ord A}}  {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ≲[ i ] p' → q ≲[ i ] q' → p ∥⃗ q ≲[ i ] p' ∥⃗ q'
≲i∥⃗-cong ≲p ≲q = ≲imap-cong (≲i∥-cong ≲p ≲q) λ leq → proj₂ leq

~i∥⃗-cong : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q q' : CTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥⃗ q ~[ i ] p' ∥⃗ q'
~i∥⃗-cong ~p ~q = ~imap-cong (~i∥-cong ~p ~q)

≲i∥⃗-cong-l : ∀ {i A B E} {{_ : Ord A}}  {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q : CTree E B ∞}
  → p ≲[ i ] p' → p ∥⃗ q ≲[ i ] p' ∥⃗  q
≲i∥⃗-cong-l b = ≲i∥⃗-cong b ≲irefl

~i∥⃗-cong-l : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree E A ∞}{q : CTree E B ∞}
  → p ~[ i ] p' → p ∥⃗ q ~[ i ] p' ∥⃗  q
~i∥⃗-cong-l b = ~i∥⃗-cong b ~irefl


≲i∥⃗-cong-r : ∀ {i A B E} {{_ : Ord B}} {{_ : Concurrent E}} {p : CTree E A ∞}{q q' : CTree E B ∞}
  → q ≲[ i ] q' → p ∥⃗ q ≲[ i ] p ∥⃗ q'
≲i∥⃗-cong-r b = ≲i∥⃗-cong {{≡-Ord}} ~irefl b


~i∥⃗-cong-r : ∀ {i A B E} {{_ : Concurrent E}} {p : CTree E A ∞}{q q' : CTree E B ∞}
  → q ~[ i ] q' → p ∥⃗ q ~[ i ] p ∥⃗ q'
~i∥⃗-cong-r b = ~i∥⃗-cong ~irefl b
