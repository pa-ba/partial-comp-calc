{-# OPTIONS --sized-types #-}


-----------------------------------------------------
-- basic properties of indexed strong bisimilarity --
-----------------------------------------------------


module CTree.IndexedBisimilarity.BasicProperties where

open import CTree.IndexedBisimilarity.Definitions public

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product.Relation.Binary.Lex.Strict
open import Relation.Binary.Construct.Closure.Transitive hiding (map)
open import Data.Empty

-- helper function for well-founded recursion
recStep : ∀ {E A l i} {p p' : CTree' E A} → p [ l ]⇒ p' →
  suc (lsuc l i) ≤ suc i ⊎ lsuc l i ≡ suc i × ∃[ a ] p [ ⟨ a ⟩ ]⇒ p'
recStep {l = ⟨ x ⟩} tr = inj₂ (refl , x , tr)
recStep {l = τ} tr = inj₁ ≤-refl


⊑-lsuc : ∀ {E A} {{_ : Ord A}} {l l' : label E A} → l ⊑ l' → (i : ℕ) → lsuc l i ≡ lsuc l' i
⊑-lsuc ⊑τ _ = refl
⊑-lsuc (⊑ε e) _ = refl
⊑-lsuc (⊑ι r) _ = refl
⊑-lsuc (⊑ρ x) _ = refl


recStep⊑ : ∀ {E A l l' i} {{_ : Ord A}} {p p' : CTree' E A} → l ⊑ l' → p [ l ]⇒ p' →
  suc (lsuc l' i) ≤ suc i ⊎ lsuc l' i ≡ suc i × ∃[ a ] p [ ⟨ a ⟩ ]⇒ p'
recStep⊑ {i = i} leq tr with recStep {i = i} tr
... | res rewrite ⊑-lsuc leq i = res

-- helper function for well-founded recursion
recStep⁺ : ∀ {E A l i} {p p' : CTree' E A} →  p [ l ]⇒ p' →
  suc (lsuc l i) ≤ suc i ⊎ lsuc l i ≡ suc i × TransClosure (λ q q' → ∃[ a ] q' [ ⟨ a ⟩ ]⇒ q) p' p
recStep⁺ {l = ⟨ x ⟩} tr = inj₂ (refl , [  (x , tr) ] )
recStep⁺ {l = τ} tr = inj₁ ≤-refl

-- helper function for well-founded recursion
recStep⊑⁺ : ∀ {E A l l' i} {{_ : Ord A}} {p p' : CTree' E A} →  l ⊑ l' → p [ l ]⇒ p' →
  suc (lsuc l' i) ≤ suc i ⊎ lsuc l' i ≡ suc i × TransClosure (λ q q' → ∃[ a ] q' [ ⟨ a ⟩ ]⇒ q) p' p
recStep⊑⁺ {i = i} leq tr with recStep⁺ {i = i} tr
... | res rewrite ⊑-lsuc leq i = res




---------------------------------------------------
-- basic properties of indexed strong bisimilarity 
---------------------------------------------------

⊑lab-monotone : ∀ {E A} {{O : Ord A}} {{O' : Ord A}} {l l' : label E A} →
  (∀ {x y} →  _⊑_ {{O}} x y → _⊑_ {{O'}} x y) →  _⊑lab_ {{O}} l l' → _⊑lab_ {{O'}} l l'
⊑lab-monotone mon ⊑τ = ⊑τ
⊑lab-monotone mon (⊑ε e) = ⊑ε e
⊑lab-monotone mon (⊑ι r) = ⊑ι r
⊑lab-monotone mon (⊑ρ leq) = ⊑ρ (mon leq)

≲i-weaken : ∀ {E L A i } {{O : Ord A}} {{O' : Ord A}} {p q : CTree' E A} →
         (∀ {x y} →  _⊑_ {{O}} x y → _⊑_ {{O'}} x y) → _≲̂_[_]_ {{O}} p L i q → _≲̂_[_]_ {{O'}} p L i q
≲i-weaken {E = E} {L} {A} {{O}} {{O'}} mon eq = prf (<×⇐-wf _) eq
  where prf : ∀ {i} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → _≲̂_[_]_ {{O}} p L i q → _≲̂_[_]_ {{O'}} p L i q
        prf {zero} _ _ = ≲izero
        prf {suc i}  {p = p} {q} (acc rec) b = ≲istep left right where
          left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p'
            → ∃[ l' ] ∃[ q' ] (_⊑_ {{LabOrd {{O'}}}} l l' × q [ l' ]⇒ q' × _≲̂_[_]_ {{O'}} p' L (lsuc l i) q')
          left ls tr with ≲ileft {{O}} b ls tr
          ... | l' , q' , leq , tr' , b' = l' , q' , ⊑lab-monotone {{O}} {{O'}} mon leq , tr' , prf (rec (recStep tr)) b'

          right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q'
            → ∃[ l' ] ∃[ p' ] (_⊑_ {{LabOrd {{O'}}}} l' l × p [ l' ]⇒ p' × _≲̂_[_]_ {{O'}} p' L (lsuc l i) q')
          right ls tr with ≲iright {{O}} b ls tr
          ... | l' , p' , leq , tr' , b' =
            l' , p' , ⊑lab-monotone {{O}} {{O'}} mon leq , tr' , prf (rec (recStep⊑ {{O'}} (⊑lab-monotone {{O}} {{O'}} mon leq) tr')) b'



~i-≲i : ∀ {E L A i } {{_ : Ord A}} {p q : CTree' E A} → p ~̂ L [ i ] q → p ≲̂ L [ i ] q
~i-≲i {{O}} = ≲i-weaken {{≡-Ord}} {{O}} λ {refl → ⊑-refl {{O}}}


~irefl : ∀ {i E A L} {p : CTree' E A} → p ~̂ L [ i ] p
~irefl = prf (<×⇐-wf _)
  where prf : ∀ {i E A L} {p : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ~̂ L [ i ] p
        prf {zero} _ = ~izero
        prf {suc i} (acc rec) =
          ~istep
            (λ _ trans → _ , trans , prf (rec (recStep trans)))
            (λ _ trans → _ , trans , prf (rec (recStep trans)))

~i≡ : ∀ {i E A L} {p q : CTree E A ∞} → p ≡ q → p ~ L [ i ] q
~i≡ refl = ~irefl

≲irefl : ∀ {i E A L} {{_ : Ord A}} {p : CTree' E A} → p ≲̂ L [ i ] p
≲irefl = ~i-≲i ~irefl

≲i⊑ : ∀ {i E A L} {{_ : Ord A}} {v w : A} → v ⊑ w → return {E = E} v ≲ L [ i ] return w
≲i⊑ {zero} _ = ≲izero
≲i⊑ {suc i} leq = ≲istep
            (λ {_ (⇒-now _) → _ , _ , ⊑ρ leq , ⇒-now _ , ≲irefl})
            (λ {_ (⇒-now _) → _ , _ , ⊑ρ leq , ⇒-now _ , ≲irefl})
                
~isym : ∀ {i E A} {p q : CTree' E A} → p ~̂[ i ] q → q ~̂[ i ] p
~isym = prf (<×⇐-wf _)
  where prf : ∀ {i E A} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ~̂[ i ] q → q ~̂[ i ] p
        prf _ ≲izero = ≲izero
        prf {i = suc i}  {p = p} {q} (acc rec) b = ≲istep' {{≡-Ord}} left right
          where left : ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l ⊑≡ l' × p [ l' ]⇒ p' × q' ~̂[ lsuc l i ] p')
                left trans with ≲iright {{≡-Ord}} b AnyEff-lsafe trans
                ... | l' , q' , leq , trans' , ibi' rewrite ⊑≡-≡ leq =
                  _ , q' , ⊑≡-refl , trans' , prf (rec (recStep trans')) ibi' 
                right : ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l' ⊑≡ l × q [ l' ]⇒ q' × q' ~̂[ lsuc l i ] p')
                right trans with ≲ileft {{≡-Ord}} b AnyEff-lsafe trans
                ... | (l' , q' , leq , trans' , ibi') rewrite ⊑≡-≡ leq =
                  _ , q' , ⊑≡-refl , trans' , prf (rec (recStep trans)) ibi'


≲itrans : ∀ {i E A L} {{_ : Ord A}} {p q r : CTree' E A} → p ≲̂ L [ i ] q → q ≲̂ L [ i ] r → p ≲̂ L [ i ] r
≲itrans b1 b2 = prf (<×⇐-wf _) b1 b2
  where prf : ∀ {i E A L} {{O : Ord A}} {p q r : CTree' E A}
            → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ≲̂ L [ i ] q → q ≲̂ L [ i ] r → p ≲̂ L [ i ] r
        prf _ ≲izero ≲izero = ≲izero
        prf {i = suc i} {L = L} {{O}} {p = p} {q} {r} (acc rec) b1 b2 = ≲istep left right
            where left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ r' ] (l ⊑ l' × r [ l' ]⇒ r' × p' ≲̂ L [ lsuc l i ] r')
                  left ls trans1 with ≲ileft b1 ls trans1
                  ... | (l' , q' , leq , trans2 , b1') with ≲ileft b2 (lsafe-≲i ls b1) trans2
                  ... | (l'' , r' , leq' , trans3 , b2') rewrite ⊑-lsuc leq i = 
                    (l'' , r' , ⊑-trans {{LabOrd {{O}}}} leq leq' , trans3 , prf (rec (recStep⊑ leq trans1 ))  b1'  b2')

                  right : lsafe L p → ∀ {l r'} → r [ l ]⇒ r' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] r')
                  right ls trans3 with ≲iright b2 (lsafe-≲i ls b1) trans3
                  ... | (l' , q' , leq , trans2 , b2') with ≲iright b1 ls trans2
                  ... | l'' , p' , leq' , trans1 , b1' rewrite ⊑-lsuc leq i = 
                    l'' , p' , ⊑-trans {{LabOrd {{O}}}} leq' leq  , trans1 , prf (rec (recStep⊑ (⊑-trans {{LabOrd {{O}}}} leq' leq) trans1))  b1' b2'

~itrans : ∀ {i E A L} {p q r : CTree' E A} → p ~̂ L [ i ] q → q ~̂ L [ i ] r → p ~̂ L [ i ] r
~itrans = ≲itrans {{≡-Ord}}

≲ilater : ∀ {i E A L} {{_ : Ord A}} {a b : ∞CTree E A ∞} → force a ≲ L [ i ] force b → later a ≲ L [ suc i ] later b
≲ilater b = ≲istep (λ {_ ⇒-later → _ , _ , ⊑τ , ⇒-later , b }) λ {_ ⇒-later →  _ , _ , ⊑τ , ⇒-later , b }

~ilater : ∀ {i E A L} {a b : ∞CTree E A ∞} → force a ~ L [ i ] force b → later a ~ L [ suc i ] later b
~ilater = ≲ilater {{≡-Ord}}

≲idown : ∀ {E A L i j} {{_ : Ord A}} {a b : CTree' E A} → j ≤ i → a ≲̂ L [ i ] b → a ≲̂ L [ j ] b
≲idown = prf (<×⇐-wf _)
  where prf : ∀ {E A L i j} {{_ : Ord A}} {p q : CTree' E A}
            → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → j ≤ i → p ≲̂ L [ i ] q → p ≲̂ L [ j ] q
        prf _ z≤n b = ≲izero
        prf {L = L} {j = suc j} {p = p} {q} (acc rec) (s≤s {_} {n} le) b = ≲istep left right
          where left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂ L [ lsuc l j ] q')
                left ls {l} trans with ≲ileft b ls trans
                ... | l' , q' , leq , trans' , b' = l' , q' , leq , trans' , prf (rec (recStep trans)) (lsuc-mono l le) b'
                right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l j ] q')
                right ls {l} trans with ≲iright b ls trans 
                ... | l' , p' , leq , trans' , b' with le' ← lsuc-mono l le rewrite sym (⊑-lsuc leq n)
                  = l' , p' , leq , trans' , prf (rec (recStep trans')) le' b'

~idown : ∀ {E A L i j} {a b : CTree' E A} → j ≤ i → a ~̂ L [ i ] b → a ~̂ L [ j ] b
~idown = ≲idown {{≡-Ord}}

≲isuc : ∀ {E A L i} {{_ : Ord A}} {a b : CTree' E A} → a ≲̂ L [ suc i ] b → a ≲̂ L [ i ] b
≲isuc e = ≲idown (n≤1+n _) e

~isuc : ∀ {E A L i} {a b : CTree' E A} → a ~̂ L [ suc i ] b → a ~̂ L [ i ] b
~isuc = ≲isuc {{≡-Ord}}

≲ilsuc : ∀ {E A L i} {{_ : Ord A}} {l : label E A} {a b : CTree' E A} → a ≲̂ L [ lsuc l i ] b → a ≲̂ L [ i ] b
≲ilsuc {l = ⟨ x ⟩} e = ≲idown (n≤1+n _) e
≲ilsuc {l = τ} e = e

≲iwait : ∀{E A B L i} {{_ : Ord A}} {c d : B → CTree E A ∞} → (∀ x → c x ≲ L [ i ] d x)
  → wait B c ≲̂ L [ i ] wait B d
≲iwait {i = zero} bs = ≲izero
≲iwait {L = L} {i = suc i} {c} {d} bs = ≲istep left right
  where left : lsafe L (wait _ c) → ∀ {l p'} → wait _ c [ l ]⇒ p'
             → ∃[ l' ] ∃[ q' ] (l ⊑ l' × wait _ d [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')
        left ls (⇒-inp r c) = _ , d r ↑  , ⊑ι r ,  ⇒-inp r d , bs r
        right : lsafe L (wait _ c) → ∀ {l q'} → wait _ d [ l ]⇒ q'
          → ∃[ l' ] ∃[ p' ] (l' ⊑ l × wait _ c [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q')
        right ls (⇒-inp r d) = _ , c r ↑ , ⊑ι r , ⇒-inp r c , bs r

~iwait : ∀{E A B L i} {c d : B → CTree E A ∞} → (∀ x → c x ~ L [ i ] d x)
  → wait B c ~̂ L [ i ] wait B d
~iwait = ≲iwait {{≡-Ord}}

≲iwait' : ∀ {i E A B L } {{_ : Ord A}}  {c d : B → CTree E A ∞}  → wait B c ≲̂ L [ i ] wait B d →
           (∀ r → c r ≲ L [ i ] d r)
≲iwait' {zero} b r = ≲izero
≲iwait' {suc i} {c = c} {d} b r
  with _ , q' , ⊑ι _ , (⇒-inp r d) , b' ← ≲ileft b wait-lsafe (⇒-inp r c) = b'


~iwait' : ∀ {i E A B L }  {c d : B → CTree E A ∞}  → wait B c ~̂ L [ i ] wait B d →
           (∀ r → c r ~ L [ i ] d r)
~iwait' = ≲iwait' {{≡-Ord}}

≲ieff : ∀{E A B L i} {{_ : Ord A}} {c d : B → CTree E A ∞} (e : E B) → (∀ x → c x ≲ L [ i ] d x) → eff e c ≲ L [ i ] eff e d
≲ieff {i = zero} e bs = ≲izero
≲ieff {L = L} {i = suc i} {c} {d} e bs = ≲istep left right
  where left : lsafe L (eff e c ↑) → ∀ {l p'} → eff e c ↑ [ l ]⇒ p'
             → ∃[ l' ] ∃[ q' ] (l ⊑ l' × eff e d ↑ [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')
        left ls (⇒-eff e c)  = _ , wait _ d , ⊑ε e , ⇒-eff e d ,  ≲iwait bs
        right : lsafe L (eff e c ↑) → ∀ {l q'} → eff e d ↑ [ l ]⇒ q'
          → ∃[ l' ] ∃[ p' ] (l' ⊑ l × eff e c ↑ [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q')
        right ls (⇒-eff e d) = _ , wait _ c , ⊑ε e , ⇒-eff e c , ≲iwait bs

~ieff : ∀{E A B L i} {c d : B → CTree E A ∞} (e : E B) → (∀ x → c x ~ L [ i ] d x) → eff e c ~ L [ i ] eff e d
~ieff = ≲ieff {{≡-Ord}}

≲i⊕-cong : ∀ {E A L i} {{_ : Ord A}} {p1 q1 p2 q2 : CTree E A ∞} → p1 ≲ L [ i ] p2 → q1 ≲ L [ i ] q2
  → p1 ⊕ q1 ≲ L [ i ] p2 ⊕ q2
≲i⊕-cong {i = zero} ≲p ≲q = ≲izero
≲i⊕-cong {L = L} {i = suc i} {p1} {q1} {p2} {q2} ≲p ≲q = ≲istep left right where
  left : lsafe L ((p1 ⊕ q1) ↑) → ∀ {l p'} → (p1 ⊕ q1) ↑ [ l ]⇒ p'
    → ∃[ l' ] ∃[ q' ] l ⊑ l' × (p2 ⊕ q2) ↑ [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q'
  left ls (⇒-⊕-l tr) with l' , q' , leq , tr' , b' ← ≲ileft ≲p (⊕-lsafe-l ls) tr = l' , q' , leq , ⇒-⊕-l tr' , b'
  left ls (⇒-⊕-r tr) with l' , q' , leq , tr' , b' ← ≲ileft ≲q (⊕-lsafe-r ls) tr = l' , q' , leq , ⇒-⊕-r tr' , b'
  right : lsafe L ((p1 ⊕ q1) ↑) → ∀ {l q'} → (p2 ⊕ q2)↑ [ l ]⇒ q'
    → ∃[ l' ] ∃[ p' ] l' ⊑ l × (p1 ⊕ q1)↑ [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q'
  right ls (⇒-⊕-l tr) with l' , q' , leq , tr' , b' ← ≲iright ≲p (⊕-lsafe-l ls) tr = l' , q' , leq , ⇒-⊕-l tr' , b'
  right ls (⇒-⊕-r tr) with l' , q' , leq , tr' , b' ← ≲iright ≲q (⊕-lsafe-r ls) tr = l' , q' , leq , ⇒-⊕-r tr' , b'

~i⊕-cong : ∀ {E A L i} {p1 q1 p2 q2 : CTree E A ∞} → p1 ~ L [ i ] p2 → q1 ~ L [ i ] q2
  → p1 ⊕ q1 ~ L [ i ] p2 ⊕ q2
~i⊕-cong = ≲i⊕-cong {{≡-Ord}}

≲i⊕-cong-r : ∀ {E A L i} {{_ : Ord A}} {p q q' : CTree E A ∞} → q ≲ L [ i ] q' → p ⊕ q ≲ L [ i ] p ⊕ q'
≲i⊕-cong-r ≲q = ≲i⊕-cong ≲irefl ≲q

~i⊕-cong-r : ∀ {E A L i} {p q q' : CTree E A ∞} → q ~ L [ i ] q' → p ⊕ q ~ L [ i ] p ⊕ q'
~i⊕-cong-r = ≲i⊕-cong-r {{≡-Ord}}


≲i⊕-cong-l : ∀ {E A L i} {{_ : Ord A}} {p q p' : CTree E A ∞} → p ≲ L [ i ] p' → p ⊕ q ≲ L [ i ] p' ⊕ q
≲i⊕-cong-l ≲p =  ≲i⊕-cong ≲p ≲irefl

~i⊕-cong-l : ∀ {E A L i} {p q p' : CTree E A ∞} → p ~ L [ i ] p' → p ⊕ q ~ L [ i ] p' ⊕ q
~i⊕-cong-l = ≲i⊕-cong-l {{≡-Ord}}

≲ilift : ∀ {E L A i } {{_ : Ord A}} {p q : CTree E A ∞} → p ≲[ i ] q → p ≲ L [ i ] q
≲ilift {E = E} {L} eq = prf (<×⇐-wf _) eq
  where prf : ∀ {i A} {{_ : Ord A}} {p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ≲̂[ i ] q → p ≲̂ L [ i ] q
        prf {zero} _ _ = ≲izero
        prf {suc i}  {p = p} {q} (acc rec) b = ≲istep left right where
          left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p'
            → ∃[ l' ] ∃[ q' ] (l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂ L [ lsuc l i ] q')
          left ls tr with ≲ileft b AnyEff-lsafe tr
          ... | l' , q' , leq , tr' , b' =  l' , q' , leq , tr' , prf (rec (recStep tr)) b'
          right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q'
            → ∃[ l' ] ∃[ p' ] (l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂ L [ lsuc l i ] q')
          right ls tr with ≲iright b AnyEff-lsafe tr
          ... | l' , p' , leq , tr' , b' =  l' , p' , leq , tr' , prf (rec (recStep⊑ leq tr')) b'

~ilift : ∀ {E L A i } {p q : CTree E A ∞} → p ~[ i ] q → p ~ L [ i ] q
~ilift = ≲ilift {{≡-Ord}}


≲i-~i : ∀ {E L A i } {{_ : Ord A}} {p q : CTree E A ∞} → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ≲ L [ i ] q → p ~ L [ i ] q
≲i-~i {E = E} {L} {A} ⊑to≡ eq = prf (<×⇐-wf _) eq
  where prf : ∀ {i}{p q : CTree' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p) → p ≲̂ L [ i ] q → p ~̂ L [ i ] q
        prf {zero} _ _ = ≲izero
        prf {suc i}  {p = p} {q} (acc rec) b = ~istep left right where
          left : lsafe L p → ∀ {l p'} → p [ l ]⇒ p'
            → ∃[ q' ] (q [ l ]⇒ q' × p' ~̂ L [ lsuc l i ] q')
          left ls tr with ≲ileft b ls tr
          ... | l' , q' , leq , tr' , b' rewrite ⊑-≡ ⊑to≡ leq =  q' , tr' , prf (rec (recStep tr)) b'
          right : lsafe L p → ∀ {l q'} → q [ l ]⇒ q'
            → ∃[ p' ] (p [ l ]⇒ p' × p' ~̂ L [ lsuc l i ] q')
          right ls tr with ≲iright b ls tr
          ... | l' , p' , leq , tr' , b' rewrite ⊑-≡ ⊑to≡ leq =  p' , tr' , prf (rec (recStep tr')) b'


module ≲i-Calculation where
  infix  3 _∎
  infixr 1 _≲⟨_⟩_
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_

  _≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree E A ∞) →
    ∀ {y : CTree E A ∞} {z : CTree E A ∞} → x ≲[ i ] y → y ≲[ i ] z → x ≲[ i ] z
  _≲⟨_⟩_ {_} x r eq =  ≲itrans r eq

  _~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree E A ∞) →
    ∀ {y : CTree E A ∞} {z : CTree E A ∞} → x ~[ i ] y → y ≲[ i ] z → x ≲[ i ] z
  _~⟨_⟩_ {_} x r eq =  ≲itrans (~i-≲i r) eq

  _≡⟨⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree E A ∞) → ∀ {y : CTree E A ∞} → x ≲[ i ] y → x ≲[ i ] y
  _≡⟨⟩_  x eq = eq

  _∎ : ∀ {E A i} {{_ : Ord A}} (x : CTree E A ∞) → x ≲[ i ] x
  _∎  x = ≲irefl



module ~i-Calculation where
  infix  3 _∎
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_

  _~⟨_⟩_ : ∀ {E A i} (x : CTree E A ∞) →
    ∀ {y : CTree E A ∞} {z : CTree E A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
  _~⟨_⟩_ {_} x r eq =  ~itrans r eq

  _≡⟨⟩_ : ∀ {E A i} (x : CTree E A ∞) → ∀ {y : CTree E A ∞} → x ~[ i ] y → x ~[ i ] y
  _≡⟨⟩_  x eq = eq

  _∎ : ∀ {E A i} (x : CTree E A ∞) → x ~[ i ] x
  _∎  x = ~irefl
