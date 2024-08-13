{-# OPTIONS --sized-types --guardedness #-}


-- Properties for the effect handler function `interpSt`.

module CTree.IndexedBisimilarity.Interp where

open import Size

open import CTree.Definitions public
open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.Bind
open import CTree.IndexedBisimilarity.MonadLaws
open import Data.Nat
open import Data.Unit
open import Data.Bool hiding (_<_)
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_ ; map)
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Function using (id; _∘_)
open import Relation.Binary.Construct.Closure.Transitive hiding (map)

-- Proof of the congruence property for `interpSt`

module InterpStep where
  data effFree {E F : Set → Set} {A : Set} : label E A → label F A → Set where
    effFreeρ : ∀ {v} → effFree ⟨ ρ v ⟩ ⟨ ρ v ⟩
    effFreeι : ∀ {B} {r : B} → effFree ⟨ ι r ⟩ ⟨ ι r ⟩
    effFreeτ : effFree τ τ

  interpSt' : ∀ {E F A S} → S → (∀ {B} → S → E B → CTree F (B × S) ∞) → CTree' E A → CTree' F A
  interpSt' st f (p ↑) = interpSt st f p ↑
  interpSt' st f (wait B c) = wait B λ r → interpSt st f (c r)
  
  interpSt-step : ∀ {E F A S} {l : label F A} {p : CTree' E A} {q : CTree' F A} {st : S}
    {f : ∀ {B} → S → E B → CTree F (B × S) ∞} → interpSt' st f p [ l ]⇒ q
      → (∃[ p' ] ∃[ l' ] effFree l l' ×  p [ l' ]⇒ p' × interpSt' st f p' ≡ q)
        ⊎ (∃[ B ] Σ[ e ∈ E B ] ∃[ c ] p [ ⟨ ε e ⟩ ]⇒ wait B c
          × (f st e >>= (λ (x , s') → interpSt s' f (c x))) ↑ [ l ]⇒ q)
  interpSt-step {p = now v ↑} (⇒-now .v) = inj₁ (-, (-, (effFreeρ ,  ⇒-now v , refl)))
  interpSt-step {p = later p ↑} ⇒-later = inj₁ (-, (-, (effFreeτ , ⇒-later , refl)))
  interpSt-step {p = (p1 ⊕ p2) ↑} (⇒-⊕-l tr) with interpSt-step {p = p1 ↑} tr
  ... | inj₁ (p' , l' , ef , tr' , eq) = inj₁ (p' , l' , ef , (⇒-⊕-l tr') , eq)
  ... | inj₂ (B , e , c , tr1 , tr2) = inj₂ (B , e , c , ⇒-⊕-l tr1 , tr2)
  interpSt-step {p = (p1 ⊕ p2) ↑} (⇒-⊕-r tr) with interpSt-step {p = p2 ↑} tr
  ... | inj₁ (p' , l' , ef , tr' , eq) = inj₁ (p' , l' , ef , (⇒-⊕-r tr') , eq)
  ... | inj₂ (B , e , c , tr1 , tr2) = inj₂ (B , e , c , ⇒-⊕-r tr1 , tr2)
  interpSt-step {p = eff e c ↑} tr = inj₂ (_ , e , c , ⇒-eff e c , tr)
  interpSt-step {p = wait B c} (⇒-inp r _) = inj₁ (-, (-, effFreeι , (⇒-inp r c) , refl))

  interpSt-eff : ∀ {E F A B S c} {e : E B} {p : CTree' E A} {q : CTree' F A} {st : S}
    {f : ∀ {B} → S → E B → CTree F (B × S) ∞} {l : label F A}  → 
    p [ ⟨ ε e ⟩ ]⇒ wait B c → (f st e >>= (λ (x , s') → interpSt s' f (c x))) ↑ [ l ]⇒ q
      → interpSt' st f p [ l ]⇒ q
  interpSt-eff (⇒-eff e c) tr2 = tr2
  interpSt-eff (⇒-⊕-l tr1) tr2 = ⇒-⊕-l (interpSt-eff tr1 tr2)
  interpSt-eff (⇒-⊕-r tr1) tr2 = ⇒-⊕-r (interpSt-eff tr1 tr2)


  interpSt-effFree : ∀ {E F A S p' l'} → {l : label F A} {p : CTree' E A} {st : S}
                   {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
                   → effFree l l' →  p [ l' ]⇒ p' →
                   interpSt' st f p [ l ]⇒ interpSt' st f p'
  interpSt-effFree effFreeρ (⇒-now v) = ⇒-now v
  interpSt-effFree ef (⇒-⊕-l tr) = ⇒-⊕-l (interpSt-effFree ef tr)
  interpSt-effFree ef (⇒-⊕-r tr) = ⇒-⊕-r (interpSt-effFree ef tr)
  interpSt-effFree effFreeτ ⇒-later = ⇒-later
  interpSt-effFree effFreeι (⇒-inp r _) = ⇒-inp r _

  effFree-lsuc : ∀ {E F A i} {l : label E A} {l' : label F A} → effFree l l' → lsuc l i ≡ lsuc l' i
  effFree-lsuc effFreeρ = refl
  effFree-lsuc effFreeι = refl
  effFree-lsuc effFreeτ = refl

  ⊑-effFree : ∀ {E F A } {{_ : Ord A}}  {le  : label E A} {lf lf' : label F A} → lf ⊑ lf' → effFree le lf →
    ∃[ le' ]   le ⊑ le' × effFree le' lf'
  ⊑-effFree (⊑ρ leq) effFreeρ = -, ⊑ρ leq , effFreeρ
  ⊑-effFree (⊑ι r) effFreeι = -, ⊑ι r , effFreeι
  ⊑-effFree ⊑τ effFreeτ = -, ⊑τ , effFreeτ


  ⊑-effFree' : ∀ {E F A } {{_ : Ord A}}  {le' : label E A} {lf lf' : label F A} → lf ⊑ lf' → effFree le' lf' →
    ∃[ le ] le ⊑ le' × effFree le lf
  ⊑-effFree' ⊑τ effFreeτ = τ , ⊑τ , effFreeτ
  ⊑-effFree' (⊑ι r) effFreeι = _ , ⊑ι _ , effFreeι
  ⊑-effFree' (⊑ρ leq) effFreeρ = -, ⊑ρ leq , effFreeρ

  interpSt-cong' : ∀ {i E F A S} {{_ : Ord A}} {p q : CTree' E A} {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
    → p ≲̂[ i ] q → interpSt' st f p ≲̂[ i ] interpSt' st f q
  interpSt-cong' = prf (<×⇐⁺-wf _) where
    prf : ∀ {i E F A S} {{_ : Ord A}} {p q : CTree' E A} {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
      (ac : Acc (×-Lex _≡_ _<_ _⇐⁺_) (i , p)) → p ≲̂[ i ] q → interpSt' st f p ≲̂[ i ] interpSt' st f q
    prf {zero} _ bi = ≲izero
    prf {suc i} {p = p} {q} {st} {f} (acc rec) bi = ≲istep' left right where
      left : ∀ {l fp'} → interpSt' st f p [ l ]⇒ fp' → 
        ∃[ l' ] ∃[ fq' ] l ⊑ l' × interpSt' st f q [ l' ]⇒ fq' × fp' ≲̂[ lsuc l i ] fq'
      left tr with interpSt-step {p = p} tr
      ... | inj₁ (p' , l' , ef , tr' , refl) rewrite effFree-lsuc {i = i} ef with ≲ileft' bi tr'
      ... | l' , q' , leq , tr'' , bi' with (⊑-effFree leq ef)
      ... | l'' , leq' , ef' =
        _ , _ , leq' , interpSt-effFree ef' tr'' , prf (rec _ (recStep⁺ tr')) bi'
      left tr | inj₂ (B , e , c , tr1 , tr2)
        with l' , wc' , ⊑ε _ , tr1' , bi1 ← ≲ileft' bi tr1 with c' , refl ← ⇒-ε-wait tr1'
        with l'' , fq' , leq , tr2' , bi2 ← ≲ileft' (≲i>>=-cong-r (f st e)  (λ (x , s') →
             prf (rec _ (inj₂ (refl , (-, ⇒-inp x c) ∷ [ -, tr1 ] ))) (≲iwait' bi1 x))) tr2
             = -, -, leq , interpSt-eff tr1' tr2' , bi2
      right : ∀ {l fq'} → interpSt' st f q [ l ]⇒ fq' → 
        ∃[ l' ] ∃[ fp' ] l' ⊑ l × interpSt' st f p [ l' ]⇒ fp' × fp' ≲̂[ lsuc l i ] fq'
      right tr with interpSt-step {p = q} tr
      ... | inj₁ (p' , l' , ef , tr' , refl) rewrite effFree-lsuc {i = i} ef with ≲iright' bi tr'
      ... | l' , q' , leq , tr'' , bi' with (⊑-effFree' leq ef)
      ... | l'' , leq' , ef' = -, -, leq' , interpSt-effFree ef' tr'' , prf (rec _ (recStep⊑⁺ leq tr'')) bi'
      right tr | inj₂ (B , e , c , tr1 , tr2)
        with l' , wc , ⊑ε _ , tr1' , bi1 ← ≲iright' bi tr1 with c , refl ← ⇒-ε-wait tr1'
        with l'' , fp' , leq , tr2' , bi2 ← ≲iright' (≲i>>=-cong-r (f st e)  (λ (x , s') →
             prf (rec _ (inj₂ (refl , (-, ⇒-inp x c) ∷ [ -, tr1' ] ))) (≲iwait' bi1 x))) tr2
             = -, -, leq , interpSt-eff tr1' tr2' , bi2



open InterpStep

≲iinterpSt-cong : ∀ {i E F A S} {{_ : Ord A}} {p q : CTree E A ∞} {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
  → p ≲[ i ] q → interpSt st f p ≲[ i ] interpSt st f q
≲iinterpSt-cong = interpSt-cong'

≲iinterpSt-map : ∀ {i E F A B S} {{_ : Ord B}} (p : CTree E A ∞) {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
  (g : A → B) → map g (interpSt st f p) ≲[ i ] interpSt st f (map g p)
≲iinterpSt-map {0} _ _ = ≲izero
≲iinterpSt-map (now v) g = ≲irefl
≲iinterpSt-map {suc i} (later p) g = ≲ilater (≲iinterpSt-map {i} (force p) g)
≲iinterpSt-map (p ⊕ q) g = ≲i⊕-cong (≲iinterpSt-map p g) (≲iinterpSt-map q g)
≲iinterpSt-map ∅ g = ≲irefl
≲iinterpSt-map (eff e c) {st} {f} g =
  ≲itrans (≲i>>=-assoc (f st e)) (≲i>>=-cong-r (f st e) (λ x → ≲iinterpSt-map (c _) g)) 


~iinterpSt-cong : ∀ {i E F A S} {p q : CTree E A ∞} {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
  → p ~[ i ] q → interpSt st f p ~[ i ] interpSt st f q
~iinterpSt-cong = ≲iinterpSt-cong {{≡-Ord}}

~iinterpSt-map : ∀ {i E F A B S} (p : CTree E A ∞) {st : S} {f : ∀ {B} → S → E B → CTree F (B × S) ∞}
  (g : A → B) → map g (interpSt st f p) ~[ i ] interpSt st f (map g p)
~iinterpSt-map = ≲iinterpSt-map {{≡-Ord}}
