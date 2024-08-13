{-# OPTIONS --sized-types #-}

-- Properties for the monadic bind operator >>=

module CTree.IndexedBisimilarity.Bind where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.MonadLaws public
open import CTree.Parallel public
open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Product renaming (map to map×)
open import Induction.WellFounded
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Product.Relation.Binary.Lex.Strict
open import Function using (id; _∘_)
open import Relation.Nullary
------------------------
-- congruence for >>= --
------------------------


≲i>>=-cong-r : ∀ {i E A B L} {{_ : Ord B}} (a : CTree E A ∞)
            {k l : A → CTree E B ∞} (h : ∀ a → k a ≲ L [ i ] l a) →
            (a >>= k) ≲ L [ i ] (a >>= l)
≲i>>=-cong-r {0} _ _ = ≲izero
≲i>>=-cong-r (now v) h =  h v
≲i>>=-cong-r {suc i} (later p) h = ≲ilater (≲i>>=-cong-r (force p) λ x → ≲idown (≤-step ≤-refl) (h x))
≲i>>=-cong-r (p ⊕ q) h = ≲i⊕-cong (≲i>>=-cong-r p h) (≲i>>=-cong-r q h)
≲i>>=-cong-r ∅ h = ≲irefl
≲i>>=-cong-r (eff e c) h = ≲ieff e λ r → ≲i>>=-cong-r (c r) h

~i>>=-cong-r : ∀ {i E A B L} (a : CTree E A ∞)
            {k l : A → CTree E B ∞} (h : ∀ a → k a ~ L [ i ] l a) →
            (a >>= k) ~ L [ i ] (a >>= l)
~i>>=-cong-r = ≲i>>=-cong-r {{≡-Ord}}

≲i>>='-cong-r : ∀ {i E A B L}  {{_ : Ord B}} (a : CTree' E A)
            {k l : A → CTree E B ∞} (h : ∀ a → k a ≲ L [ i ] l a) →
            (a >>=' k) ≲̂ L [ i ] (a >>=' l)
≲i>>='-cong-r (p ↑) h = ≲i>>=-cong-r p h
≲i>>='-cong-r (wait B c) h = ≲iwait (λ r → ≲i>>=-cong-r (c r) h)

>>=-step : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → CTree E B ∞) →
  (p >>=' k) [ l ]⇒ q → (∃[ v ]  ((p [ ⟨ ρ v ⟩ ]⇒ ∅ ↑) × (k v ↑ [ l ]⇒ q)))
    ⊎ (∃[ l' ] retFree l l' × (∃[ p' ] p [ l' ]⇒ p' × q ≡ p' >>=' k))
>>=-step (now v ↑) k trans = inj₁ ( v , ⇒-now v , trans)
>>=-step (later p ↑) k ⇒-later = inj₂ ( τ , retFreeτ ,  force p ↑ ,  ⇒-later , refl)
>>=-step ((p ⊕ q) ↑) k (⇒-⊕-l trans) with >>=-step (p ↑) k trans
... | inj₁ (v , trans1 , trans2)  = inj₁ (v , ⇒-⊕-l trans1 , trans2)
... | inj₂ (l' , rf , p' , trans' , b) = inj₂ ( l' , rf , p' , ⇒-⊕-l trans' , b)
>>=-step ((p ⊕ q)↑) k (⇒-⊕-r trans) with >>=-step (q ↑) k trans
... | inj₁ (v , trans1 , trans2)  = inj₁ (v , ⇒-⊕-r trans1 , trans2)
... | inj₂ (l' , rf , p' , trans' , b) = inj₂ ( l' , rf , p' , ⇒-⊕-r trans' , b)
>>=-step (eff e c ↑) k (⇒-eff .e _) = inj₂ ( ⟨ ε e ⟩ , retFreeε ,  wait _ c ,  ⇒-eff e c , refl)
>>=-step (wait _ c) k (⇒-inp r _) = inj₂ ( ⟨ ι r ⟩ , retFreeι ,  c r ↑ ,  ⇒-inp r c , refl)

>>=-step1 : ∀ {E A B l v} {p : CTree' E A} {p' : CTree' E A} {q : CTree' E B} (k : A → CTree E B ∞) →
          p [ ⟨ ρ v ⟩ ]⇒ p' → k v ↑ [ l ]⇒ q → (p >>=' k) [ l ]⇒ q
>>=-step1 k (⇒-now _) tr2 = tr2
>>=-step1 k (⇒-⊕-l tr1) tr2 = ⇒-⊕-l (>>=-step1 k tr1 tr2)
>>=-step1 k (⇒-⊕-r tr1) tr2 = ⇒-⊕-r (>>=-step1 k tr1 tr2)

>>=-step2 : ∀ {E A B l l' p'} (p : CTree' E A ) (k : A → CTree E B ∞) →
          retFree l l' → p [ l' ]⇒ p' → p >>=' k [ l ]⇒ p' >>=' k
>>=-step2 (now v ↑) k () (⇒-now .v) 
>>=-step2 (later p ↑) k retFreeτ ⇒-later = ⇒-later
>>=-step2 ((p ⊕ q)↑) k rf (⇒-⊕-l tr)
  with tr' ← >>=-step2 (p ↑) k rf tr =  ⇒-⊕-l tr'
>>=-step2 ((p ⊕ q)↑) k rf (⇒-⊕-r tr)
  with tr' ← >>=-step2 (q ↑) k rf tr =  ⇒-⊕-r tr'
>>=-step2 (eff e c ↑) k retFreeε (⇒-eff .e .c) = ⇒-eff e _
>>=-step2 (wait _ c) k retFreeι (⇒-inp r _) = ⇒-inp r _




⊑-retFree : ∀ {E A A'} {{_ : Ord A}} → {l l' : label E A} {l'' : label E A'} → retFree l'' l → l ⊑ l' → l ≡ l'
⊑-retFree retFreeε (⊑ε _) = refl
⊑-retFree retFreeι (⊑ι _) = refl
⊑-retFree retFreeτ ⊑τ = refl

⊑-retFree' : ∀ {E A A'} {{_ : Ord A}} → {l l' : label E A} {l'' : label E A'} → retFree l'' l' → l ⊑ l' → l ≡ l'
⊑-retFree' retFreeε (⊑ε _) = refl
⊑-retFree' retFreeι (⊑ι _) = refl
⊑-retFree' retFreeτ ⊑τ = refl


>>=-lsafe-l : ∀ {E L A B} {p : CTree' E A} {f : A → CTree E B ∞} → lsafe L (p >>=' f) → lsafe L p
>>=-lsafe-l {p = p} {f} ls {l = ⟨ ε x ⟩} tr with ls (>>=-step2 p f retFreeε tr)
... | isEffPredε .x x₁ = isEffPredε x x₁
>>=-lsafe-l ls {l = ⟨ ι x ⟩} tr = isEffPredι x
>>=-lsafe-l ls {l = ⟨ ρ x ⟩} tr = isEffPredρ x
>>=-lsafe-l ls {l = τ} tr = isEffPredτ

>>=-lsafe-r : ∀ {E L A B v} {p p' : CTree' E A} {f : A → CTree E B ∞} → lsafe L (p >>=' f) → p [ ⟨ ρ v ⟩ ]⇒ p' → lsafe L (f v ↑)
>>=-lsafe-r {f = f} ls ptr fvtr = ls (>>=-step1 f ptr fvtr)

≲i>>=-cong : ∀ {i E A B L} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree' E A} (b : p ≲̂ L [ i ] q)
              {k k' : A → CTree E B ∞} →
              (h : ∀ {a b} → a ⊑ b → (k a) ≲ L [ i ] (k' b)) →
              (p >>=' k) ≲̂ L [ i ] (q >>=' k')
≲i>>=-cong {i} b h = prf i (<×⇐-wf _) b h where
  prf : ∀ {E A B L} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree' E A} i (ac : Acc (×-Lex _≡_ _<_ _⇐_) (i , p)) (b : p ≲̂ L [ i ] q)
          {k k' : A → CTree E B ∞}  → (h : ∀ {a b} → a ⊑ b → (k a) ≲ L [ i ] (k' b)) → (p >>=' k) ≲̂ L [ i ] (q >>=' k')
  prf zero _ b h = ≲izero
  prf {L = L} {p = p} {q} (suc i) (acc rec) b {k} {k'} h = ≲istep left right where
    left : lsafe L (p >>=' k) → ∀ {l pk'} → p >>=' k [ l ]⇒ pk'
      → ∃[ l' ] ∃[ qk' ] l ⊑ l' × q >>=' k' [ l' ]⇒ qk' × pk' ≲̂ L [ lsuc l i ] qk'
    left ls trans with >>=-step p k trans
    ... | inj₁ (v , trans1 , trans2) with ≲ileft b (>>=-lsafe-l ls) trans1
    ... | ⟨ ρ v' ⟩ , q' , ⊑ρ leq , trans1' , b' with ≲ileft (h leq) (>>=-lsafe-r ls trans1) trans2
    ... | l' , kv' , leq' , trans2' , b''  =  l' , _ , leq' , >>=-step1 k' trans1' trans2' , b''
    left ls {⟨ a ⟩} trans | inj₂ (l' , rf , p' , trans' , refl) with retFreeAction rf
    ... | a' , refl with ≲ileft b (>>=-lsafe-l ls) trans'
    ... | l' ,  q' , leq , trans'' , b'' rewrite sym (⊑-retFree rf leq)
      = _ , _ , ⊑-refl ,  >>=-step2 q k' rf trans'' ,  prf (suc i) (rec (suc i , p') (inj₂(refl , _ , trans'))) b'' h 

    left ls {τ} trans | inj₂ (.τ , retFreeτ , p' , trans' , refl)  with ≲ileft b (>>=-lsafe-l ls) trans'
    ... | τ , q' , ⊑τ , trans'' , b'' =  _ , _ , ⊑τ , >>=-step2 q k' retFreeτ trans''
      ,  ≲itrans ≲irefl (prf i (rec (i , p') (inj₁ ≤-refl)) b'' λ le → ≲isuc (h le)) 

    right : lsafe L (p >>=' k) → ∀ {l qk'} → q >>=' k' [ l ]⇒ qk'
      → ∃[ l' ] ∃[ pk' ] l' ⊑ l × p >>=' k [ l' ]⇒ pk' × pk' ≲̂ L [ lsuc l i ] qk'
    right ls trans with >>=-step q k' trans
    ... | inj₁ (v , trans1 , trans2) with ≲iright b (>>=-lsafe-l ls) trans1
    ... | ⟨ ρ v' ⟩ , p' , ⊑ρ leq , trans1' , b' with ≲iright (h leq) (>>=-lsafe-r ls trans1') trans2
    ... | l' , kv' , leq' , trans2' , b'' =  l' , _ , leq' , >>=-step1 k trans1' trans2' , b''
    right ls {⟨ a ⟩} trans | inj₂ (l' , rf , q' , trans' , refl) with retFreeAction rf
    ... | a' , refl with ≲iright b (>>=-lsafe-l ls) trans' 
    ... | l' , p' , leq , trans'' , b'' rewrite ⊑-retFree' rf leq
      =  _ , _ , ⊑-refl , >>=-step2 p k rf trans'' , prf (suc i) (rec (suc i , p') (inj₂ (refl , _ , trans''))) b'' h
    right ls {τ} trans | inj₂ (.τ , retFreeτ , q' , trans' , refl)  with ≲iright b (>>=-lsafe-l ls) trans'
    ... | τ , p' , ⊑τ , trans'' , b'' =
      _ , _ , ⊑τ , >>=-step2 p k retFreeτ trans'' , prf i (rec (i , p') (inj₁ ≤-refl)) b'' λ le → ≲isuc (h le)

~i>>=-cong : ∀ {i E A B L}  {p q : CTree' E A} (b : p ~̂ L [ i ] q)
              {k k' : A → CTree E B ∞} →
              (h : ∀ a → (k a) ~ L [ i ] (k' a)) →
              (p >>=' k) ~̂ L [ i ] (q >>=' k')
~i>>=-cong b h = ≲i>>=-cong {{≡-Ord}} {{≡-Ord}} b λ { {a} refl → h a}

≲i>>=-cong-l : ∀ {i E A B L} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree' E A} (b : p ≲̂ L [ i ] q)
              {k : A → CTree E B ∞} →
              (h : ∀ {a b} → a ⊑ b → (k a) ≲ L [ i ] (k b)) →
              (p >>=' k) ≲̂ L [ i ] (q >>=' k)
≲i>>=-cong-l {i} b h = ≲i>>=-cong b h 

~i>>=-cong-l : ∀ {i E A B L} {p q : CTree' E A} (b : p ~̂ L [ i ] q)
              {k : A → CTree E B ∞} →
              (p >>=' k) ~̂ L [ i ] (q >>=' k)
~i>>=-cong-l {i} b = ~i>>=-cong b λ x → ~irefl


≲i>>=-assoc' : ∀ {E A B C i} {{_ : Ord C}} (p : CTree E A ∞)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞}{f : A → CTree E C ∞} →
                (∀ a → k a >>= l ≲[ i ] f a) →
                ((p >>= k) >>= l) ≲[ i ] (p >>= f)
≲i>>=-assoc' p b = ≲itrans (≲i>>=-assoc p) (≲i>>=-cong-r p b)

~i>>=-assoc' : ∀ {E A B C i} (p : CTree E A ∞)
                {k : A → CTree E B ∞}{l : B → CTree E C ∞}{f : A → CTree E C ∞} →
                (∀ a → k a >>= l ~[ i ] f a) →
                ((p >>= k) >>= l) ~[ i ] (p >>= f)
~i>>=-assoc' p b = ~itrans (~i>>=-assoc p) (~i>>=-cong-r p b)


------------------------
-- congruence for map --
------------------------


map' : ∀ {A B E} → (A → B) → CTree' E A → CTree' E B
map' f p = p >>=' (λ x → return (f x))


≲imap'-id : ∀ {E A L i} {{_ : Ord A}} (p : CTree' E A) → map' id p ≲̂ L [ i ] p
≲imap'-id (p ↑) = ≲imap-id p
≲imap'-id (wait B c) = ≲iwait (λ r → ≲imap-id (c r))

≲imap'-∘ : ∀ {E A B C L i} {{_ : Ord C}} (p : CTree' E A) {f : A → B} {g : B → C}
  → map' g (map' f p) ≲̂ L [ i ] map' (g ∘ f) p
≲imap'-∘ (p ↑) = ≲imap-∘ p
≲imap'-∘ (wait B c) = ≲iwait (λ r → ≲imap-∘(c r))

≲imap-cong : ∀ {i E A B L} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree' E A}
             (b : p ≲̂ L [ i ] q) → {f : A → B} → (le : ∀ {a b} → a ⊑ b → f a ⊑ f b) → map' f p ≲̂ L [ i ] map' f q
≲imap-cong b le = ≲i>>=-cong-l b λ le' → ≲i⊑ (le le')

~imap-cong : ∀ {i E A B L} {p q : CTree' E A}
             (b : p ~̂ L [ i ] q) → {f : A → B} → map' f p ~̂ L [ i ] map' f q
~imap-cong b = ≲imap-cong {{≡-Ord}} {{≡-Ord}} b λ {refl → refl}

≲imap->>= : ∀ {E A B C L i} {{_ : Ord C}} (p : CTree E A ∞)
                {k : A → B}{l : B → CTree E C ∞} →
                ((map k p) >>= l) ≲ L [ i ] (p >>= λ a → l (k a))
≲imap->>= p {k} {l} = ≲itrans (≲i>>=-assoc p) (≲i>>=-cong-r p (λ r → ≲ireturn->>= {f = l}))

~imap->>= : ∀ {E A B C L i} (p : CTree E A ∞)
                {k : A → B}{l : B → CTree E C ∞} →
                ((map k p) >>= l) ~ L [ i ] (p >>= λ a → l (k a))
~imap->>= = ≲imap->>= {{≡-Ord}}

-----------
-- never --
-----------

~inever->>= : ∀ {i A B E L} {f : A → CTree E B ∞} → (never >>= f) ~ L [ i ] never
~inever->>= {zero} = ~izero
~inever->>= {suc i} {L = L} {f = f} = ~istep left right where
  left : lsafe L (later (∞never ∞>>= f) ↑) → ∀ {l p'} → later (∞never ∞>>= f) ↑ [ l ]⇒ p'
    → ∃[ q' ] never ↑ [ l ]⇒ q' × p' ~̂ L [ lsuc l i ] q'
  left _ ⇒-later = _ ,  ⇒-later , ~inever->>= {i}
  right : lsafe L (later (∞never ∞>>= f) ↑) → ∀ {l q'} → never ↑ [ l ]⇒ q'
    → ∃[ p' ] later (∞never ∞>>= f) ↑ [ l ]⇒ p' × p' ~̂ L [ lsuc l i ] q'
  right _ ⇒-later = _ , ⇒-later , ~inever->>= {i}

≲inever->>= : ∀ {i A B E L} {{_ : Ord B}} {f : A → CTree E B ∞} → (never >>= f) ≲ L [ i ] never
≲inever->>= = ~i-≲i ~inever->>=

map-step : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → B) →
  (map' k p) [ l ]⇒ q → (∃[ v ]  ((p [ ⟨ ρ v ⟩ ]⇒ ∅ ↑) × l ≡ ⟨ ρ (k v) ⟩ ))
    ⊎ (∃[ l' ] retFree l l' × (∃[ p' ] p [ l' ]⇒ p' × q ≡ map' k p'))
map-step p k tr with >>=-step p (λ x → return (k x)) tr
... | inj₁ (v , tr1 , ⇒-now .(k v)) = inj₁ ( v , tr1 , refl)
... | inj₂ (l' , rf , p' , tr' , refl) = inj₂ (l' , rf , p' , tr' , refl)

map-step1 : ∀ {E A B v} {p : CTree' E A} {p' : CTree' E A} (k : A → B) →
          p [ ⟨ ρ v ⟩ ]⇒ p' → (map' k p) [ ⟨ ρ (k v)⟩ ]⇒ ∅ ↑
map-step1 k tr = >>=-step1 (λ x → return (k x)) tr (⇒-now _)

map-step2 : ∀ {E A B l l' p'} (p : CTree' E A ) (k : A → B) →
          retFree l l' → p [ l' ]⇒ p' → map' k p [ l ]⇒ map' k p'
map-step2 p k rf tr = >>=-step2 p (λ x → return (k x)) rf tr

map-step-lmap : ∀ {E A B l p'} (p : CTree' E A ) (k : A → B) →
          p [ l ]⇒ p' → map' k p [ lmap k l ]⇒ map' k p'
map-step-lmap {l = ⟨ ε x ⟩} p k tr = map-step2 p k retFreeε tr
map-step-lmap {l = ⟨ ι x ⟩} p k tr = map-step2 p k retFreeι tr
map-step-lmap {l = ⟨ ρ x ⟩} p k tr rewrite ⇒-ρ-∅ tr = map-step1 k tr
map-step-lmap {l = τ} p k tr = map-step2 p k retFreeτ tr



map-step' : ∀ {E A B l} (p : CTree' E A) {q : CTree' E B } (k : A → B) (k' : B → A) (eq : ∀ v → k' (k v) ≡ v) →
  (map' k p) [ l ]⇒ q → ((∃[ p' ] p [ lmap k' l ]⇒ p' × q ≡ map' k p'))
map-step' p k k' eq tr with map-step p k tr
... | inj₁ (v , tr' , refl) rewrite eq v rewrite ⇒-ρ-∅ tr =  ∅ ↑ , tr' , refl
... | inj₂ (l' , rf , p' , tr' , refl) rewrite retFree-lmap k' rf = p' , tr' , refl 
