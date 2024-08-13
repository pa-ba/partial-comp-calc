{-# OPTIONS --sized-types #-}


module CTree.IndexedBisimilarity.PatternMatching where

open import CTree.IndexedBisimilarity.BasicProperties public
open import CTree.IndexedBisimilarity.MonadLaws public
open import CTree.IndexedBisimilarity.Bind public
open import Data.Maybe hiding (_>>=_; map)
open import Function
open import Data.Bool


----------------------
-- Pattern matching --
----------------------

match : ∀ {i} {A B : Set} {C : Set} {E} → (A → Maybe B) → CTree E C i → (B → CTree E C i) → A → CTree E C i
match m d f a with m a
... | just x =  f x
... | nothing = d

getJust : ∀ {i} {A : Set} {B : Set} {E} → CTree E B i → (A → CTree E B i) → Maybe A → CTree E B i
getJust = match id


≲imatch-assoc : ∀ {i A B C D E L} {{_ : Ord D}} (c : A → Maybe B) (m : CTree E A ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞}{g : C → CTree E D ∞} →
               ((m >>= match c d f) >>= g) ≲ L [ i ] (m >>= match c (d >>= g) (λ x → f x >>=  g))
≲imatch-assoc {i} {A} {B} {L = L} c m {d} {f} {g} =
            ≲itrans (≲i>>=-assoc m) ( ≲i>>=-cong-r m (λ x → cases c x ))
  where 
  cases : (c : A → Maybe B) (x : A) →
          (match c d f x >>= g) ≲ L [ i ] (match c (d >>= g) (λ y → f y >>= g) x)
  cases c x with c x
  ... | just y  =  ≲irefl
  ... | nothing =  ≲irefl

~imatch-assoc : ∀ {i A B C D E L} (c : A → Maybe B) (m : CTree E A ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞}{g : C → CTree E D ∞} →
               ((m >>= match c d f) >>= g) ~ L [ i ] (m >>= match c (d >>= g) (λ x → f x >>=  g))
~imatch-assoc = ≲imatch-assoc {{≡-Ord}}

≲igetJust-assoc : ∀ {i B C D E L} {{_ : Ord D}} (m : CTree E (Maybe B) ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞}{g : C → CTree E D ∞} →
               ((m >>= getJust d f) >>= g) ≲ L [ i ] (m >>= getJust (d >>= g) (λ x → f x >>= g))
≲igetJust-assoc = ≲imatch-assoc id

~igetJust-assoc : ∀ {i B C D E L} (m : CTree E (Maybe B) ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞}{g : C → CTree E D ∞} →
               ((m >>= getJust d f) >>= g) ~ L [ i ] (m >>= getJust (d >>= g) (λ x → f x >>= g))
~igetJust-assoc = ~imatch-assoc id



≲imatch-cong-default : ∀{i A B C E L} {{_ : Ord C}} (c : A → Maybe B) (m : CTree E A ∞)
  {d : CTree E C ∞} {e : CTree E C ∞} {f : B → CTree E C ∞}
               (h : d ≲ L [ i ] e) →
               (m >>= match c d f) ≲ L [ i ] (m >>= match c e f)
≲imatch-cong-default {i} {A} {L = L} c m {d} {e} {f} h =  ≲i>>=-cong-r m   cases
  where cases : (a : A) → (match c d f a) ≲ L [ i ] (match c e f a)
        cases a with c a
        ...| just x =  ≲irefl
        ...| nothing = h

~imatch-cong-default : ∀{i A B C E L} (c : A → Maybe B) (m : CTree E A ∞)
  {d : CTree E C ∞} {e : CTree E C ∞} {f : B → CTree E C ∞}
               (h : d ~ L [ i ] e) →
               (m >>= match c d f) ~ L [ i ] (m >>= match c e f)
~imatch-cong-default = ≲imatch-cong-default {{≡-Ord}}

≲igetJust-cong-default : ∀{i B C E L} {{_ : Ord C}} (m : CTree E (Maybe B) ∞)
  {d : CTree E C ∞} {e : CTree E C ∞} {f : B → CTree E C ∞}
               (h : d ≲ L [ i ] e) →
               (m >>= getJust d f) ≲ L [ i ] (m >>= getJust e f)
≲igetJust-cong-default = ≲imatch-cong-default id

~igetJust-cong-default : ∀{i B C E L} (m : CTree E (Maybe B) ∞)
  {d : CTree E C ∞} {e : CTree E C ∞} {f : B → CTree E C ∞}
               (h : d ~ L [ i ] e) →
               (m >>= getJust d f) ~ L [ i ] (m >>= getJust e f)
~igetJust-cong-default = ~imatch-cong-default id


≲imatch-cong : ∀{i A B C E L } {{_ : Ord C}} (c : A → Maybe B) (m : CTree E A ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞} {g : B → CTree E C ∞}
               (h : ∀ x → f x ≲ L [ i ] g x) →
               (m >>= match c d f) ≲ L [ i ] (m >>= match c d g)
≲imatch-cong {i} {A} {L = L} c m {d} {f} {g} e =  ≲i>>=-cong-r m  cases
  where cases : (x : A) → match c d f x ≲ L [ i ] match c d g x
        cases x with c x
        ...| just y =  e y
        ...| nothing =  ≲irefl

~imatch-cong : ∀{i A B C E L } (c : A → Maybe B) (m : CTree E A ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞} {g : B → CTree E C ∞}
               (h : ∀ x → f x ~ L [ i ] g x) →
               (m >>= match c d f) ~ L [ i ] (m >>= match c d g)
~imatch-cong = ≲imatch-cong {{≡-Ord}}

≲igetJust-cong : ∀{i B C E L} {{_ : Ord C}} (m : CTree E (Maybe B) ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞} {g : B → CTree E C ∞}
               (h : ∀ x → f x ≲ L [ i ] g x) →
               (m >>= getJust d f) ≲ L [ i ] (m >>= getJust d g)
≲igetJust-cong = ≲imatch-cong id

~igetJust-cong : ∀{i B C E L} (m : CTree E (Maybe B) ∞) {d : CTree E C ∞}
               {f : B → CTree E C ∞} {g : B → CTree E C ∞}
               (h : ∀ x → f x ~ L [ i ] g x) →
               (m >>= getJust d f) ~ L [ i ] (m >>= getJust d g)
~igetJust-cong = ~imatch-cong id

≲imatch-distr :  ∀ {A B i C E L }  {{_ : Ord C}} (c : A → Maybe B)
            {p q : CTree E C ∞} {f : B → CTree E C ∞} a
            → match c p f a ⊕ q ≲ L [ i ] match c (p ⊕ q) (λ x → f x ⊕ q) a
≲imatch-distr c a with c a
... | nothing = ≲irefl
... | just x = ≲irefl

~imatch-distr :  ∀ {A B i C E L } (c : A → Maybe B)
            {p q : CTree E C ∞} {f : B → CTree E C ∞} a
            → match c p f a ⊕ q ~ L [ i ] match c (p ⊕ q) (λ x → f x ⊕ q) a
~imatch-distr = ≲imatch-distr {{≡-Ord}}

≲iif->>= : ∀ {A B E L i} {{_ : Ord B}} {x y : CTree E A ∞} {f : A → CTree E B ∞} b 
  → ((if b then x else y) >>= f) ≲ L [ i ] (if b then (x >>= f) else (y >>= f))
≲iif->>= false =  ≲irefl
≲iif->>= true = ≲irefl

~iif->>= : ∀ {A B E L i} {x y : CTree E A ∞} {f : A → CTree E B ∞} b 
  → ((if b then x else y) >>= f) ~ L [ i ] (if b then (x >>= f) else (y >>= f))
~iif->>= = ≲iif->>= {{≡-Ord}}

≲iif-then-cong : ∀ b {A E n}  {{_ : Ord A}} {x y x' : CTree E A ∞} (eq : x ≲[ n ] x')
  → (if b then x else y) ≲[ n ] (if b then x' else y)
≲iif-then-cong false eq = ≲irefl
≲iif-then-cong true eq =  eq

~iif-then-cong : ∀ b {A E n} {x y x' : CTree E A ∞} (eq : x ~[ n ] x')
  → (if b then x else y) ~[ n ] (if b then x' else y)
~iif-then-cong b = ≲iif-then-cong b {{≡-Ord}}
