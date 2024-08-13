{-# OPTIONS --copatterns --sized-types --guardedness #-}

module CCTree.IndexedBisimilarity where
open import Preorder
open import CCTree.Definitions public
import CTree.Bisimilarity as CT
open import Data.Product hiding (map)
open import Size public
open import Data.Unit
import CTree as CT
open import Data.Nat
open import Data.Maybe hiding (_>>=_) renaming (map to mapMaybe)
open import Relation.Binary.PropositionalEquality

---------------------------------------------
-- Definition of step-indexed bisimilarity --
---------------------------------------------



infix 3 _≲[_]_
record _≲[_]_ {E A} {{_ : Ord A}} {{_ : Concurrent E}} (p : CCTree E A ∞) (i : ℕ) (q : CCTree E A ∞) : Set₁ where
  constructor ≲imk
  field
    ≲iapp : ⟦ p ⟧ CT.return CT.≲[ i ] ⟦ q ⟧ CT.return

open _≲[_]_ public


infix 3 _~[_]_
_~[_]_ : {E : Set → Set} {A : Set} {{_ : Concurrent E}} → CCTree E A ∞ → ℕ → CCTree E A ∞ → Set₁ 
_~[_]_ = _≲[_]_ {{≡-Ord}}


~iapp : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ i ] q → ⟦ p ⟧ CT.return CT.~[ i ] ⟦ q ⟧ CT.return
~iapp = ≲iapp {{≡-Ord}}

~imk : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree E A ∞} → ⟦ p ⟧ CT.return CT.~[ i ] ⟦ q ⟧ CT.return → p ~[ i ] q
~imk = ≲imk {{≡-Ord}}


--------------------------------
-- Definition of bisimilarity --
--------------------------------

infix 3 _≲_
record _≲_  {E A} {{_ : Ord A}} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E A ∞) : Set₁ where
  constructor ≲mk
  field
    ≲app : ⟦ p ⟧ CT.return CT.≲ ⟦ q ⟧ CT.return

open _≲_ public


infix 3 _~_
_~_ : {E : Set → Set} {A : Set} {{_ : Concurrent E}} → CCTree E A ∞ → CCTree E A ∞ → Set₁
_~_ = _≲_ {{≡-Ord}}



~app : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~ q → ⟦ p ⟧ CT.return CT.~ ⟦ q ⟧ CT.return
~app = ≲app {{≡-Ord}}

~mk : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree E A ∞} → ⟦ p ⟧ CT.return CT.~ ⟦ q ⟧ CT.return → p ~ q
~mk = ≲mk {{≡-Ord}}

≲-≲i : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞} → (p ≲ q) → p ≲[ i ] q
≲-≲i (≲mk eq) = ≲imk (CT.≲-≲i eq)

≲i-≲ : ∀ {E A} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞} → (∀ i → p ≲[ i ] q) → p ≲ q
≲i-≲ eqi = ≲mk (CT.≲i-≲ λ i → ≲iapp (eqi i))


~-~i : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree E A ∞} → (p ~ q) → p ~[ i ] q
~-~i = ≲-≲i {{≡-Ord}}

~i-~ : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree E A ∞} → (∀ i → p ~[ i ] q) → p ~ q
~i-~ = ≲i-≲ {{≡-Ord}}

≲i-~i : ∀ {E A i } {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞}
  → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ≲[ i ] q → p ~[ i ] q
≲i-~i le (≲imk b) = ~imk (CT.≲i-~i le b)

-----------------------
-- basice properties --
-----------------------

~i-≲i : ∀ {E A i } {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ i ] q → p ≲[ i ] q
~i-≲i (≲imk b) = ≲imk (CT.~i-≲i b)

≲izero : ∀ {E A} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ≲[ 0 ] q
≲izero = ≲imk CT.≲izero

~izero : ∀ {E A} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ 0 ] q
~izero = ≲izero {{≡-Ord}}

≲i⊑ : ∀ {i E A} {{_ : Ord A}} {{_ : Concurrent E}} {v w : A} → v ⊑ w → return {E = E} v ≲[ i ] return w
≲i⊑ le = ≲imk (CT.≲i⊑ le)


≲irefl : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree E A ∞} → p ≲[ i ] p
≲irefl = ≲imk (CT.≲irefl)

~irefl : ∀ {E A i}{{_ : Concurrent E}} {p : CCTree E A ∞} → p ~[ i ] p
~irefl = ≲irefl {{≡-Ord}}


~isym : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ~[ i ] q → q ~[ i ] p
~isym (≲imk b) = ≲imk (CT.~isym b)

≲itrans : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q r : CCTree E A ∞} → p ≲[ i ] q → q ≲[ i ] r → p ≲[ i ] r
≲itrans (≲imk b1) (≲imk b2) = ≲imk (CT.≲itrans b1 b2)


~itrans : ∀ {E A i} {{_ : Concurrent E}} {p q r : CCTree E A ∞} → p ~[ i ] q → q ~[ i ] r → p ~[ i ] r
~itrans = ≲itrans {{≡-Ord}}


------------------------
-- calculation syntax --
------------------------


module ~i-Calculation where
  _~⟨_⟩_ : ∀ {E A i} {{_ : Concurrent E}} (x : CCTree E A ∞) →
    ∀ {y : CCTree E A ∞} {z : CCTree E A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
  _~⟨_⟩_ {_} x r eq =  ~itrans r eq
  
  _≡⟨⟩_ : ∀ {E A i} {{_ : Concurrent E}} (x : CCTree E A ∞) → ∀ {y : CCTree E A ∞} → x ~[ i ] y → x ~[ i ] y
  _≡⟨⟩_  x eq = eq


  _∎ : ∀ {E A i} {{_ : Concurrent E}} (x : CCTree E A ∞) → x ~[ i ] x
  _∎  x = ~irefl

  infix  3 _∎
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_

module ≲i-Calculation where
  infix  3 _∎
  infixr 1 _≲⟨_⟩_
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_

  _≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree E A ∞) →
    ∀ {y : CCTree E A ∞} {z : CCTree E A ∞} → x ≲[ i ] y → y ≲[ i ] z → x ≲[ i ] z
  _≲⟨_⟩_ {_} x r eq =  ≲itrans r eq

  _~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree E A ∞) →
    ∀ {y : CCTree E A ∞} {z : CCTree E A ∞} → x ~[ i ] y → y ≲[ i ] z → x ≲[ i ] z
  _~⟨_⟩_ {_} x r eq =  ≲itrans (~i-≲i r) eq

  _≡⟨⟩_ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree E A ∞) → ∀ {y : CCTree E A ∞} → x ≲[ i ] y → x ≲[ i ] y
  _≡⟨⟩_  x eq = eq

  _∎ : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} (x : CCTree E A ∞) → x ≲[ i ] x
  _∎  x = ≲irefl


-----------------
-- congruences --
-----------------


≲i>>=-cong-r : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : A → CCTree E B ∞} (h : ∀ a → k a ≲[ i ] l a) →
          (a >>= k) ≲[ i ] (a >>= l)
≲i>>=-cong-r a h = ≲imk (≲icong a (λ x → ≲iapp (h x))) 


~i>>=-cong-r : ∀ {E A B i} {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : A → CCTree E B ∞} (h : ∀ a → k a ~[ i ] l a) →
          (a >>= k) ~[ i ] (a >>= l)
~i>>=-cong-r = ≲i>>=-cong-r {{≡-Ord}}

≲i>>-cong-r : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : CCTree E B ∞} (h : k ≲[ i ] l) →
          (a >> k) ≲[ i ] (a >> l)
≲i>>-cong-r a h = ≲i>>=-cong-r a (λ _ → h)


~i>>-cong-r : ∀ {E A B i} {{_ : Concurrent E}} (a : CCTree E A ∞)
          {k l : CCTree E B ∞} (h : k ~[ i ] l) →
          (a >> k) ~[ i ] (a >> l)
~i>>-cong-r a h = ~i>>=-cong-r a (λ _ → h)

≲imap-cong : ∀ {E A B i} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}}  {p q : CCTree E A ∞} (b : p ≲[ i ] q)
                {f : A → B} → (le : ∀ {a b} → a ⊑ b → f a ⊑ f b) → map f p ≲[ i ] map f q
≲imap-cong {p = p} {q} b {f} le = ≲imk (CT.≲itrans (CT.~i-≲i (CT.~isym (~icong-map p {f} {CT.return})))
  (CT.≲itrans (CT.≲imap-cong (≲iapp b) le) (CT.~i-≲i (~icong-map q {f} {CT.return}))))


~imap-cong : ∀ {E A B i} {{_ : Concurrent E}}  {p q : CCTree E A ∞} (b : p ~[ i ] q)
                {f : A → B} → map f p ~[ i ] map f q
~imap-cong {p = p} {q} b {f} = ≲imk (CT.~itrans (CT.~isym (~icong-map p {f} {CT.return}))
  (CT.~itrans (CT.~imap-cong (~iapp b)) (~icong-map q {f} {CT.return})))




≲ilater : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {a b : ∞CCTree E A ∞} → force a ≲[ i ] force b → later a ≲[ suc i ] later b
≲ilater (≲imk b) = ≲imk (CT.≲ilater b)

~ilater : ∀ {E A i} {{_ : Concurrent E}} {a b : ∞CCTree E A ∞} → force a ~[ i ] force b → later a ~[ suc i ] later b
~ilater (≲imk b) = ~imk (CT.~ilater b)


≲i⊕-cong : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p1 q1 p2 q2 : CCTree E A ∞} → p1 ≲[ i ] p2 → q1 ≲[ i ] q2
  → p1 ⊕ q1 ≲[ i ] p2 ⊕ q2
≲i⊕-cong (≲imk b1) (≲imk b2) = ≲imk (CT.≲i⊕-cong b1 b2)


~i⊕-cong : ∀ {E A i} {{_ : Concurrent E}} {p1 q1 p2 q2 : CCTree E A ∞} → p1 ~[ i ] p2 → q1 ~[ i ] q2
  → p1 ⊕ q1 ~[ i ] p2 ⊕ q2
~i⊕-cong (≲imk b1) (≲imk b2) = ~imk (CT.~i⊕-cong b1 b2)


≲i⊕-cong-r : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q q' : CCTree E A ∞} → q ≲[ i ] q' → p ⊕ q ≲[ i ] p ⊕ q'
≲i⊕-cong-r ≲q = ≲i⊕-cong ≲irefl ≲q

~i⊕-cong-r : ∀ {E A i} {{_ : Concurrent E}} {p q q' : CCTree E A ∞} → q ~[ i ] q' → p ⊕ q ~[ i ] p ⊕ q'
~i⊕-cong-r ~q = ~i⊕-cong ~irefl ~q


≲i⊕-cong-l : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q p' : CCTree E A ∞} → p ≲[ i ] p' → p ⊕ q ≲[ i ] p' ⊕ q
≲i⊕-cong-l ≲p =  ≲i⊕-cong ≲p ≲irefl

~i⊕-cong-l : ∀ {E A i} {{_ : Concurrent E}} {p q p' : CCTree E A ∞} → p ~[ i ] p' → p ⊕ q ~[ i ] p' ⊕ q
~i⊕-cong-l ~p =  ~i⊕-cong ~p ~irefl


≲ieff : ∀{E A B i} {{_ : Ord A}} {{_ : Concurrent E}} {c d : B → CCTree E A ∞} (e : E B) → (∀ x → c x ≲[ i ] d x) → eff e c ≲[ i ] eff e d
≲ieff e f  = ≲imk (CT.≲ieff e (λ x → ≲iapp (f x)))

~ieff : ∀{E A B i} {{_ : Concurrent E}} {c d : B → CCTree E A ∞} (e : E B) → (∀ x → c x ~[ i ] d x) → eff e c ~[ i ] eff e d
~ieff = ≲ieff {{≡-Ord}}


--------------------------
-- properties about >>= --
--------------------------

≲inever->>= : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} {f : A → CCTree E B ∞} → (never >>= f) ≲[ i ] never
≲inever->>= {i = 0} = ≲izero
≲inever->>= {i = suc i} {f = f} = ≲imk (CT.≲ilater (≲iapp (≲inever->>= {f = f})))

~inever->>= : ∀ {E A B i} {{_ : Concurrent E}} {f : A → CCTree E B ∞} → (never >>= f) ~[ i ] never
~inever->>= = ≲inever->>= {{≡-Ord}}


≲i>>=-later : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} {p : ∞CCTree E A ∞} {f : A → CCTree E B ∞}
  → (later p >>= f) ≲[ i ] later (p ∞>>= f)
≲i>>=-later {i = zero} = ≲izero
≲i>>=-later {i = suc i} {p = p} {f} = ≲imk (CT.≲ilater CT.≲irefl)

~i>>=-later : ∀ {E A B i} {{_ : Concurrent E}} {p : ∞CCTree E A ∞} {f : A → CCTree E B ∞}
  → (later p >>= f) ~[ i ] later (p ∞>>= f)
~i>>=-later = ≲i>>=-later {{≡-Ord}}



----------------
-- monad laws --
----------------


≲i>>=-return : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree E A ∞}  → (p >>= return) ≲[ i ] p
≲i>>=-return = ≲imk CT.≲irefl

~i>>=-return : ∀ {E A i} {{_ : Concurrent E}} {p : CCTree E A ∞}  → (p >>= return) ~[ i ] p
~i>>=-return = ~imk CT.~irefl

≲ireturn->>= : ∀ {E A B} {{_ : Ord B}} {{_ : Concurrent E}} {i} {x : A} {f : A → CCTree E B ∞}  → (return x >>= f) ≲[ i ] f x
≲ireturn->>= = ≲imk CT.≲irefl

~ireturn->>= : ∀ {E A B} {{_ : Concurrent E}} {i} {x : A} {f : A → CCTree E B ∞}  → (return x >>= f) ~[ i ] f x
~ireturn->>= = ~imk CT.~irefl


≲i>>=-assoc : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞} →
                ((p >>= k) >>= l) ≲[ i ] (p >>= λ a → k a >>= l)
≲i>>=-assoc p {k} {l} = ≲imk CT.≲irefl

~i>>=-assoc : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞} →
                ((p >>= k) >>= l) ~[ i ] (p >>= λ a → k a >>= l)
~i>>=-assoc p {k} {l} = ~imk CT.~irefl



≲i>>=-assoc' : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞}{f : A → CCTree E C ∞} →
                (∀ a → k a >>= l ≲[ i ] f a) →
                ((p >>= k) >>= l) ≲[ i ] (p >>= f)
≲i>>=-assoc' p b = ≲itrans (≲i>>=-assoc p) (≲i>>=-cong-r p b)

~i>>=-assoc' : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → CCTree E B ∞}{l : B → CCTree E C ∞}{f : A → CCTree E C ∞} →
                (∀ a → k a >>= l ~[ i ] f a) →
                ((p >>= k) >>= l) ~[ i ] (p >>= f)
~i>>=-assoc' p b = ~itrans (~i>>=-assoc p) (~i>>=-cong-r p b)


≲i>>-assoc : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞)
             {q : CCTree E B ∞}{r : CCTree E C ∞} →
             (p >> q) >> r ≲[ i ] p >> (q >> r)
≲i>>-assoc p = ≲i>>=-assoc p

~i>>-assoc : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞)
             {q : CCTree E B ∞}{r : CCTree E C ∞} →
             (p >> q) >> r ~[ i ] p >> (q >> r)
~i>>-assoc p = ~i>>=-assoc p

≲i>>-assoc' : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : CCTree E B ∞}{l : B → CCTree E C ∞}{f : CCTree E C ∞} →
                (k >>= l ≲[ i ] f) →
                ((p >> k) >>= l) ≲[ i ] (p >> f)
≲i>>-assoc' p b = ≲itrans (≲i>>=-assoc p) (≲i>>-cong-r p b)


~i>>-assoc' : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : CCTree E B ∞}{l : B → CCTree E C ∞}{f : CCTree E C ∞} →
                (k >>= l ~[ i ] f) →
                ((p >> k) >>= l) ~[ i ] (p >> f)
~i>>-assoc' p b = ~itrans (~i>>=-assoc p) (~i>>-cong-r p b)

≲imap->>= : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → B}{l : B → CCTree E C ∞} →
                ((map k p) >>= l) ≲[ i ] (p >>= λ a → l (k a))
≲imap->>= p {k} {l} = ≲itrans (≲i>>=-assoc p) (≲i>>=-cong-r p (λ r → ≲ireturn->>=))


~imap->>= : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞)
                {k : A → B}{l : B → CCTree E C ∞} →
                ((map k p) >>= l) ~[ i ] (p >>= λ a → l (k a))
~imap->>= p {k} {l} = ~itrans (~i>>=-assoc p) (~i>>=-cong-r p (λ r → ~ireturn->>=))

~imap-return : ∀ {E A B i} {{_ : Concurrent E}} {v : A} {f : A → B} →
                map f (return v) ~[ i ] return {E = E} (f v)
~imap-return = ~imk CT.~irefl

open ~i-Calculation

~i>>=-return->>= : ∀ {E A B C D i} {{_ : Concurrent E}} (p : CCTree E A ∞) →
                {f : A → B} {g : A → B → CCTree E C ∞}{h : C → CCTree E D ∞} →
               p >>= (λ x → return (f x) >>= g x) >>= h ~[ i ] p >>= (λ x → g x (f x)) >>= h
~i>>=-return->>= p {f} {g} {h} =
  ((p >>= (λ x → return (f x) >>= g x)) >>= h)
  ~⟨ ~i>>=-assoc p ⟩
  (p >>= (λ x → (return (f x) >>= g x) >>= h)) 
  ~⟨ (~i>>=-cong-r p λ x → ~i>>=-assoc _) ⟩
  (p >>= (λ x → return (f x) >>= (λ y → g x y >>= h)))
  ~⟨ (~i>>=-cong-r p λ x → ~ireturn->>=) ⟩
  (p >>= (λ x → (g x (f x)) >>= h))
  ~⟨ ~isym (~i>>=-assoc p) ⟩
  (p >>= (λ x → g x (f x)) >>= h)
  ∎

≲i>>=-return->>= : ∀ {E A B C D i} {{_ : Ord D}} {{_ : Concurrent E}} (p : CCTree E A ∞) →
                {f : A → B} {g : A → B → CCTree E C ∞}{h : C → CCTree E D ∞} →
               p >>= (λ x → return (f x) >>= g x) >>= h ≲[ i ] p >>= (λ x → g x (f x)) >>= h
≲i>>=-return->>= p = ~i-≲i (~i>>=-return->>= p)


--------------------------
-- non-determinism laws --
--------------------------


≲i⊕-unit-l : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree E A ∞} → ∅ ⊕ p ≲[ i ] p
≲i⊕-unit-l = ≲imk CT.≲i⊕-unit-l

~i⊕-unit-l : ∀ {E A i} {{_ : Concurrent E}} {p : CCTree E A ∞} → ∅ ⊕ p ~[ i ] p
~i⊕-unit-l = ~imk CT.~i⊕-unit-l


≲i⊕-assoc : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q r : CCTree E A ∞} → (p ⊕ q) ⊕ r ≲[ i ] p ⊕ (q ⊕ r)
≲i⊕-assoc = ≲imk CT.≲i⊕-assoc

~i⊕-assoc : ∀ {E A i} {{_ : Concurrent E}} {p q r : CCTree E A ∞} → (p ⊕ q) ⊕ r ~[ i ] p ⊕ (q ⊕ r)
~i⊕-assoc = ~imk CT.~i⊕-assoc


≲i⊕-idem : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ p ≲[ i ] p
≲i⊕-idem = ≲imk CT.≲i⊕-idem

~i⊕-idem : ∀ {E A i} {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ p ~[ i ] p
~i⊕-idem = ~imk CT.~i⊕-idem

≲i⊕-comm : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ⊕ q ≲[ i ] q ⊕ p
≲i⊕-comm = ≲imk CT.≲i⊕-comm

~i⊕-comm : ∀ {E A i} {{_ : Concurrent E}} {p q : CCTree E A ∞} → p ⊕ q ~[ i ] q ⊕ p
~i⊕-comm = ~imk CT.~i⊕-comm

≲i⊕-unit-r : ∀ {E A i} {{_ : Ord A}} {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ ∅ ≲[ i ] p
≲i⊕-unit-r = ≲imk CT.≲i⊕-unit-r

~i⊕-unit-r : ∀ {E A i} {{_ : Concurrent E}} {p : CCTree E A ∞} → p ⊕ ∅ ~[ i ] p
~i⊕-unit-r = ~imk CT.~i⊕-unit-r

≲i⊕-distr : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} (p q : CCTree E A ∞) {f : A → CCTree E B ∞}
  → (p ⊕ q) >>= f ≲[ i ] (p >>= f) ⊕ (q >>= f)
≲i⊕-distr p q = ≲imk CT.≲irefl

~i⊕-distr : ∀ {E A B i} {{_ : Concurrent E}} (p q : CCTree E A ∞) {f : A → CCTree E B ∞}
  → (p ⊕ q) >>= f ~[ i ] (p >>= f) ⊕ (q >>= f)
~i⊕-distr p q = ~imk CT.~irefl

≲i∅->>= :  ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} {f : A → CCTree E B ∞} → ∅ >>= f ≲[ i ] ∅
≲i∅->>= = ≲imk CT.≲irefl

~i∅->>= :  ∀ {E A B i} {{_ : Concurrent E}} {f : A → CCTree E B ∞} → ∅ >>= f ~[ i ] ∅
~i∅->>= = ~imk CT.~irefl


-------------------
-- parallel laws --
-------------------

≲ireturn-∥⃗ : ∀ {E A B i} {{_ : Ord B}} {{_ : Concurrent E}} {v : A} {p : CCTree E B ∞} 
  → return v ∥⃗ p ≲[ i ] p
≲ireturn-∥⃗ = ≲imk CT.≲ireturn-∥⃗

~ireturn-∥⃗ : ∀ {E A B i} {{_ : Concurrent E}} {v : A} {p : CCTree E B ∞} 
  → return v ∥⃗ p ~[ i ] p
~ireturn-∥⃗ = ~imk CT.~ireturn-∥⃗


≲i∥⃗->>= : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} {p : CCTree E A ∞} {q : CCTree E B ∞} {f : B → CCTree E C ∞}
  → (p ∥⃗ q) >>= f ≲[ i ] p ∥⃗ (q >>= f)
≲i∥⃗->>= {q = q} {f} = ≲imk CT.≲irefl

~i∥⃗->>= : ∀ {E A B C i} {{_ : Concurrent E}} {p : CCTree E A ∞} {q : CCTree E B ∞} {f : B → CCTree E C ∞}
  → (p ∥⃗ q) >>= f ~[ i ] p ∥⃗ (q >>= f)
~i∥⃗->>= {q = q} {f} = ~imk CT.~irefl


≲i∥⃗-cong : ∀ {E A B i} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q q' : CCTree E B ∞}
  → p ≲[ i ] p' → q ≲[ i ] q' → p ∥⃗ q ≲[ i ] p' ∥⃗ q'
≲i∥⃗-cong (≲imk b1) (≲imk b2) = ≲imk (CT.≲i∥⃗-cong b1 b2)

~i∥⃗-cong : ∀ {E A B i} {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q q' : CCTree E B ∞}
  → p ~[ i ] p' → q ~[ i ] q' → p ∥⃗ q ~[ i ] p' ∥⃗ q'
~i∥⃗-cong (≲imk b1) (≲imk b2) = ~imk (CT.~i∥⃗-cong b1 b2)


≲i∥⃗-cong-l : ∀ {E A B i} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q : CCTree E B ∞}
  → p ≲[ i ] p' → p ∥⃗ q ≲[ i ] p' ∥⃗  q
≲i∥⃗-cong-l b = ≲i∥⃗-cong b ≲irefl

~i∥⃗-cong-l : ∀ {E A B i} {{_ : Concurrent E}} {p p' : CCTree E A ∞}{q : CCTree E B ∞}
  → p ~[ i ] p' → p ∥⃗ q ~[ i ] p' ∥⃗  q
~i∥⃗-cong-l b = ~i∥⃗-cong b ~irefl

≲i∥⃗-cong-r : ∀ {E A B i}  {{_ : Ord B}} {{_ : Concurrent E}} {p : CCTree E A ∞}{q q' : CCTree E B ∞}
  → q ≲[ i ] q' → p ∥⃗ q ≲[ i ] p ∥⃗ q'
≲i∥⃗-cong-r b = ≲i∥⃗-cong {{≡-Ord}} ~irefl b

~i∥⃗-cong-r : ∀ {E A B i} {{_ : Concurrent E}} {p : CCTree E A ∞}{q q' : CCTree E B ∞}
  → q ~[ i ] q' → p ∥⃗ q ~[ i ] p ∥⃗ q'
~i∥⃗-cong-r b = ~i∥⃗-cong ~irefl b


~icong' : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞) {k : A → CTree E B ∞} {k' : A → CTree E C ∞}
  (b : ∀ x → k x CT.>> CT.now tt CT.~[ i ] k' x CT.>> CT.now tt)
  → ⟦ p ⟧ k CT.>> CT.now tt CT.~[ i ] ⟦ p ⟧ k' CT.>> CT.now tt
~icong' p b = CT.~itrans (~icong-map p {f = λ _ → tt}) (CT.~itrans (~icong p b) (CT.~isym (~icong-map p {f = λ _ → tt})))


~icont : ∀ {E A B i} {{_ : Concurrent E}} (p : CCTree E A ∞) (f : A → B) →
         ⟦ p ⟧ CT.now  CT.>> CT.now tt CT.~[ i ] (⟦ p ⟧ (λ r → CT.now (f r))) CT.>> CT.now tt
~icont p f = CT.~itrans (~icong-map p) (CT.~isym (~icong-map p))


~i∥⃗-map-l : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → C}
  → p ∥⃗ q ~[ i ]  map f p ∥⃗ q
~i∥⃗-map-l p q {f} = ~imk (CT.~itrans (CT.~itrans (CT.~i∥⃗-map-l (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.return) {f = λ x → tt})
  (CT.~i∥⃗-cong-l  (~icont p f ))) (CT.~isym ( CT.~i∥⃗-map-l (⟦ p ⟧ (λ r → CT.now (f r))) (⟦ q ⟧ CT.return) {f = λ x → tt})))


≲i∥⃗-map-l : ∀ {E A B C i} {{_ : Ord B}} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → C}
  → p ∥⃗ q ≲[ i ]  map f p ∥⃗ q
≲i∥⃗-map-l p q = ~i-≲i (~i∥⃗-map-l p q)

~i∥⃗-map : ∀ {E A A' B B' i} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → A'} {g : B → B'}
  → map g (p ∥⃗ q) ~[ i ]  map f p ∥⃗ map g q
~i∥⃗-map p q  = ~itrans (~i∥⃗->>= {p = p} {q = q}) (~i∥⃗-map-l p _)

≲i∥⃗-map : ∀ {E A A' B B' i} {{_ : Ord B'}} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) {f : A → A'} {g : B → B'}
  → map g (p ∥⃗ q) ≲[ i ]  map f p ∥⃗ map g q
≲i∥⃗-map p q  = ~i-≲i (~i∥⃗-map p q)

~i∥⃗-assoc : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] p ∥⃗ (q ∥⃗ r)
~i∥⃗-assoc p q r = ~imk (CT.~i∥⃗-assoc (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.return) (⟦ r ⟧ CT.return))

≲i∥⃗-assoc : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ≲[ i ] p ∥⃗ (q ∥⃗ r)
≲i∥⃗-assoc p q r = ~i-≲i (~i∥⃗-assoc p q r)


~i∥⃗-comm : ∀ {E A B C i} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ~[ i ] (q ∥⃗ p) ∥⃗ r
~i∥⃗-comm p q r = ~imk (CT.~i∥⃗-comm (⟦ p ⟧ CT.now) (⟦ q ⟧ CT.now) (⟦ r ⟧ CT.return))

≲i∥⃗-comm : ∀ {E A B C i} {{_ : Ord C}} {{_ : Concurrent E}} (p : CCTree E A ∞) (q : CCTree E B ∞) (r : CCTree E C ∞)
  → (p ∥⃗ q) ∥⃗ r ≲[ i ] (q ∥⃗ p) ∥⃗ r
≲i∥⃗-comm p q r = ~i-≲i (~i∥⃗-comm p q r)

------------
-- interp --
------------


≲iinterpSt-cong : ∀ {E F A S i} {{_ : Ord A}} {{_ : Concurrent E}} {{_ : Concurrent F}}
  {p q : CCTree E A ∞} {st : S} {f : ∀ {B} → S → E B → CCTree F (B × S) ∞}
  → p ≲[ i ] q → interpSt st f p ≲[ i ] interpSt st f q
≲iinterpSt-cong (≲imk b) = ≲imk (CT.≲i>>=-cong-l (CT.≲iinterpSt-cong b) CT.≲i⊑)

~iinterpSt-cong : ∀ {E F A S i} {{_ : Concurrent E}} {{_ : Concurrent F}} {p q : CCTree E A ∞}
  {st : S} {f : ∀ {B} → S → E B → CCTree F (B × S) ∞}
  → p ~[ i ] q → interpSt st f p ~[ i ] interpSt st f q
~iinterpSt-cong {f = f} = ≲iinterpSt-cong {{≡-Ord}} {f = f}


~iinterpSt-map : ∀ {E F A B S i} {{_ : Concurrent E}} {{_ : Concurrent F}} {p : CCTree E A ∞}
  {st : S} {f : ∀ {B} → S → E B → CCTree F (B × S) ∞}
  (g : A → B) → map g (interpSt st f p) ~[ i ] interpSt st f (map g p)
~iinterpSt-map {p = p}{st}{f} g = ~imk (CT.~itrans
  (CT.~isym ((CT.~imap->>= (CT.interpSt st (λ s e → ⟦ f s e ⟧ CT.now) (⟦ p ⟧ CT.now)))  {k = g} {l = CT.return}))
  (CT.~i>>=-cong-l {p = CT.map g (CT.interpSt st (λ s e → ⟦ f s e ⟧ CT.now) (⟦ p ⟧ CT.now))↑} {q = CT.interpSt st (λ s e → ⟦ f s e ⟧ CT.now) (⟦ p ⟧ (λ r → CT.now (g r)))↑}
  ( CT.~itrans (CT.~iinterpSt-map (⟦ p ⟧ CT.now) g) ((CT.~iinterpSt-cong (~icong-map p)))) {k = CT.return}))

≲iinterpSt-map : ∀ {E F A B S i} {{_ : Ord B}} {{_ : Concurrent E}} {{_ : Concurrent F}} {p : CCTree E A ∞}
  {st : S} {f : ∀ {B} → S → E B → CCTree F (B × S) ∞}
  (g : A → B) → map g (interpSt st f p) ≲[ i ] interpSt st f (map g p)
≲iinterpSt-map {f = f} g = ~i-≲i (~iinterpSt-map {f = f} g)
