{-# OPTIONS --copatterns --sized-types --guardedness --large-indices #-}

-------------------------------------------------------------------------
-- Skew indexed strong bisimilarity is defined as indexed
-- strong bisimiliarity that is conditional on the left-hand side term
-- being safe (= does not permit a trace that gets stuck).
-------------------------------------------------------------------------

module CTree.SkewIndexedBisimilarity where

open import Size

open import CTree.Definitions
open import CTree.Stuck
open import CTree.Safe
open import CTree.IndexedBisimilarity
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product renaming (map to map×)
open import Data.Unit
open import Data.Empty
open import Data.Fin hiding (_≤_ ; _<_ ; _≤?_)
open import Induction.WellFounded
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum hiding (map)
open import Relation.Binary.Construct.Closure.Transitive hiding (map; symmetric)


data NotStuckEff  {E : Set → Set} : Eff (Stuck E) → Set where
  notStuckEff : ∀ {A} {e : E A} → NotStuckEff (MkEff (notStuck e))


stuck-lsafe : ∀ {E A} {f : ⊥ → CTree⊥ E A ∞} → ¬ lsafe NotStuckEff (eff stuckEff f ↑)
stuck-lsafe ls with ls (⇒-eff stuckEff _)
... | isEffPredε .stuckEff ()

infix 3 _⊥~̂[_]_

infix 3 _⊥~[_]_

_⊥~̂[_]_ : ∀ {E A} → CTree⊥' E A → ℕ → CTree⊥' E A → Set₁
p ⊥~̂[ i ] q = p ~̂ (NotStuckEff) [ i ] q

_⊥~[_]_ : ∀ {E A} → CTree⊥ E A ∞ → ℕ → CTree⊥ E A ∞ → Set₁
p ⊥~[ i ] q = p ~ (NotStuckEff) [ i ] q

infix 3 _⊥≲̂[_]_

infix 3 _⊥≲[_]_

_⊥≲̂[_]_ : ∀ {E A} {{_ : Ord A}} → CTree⊥' E A → ℕ → CTree⊥' E A → Set₁
p ⊥≲̂[ i ] q = p ≲̂ (NotStuckEff) [ i ] q

_⊥≲[_]_ : ∀ {E A} {{_ : Ord A}} → CTree⊥ E A ∞ → ℕ → CTree⊥ E A ∞ → Set₁
p ⊥≲[ i ] q = p ≲ (NotStuckEff) [ i ] q






⊥~istuck : ∀ {i E A} {p : CTree⊥ E A ∞} {f} → eff stuckEff f ⊥~[ i ] p
⊥~istuck {zero} = ~izero
⊥~istuck {suc i} = ~istep (λ { ls tr → ⊥-elim (stuck-lsafe ls)})
         λ {ls tr → ⊥-elim (stuck-lsafe ls)}

⊥≲istuck : ∀ {i E A} {{_ : Ord A}} {p : CTree⊥ E A ∞} {f} → eff stuckEff f ⊥≲[ i ] p
⊥≲istuck = ~i-≲i ⊥~istuck

data safeP' {E A} (P : A → Set) : CTree⊥' E A → Set₁ where
  safeP↑ : ∀ {p} → safeP P p → safeP' P (p ↑)
  safeP-wait : ∀ {B} {c : B → CTree⊥ E A ∞} → (∀ r → safeP P (c r)) → safeP' P (wait B c)

safeP-lsafe : ∀ {E A P} {p : CTree⊥' E A} → safeP' P p → lsafe NotStuckEff p
safeP-lsafe (safeP-wait f) (⇒-inp r _) = isEffPredι r
safeP-lsafe (safeP↑ (spnow Pv)) (⇒-now v) = isEffPredρ v
safeP-lsafe (safeP↑ (splater x)) ⇒-later = isEffPredτ
safeP-lsafe (safeP↑ (spplus s s')) (⇒-⊕-l tr) = safeP-lsafe (safeP↑ s) tr
safeP-lsafe (safeP↑ (spplus s s')) (⇒-⊕-r tr) = safeP-lsafe (safeP↑ s') tr
safeP-lsafe (safeP↑ spempty ) ()
safeP-lsafe (safeP↑ (speff x)) (⇒-eff (notStuck e) _) = isEffPredε (notStuck e) notStuckEff

safeP⇒ : ∀ {E A P} {p : CTree⊥' E A} {l p'} → safeP' P p → p [ l ]⇒ p' → safeP' P p'
safeP⇒ (safeP↑ (spnow Pv)) (⇒-now v) = safeP↑ spempty
safeP⇒ (safeP↑ (splater x)) ⇒-later = safeP↑ (spforce x)
safeP⇒ (safeP↑ (spplus s s')) (⇒-⊕-l tr) = safeP⇒ (safeP↑ s) tr
safeP⇒ (safeP↑ (spplus s s')) (⇒-⊕-r tr) = safeP⇒ (safeP↑ s') tr
safeP⇒ (safeP↑ (speff x)) (⇒-eff (notStuck e) _) = safeP-wait x
safeP⇒ (safeP-wait p) (⇒-inp r _) = safeP↑ (p r)


⊥≲i-≲i : ∀ {E A i P} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → safeP P p → p ⊥≲[ i ] q → p ≲[ i ] q
⊥≲i-≲i s = prf (<×⇐-wf _)  (safeP↑ s)
  where prf : ∀ {i E A P} {{_ : Ord A}} {p q : CTree⊥' E A} → Acc (×-Lex _≡_ _<_ _⇐_) (i , p)
            → safeP' P p → p ⊥≲̂[ i ] q → p ≲̂[ i ] q
        prf {i = 0} _ _ _ = ≲izero
        prf {i = suc i}  {p = p} {q} (acc rec) s b = ≲istep' left right
          where left : ∀ {l p'} → p [ l ]⇒ p' → ∃[ l' ] ∃[ q' ] l ⊑ l' × q [ l' ]⇒ q' × p' ≲̂[ lsuc l i ] q'
                left trans with ≲ileft b (safeP-lsafe s) trans
                ... | l' , q' , leq , trans' , ibi'
                  = l' , q' , leq , trans' , prf (rec (recStep trans)) (safeP⇒ s trans) ibi'
                right : ∀ {l q'} → q [ l ]⇒ q' → ∃[ l' ] ∃[ p' ] l' ⊑ l × p [ l' ]⇒ p' × p' ≲̂[ lsuc l i ] q'
                right trans with ≲iright b (safeP-lsafe s) trans
                ... | l' , q' , leq , trans' , ibi'
                  = l' , q' , leq , trans' , prf (rec (recStep⊑ leq trans')) (safeP⇒ s trans') ibi'

-----------------------------
-- step-indexed version of --
-- Proposition 1 (ii)      --
-----------------------------

⊥~i-~i : ∀ {E A i P} {p q : CTree⊥ E A ∞} → safeP P p → p ⊥~[ i ] q → p ~[ i ] q
⊥~i-~i = ⊥≲i-≲i {{≡-Ord}}

-----------------------------
-- step-indexed version of --
-- Proposition 1 (i)       --
-----------------------------
~i-⊥~i : ∀ {E A i } {p q : CTree⊥ E A ∞} → p ~[ i ] q → p ⊥~[ i ] q
~i-⊥~i = ~ilift

-----------------------------
-- step-indexed version of --
-- Proposition 2 (i)       --
-----------------------------

⊥~i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊥~[ i ] q → p ⊥≲[ i ] q
⊥~i-⊥≲i = ~i-≲i


≲i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ≲[ i ] q → p ⊥≲[ i ] q
≲i-⊥≲i = ≲ilift

-----------------------------
-- step-indexed version of --
-- Proposition 2 (ii)      --
-----------------------------

⊥≲i-⊥~i : ∀ {E A i} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → (∀ {x y : A} → x ⊑ y → x ≡ y) → p ⊥≲[ i ] q → p ⊥~[ i ] q
⊥≲i-⊥~i = ≲i-~i

~i-⊥≲i : ∀ {E A i } {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ~[ i ] q → p ⊥≲[ i ] q
~i-⊥≲i le = ≲i-⊥≲i (~i-≲i le)


⊥~irefl : ∀ {i E A} {p : CTree⊥ E A ∞} → p ⊥~[ i ] p
⊥~irefl = ~irefl

⊥≲irefl : ∀ {i E A} {{_ : Ord A}} {p : CTree⊥ E A ∞} → p ⊥≲[ i ] p
⊥≲irefl = ≲irefl


⊥≲i⊑ : ∀ {i E A} {{_ : Ord A}} {v w : A} → v ⊑ w → return {E = Stuck E} v ⊥≲[ i ] return w
⊥≲i⊑ = ≲i⊑


⊥~itrans : ∀ {i E A} {p q r : CTree⊥ E A ∞} → p ⊥~[ i ] q → q ⊥~[ i ] r → p ⊥~[ i ] r
⊥~itrans = ~itrans

⊥≲itrans : ∀ {i E A} {{_ : Ord A}} {p q r : CTree⊥ E A ∞} → p ⊥≲[ i ] q → q ⊥≲[ i ] r → p ⊥≲[ i ] r
⊥≲itrans = ≲itrans

⊥~ilater : ∀ {i E A} {a b : ∞CTree⊥ E A ∞} → force a ⊥~[ i ] force b → later a ⊥~[ suc i ] later b
⊥~ilater = ~ilater

⊥≲ilater : ∀ {i E A} {{_ : Ord A}} {a b : ∞CTree⊥ E A ∞} → force a ⊥≲[ i ] force b → later a ⊥≲[ suc i ] later b
⊥≲ilater = ≲ilater

⊥~izero : ∀ {E A} {a b : CTree⊥ E A ∞} → a ⊥~[ 0 ] b
⊥~izero = ~izero

⊥≲izero : ∀ {E A} {{_ : Ord A}} {a b : CTree⊥ E A ∞} → a ⊥≲[ 0 ] b
⊥≲izero = ≲izero

⊥~ieff : ∀{E A B i} {c d : B → CTree⊥ E A ∞ } (e : (Stuck E) B) → (∀ x → c x ⊥~[ i ] d x) → eff e c ⊥~[ i ] eff e d
⊥~ieff = ~ieff

⊥≲ieff : ∀{E A B i} {{_ : Ord A}} {c d : B → CTree⊥ E A ∞ } (e : (Stuck E) B) → (∀ x → c x ⊥≲[ i ] d x) → eff e c ⊥≲[ i ] eff e d
⊥≲ieff = ≲ieff


~istuck-refl : ∀ {i E A}{f g : ⊥ → CTree⊥ E A ∞} → eff stuckEff f ~[ i ] eff stuckEff g
~istuck-refl = ~ieff stuckEff (λ x → ⊥-elim x)

≲istuck-refl : ∀ {i E A} {{_ : Ord A}} {f g : ⊥ → CTree⊥ E A ∞} → eff stuckEff f ≲[ i ] eff stuckEff g
≲istuck-refl = ≲ieff stuckEff (λ x → ⊥-elim x)



⊥~istuck-⊕-l : ∀ {i E B} {p q : CTree⊥ E B ∞}  {f} → eff stuckEff f ⊕ p ⊥~[ i ] q
⊥~istuck-⊕-l = ~ilsafe λ ls → stuck-lsafe (⊕-lsafe-l ls)

⊥≲istuck-⊕-l : ∀ {i E B} {{_ : Ord B}} {p q : CTree⊥ E B ∞}  {f} → eff stuckEff f ⊕ p ⊥≲[ i ] q
⊥≲istuck-⊕-l = ~i-≲i ⊥~istuck-⊕-l

⊥~istuck-⊕-r : ∀ {i E B} {p q : CTree⊥ E B ∞} {f} → p ⊕ eff stuckEff f ⊥~[ i ] q
⊥~istuck-⊕-r = ~ilsafe λ ls → stuck-lsafe (⊕-lsafe-r ls)

⊥≲istuck-⊕-r : ∀ {i E B} {{_ : Ord B}} {p q : CTree⊥ E B ∞} {f} → p ⊕ eff stuckEff f ⊥≲[ i ] q
⊥≲istuck-⊕-r = ~i-≲i ⊥~istuck-⊕-r

⊥~i>>=-assoc : ∀{i A B C E} (p : CTree⊥ E A ∞)
                 {k : A → CTree⊥ E B ∞}{l : B → CTree⊥ E C ∞} →
                 ((p >>= k) >>= l) ⊥~[ i ] (p >>= λ a → k a >>= l)
⊥~i>>=-assoc =  ~i>>=-assoc

⊥≲i>>=-assoc : ∀{i A B C E} {{_ : Ord C}} (p : CTree⊥ E A ∞)
                 {k : A → CTree⊥ E B ∞}{l : B → CTree⊥ E C ∞} →
                 ((p >>= k) >>= l) ⊥≲[ i ] (p >>= λ a → k a >>= l)
⊥≲i>>=-assoc =  ≲i>>=-assoc

⊥~i>>=-return : ∀ {E A i} {p : CTree⊥ E A ∞}  → (p >>= return) ⊥~[ i ] p
⊥~i>>=-return =  ~i>>=-return

⊥≲i>>=-return : ∀ {E A i} {{_ : Ord A}} {p : CTree⊥ E A ∞}  → (p >>= return) ⊥≲[ i ] p
⊥≲i>>=-return = ≲i>>=-return


⊥~i-return->>= : ∀ {E A B} {i} {x : A} {f : A → CTree⊥ E B ∞}  → (return x >>= f) ⊥~[ i ] f x
⊥~i-return->>= {f = f} = ~ireturn->>= {f = f}

⊥≲i-return->>= : ∀ {E A B} {{_ : Ord B}} {i} {x : A} {f : A → CTree⊥ E B ∞}  → (return x >>= f) ⊥≲[ i ] f x
⊥≲i-return->>= {f = f} = ≲ireturn->>= {f = f}


⊥~i⊕-cong : ∀ {E A i} {p q p' q' : CTree⊥ E A ∞} → p ⊥~[ i ] p'
  → q ⊥~[ i ] q' → p ⊕ q ⊥~[ i ] p' ⊕ q'
⊥~i⊕-cong = ~i⊕-cong

⊥≲i⊕-cong : ∀ {E A i} {{_ : Ord A}} {p q p' q' : CTree⊥ E A ∞} → p ⊥≲[ i ] p'
  → q ⊥≲[ i ] q' → p ⊕ q ⊥≲[ i ] p' ⊕ q'
⊥≲i⊕-cong = ≲i⊕-cong


⊥~i⊕-cong-r : ∀ {E A i} {p q q' : CTree⊥ E A ∞} → q ⊥~[ i ] q' → p ⊕ q ⊥~[ i ] p ⊕ q'
⊥~i⊕-cong-r = ~i⊕-cong-r

⊥≲i⊕-cong-r : ∀ {E A i} {{_ : Ord A}} {p q q' : CTree⊥ E A ∞} → q ⊥≲[ i ] q' → p ⊕ q ⊥≲[ i ] p ⊕ q'
⊥≲i⊕-cong-r = ≲i⊕-cong-r


⊥~idown : ∀ {E A i j} {a b : CTree⊥ E A ∞} → j ≤ i → a ⊥~[ i ] b → a ⊥~[ j ] b
⊥~idown = ~idown

⊥≲idown : ∀ {E A i j} {{_ : Ord A}} {a b : CTree⊥ E A ∞} → j ≤ i → a ⊥≲[ i ] b → a ⊥≲[ j ] b
⊥≲idown = ≲idown

⊥~isuc : ∀ {E A i} {a b : CTree⊥ E A ∞} → a ⊥~[ suc i ] b → a ⊥~[ i ] b
⊥~isuc = ~isuc

⊥≲isuc : ∀ {E A i} {{_ : Ord A}} {a b : CTree⊥ E A ∞} → a ⊥≲[ suc i ] b → a ⊥≲[ i ] b
⊥≲isuc = ≲isuc


⊥~i⊕-cong-l : ∀ {E A i} {p q p' : CTree⊥ E A ∞} → p ⊥~[ i ] p' → p ⊕ q ⊥~[ i ] p' ⊕ q
⊥~i⊕-cong-l = ~i⊕-cong-l

⊥≲i⊕-cong-l : ∀ {E A i} {{_ : Ord A}} {p q p' : CTree⊥ E A ∞} → p ⊥≲[ i ] p' → p ⊕ q ⊥≲[ i ] p' ⊕ q
⊥≲i⊕-cong-l = ≲i⊕-cong-l


⊥~i>>=-cong-r : ∀ {i E A B}  (a : CTree⊥ E A ∞)
            {k l : A → CTree⊥ E B ∞} (h : ∀ a → (k a) ⊥~[ i ] (l a)) →
            (a >>= k) ⊥~[ i ] (a >>= l)   
⊥~i>>=-cong-r = ~i>>=-cong-r

⊥≲i>>=-cong-r : ∀ {i E A B} {{_ : Ord B}} (a : CTree⊥ E A ∞)
            {k l : A → CTree⊥ E B ∞} (h : ∀ a → (k a) ⊥≲[ i ] (l a)) →
            (a >>= k) ⊥≲[ i ] (a >>= l)   
⊥≲i>>=-cong-r = ≲i>>=-cong-r


⊥~i>>=-cong-l : ∀ {i E A B}  {a b : CTree⊥ E A ∞} (eq : a ⊥~[ i ] b)
            {k : A → CTree⊥ E B ∞} →
            (a >>= k) ⊥~[ i ] (b >>= k)
⊥~i>>=-cong-l = ~i>>=-cong-l

⊥≲i>>=-cong-l : ∀ {i E A B} {{_ : Ord A}} {{_ : Ord B}}  {a b : CTree⊥ E A ∞} (eq : a ⊥≲[ i ] b)
            {k : A → CTree⊥ E B ∞} →
            (h : ∀ {a b} → a ⊑ b → (k a) ⊥≲[ i ] (k b)) →
            (a >>= k) ⊥≲[ i ] (b >>= k)
⊥≲i>>=-cong-l = ≲i>>=-cong-l


⊥≲i>>=-cong : ∀ {i E A B} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥' E A} (b : p ⊥≲̂[ i ] q)
              {k k' : A → CTree⊥ E B ∞} →
              (h : ∀ {a b} → a ⊑ b → (k a) ⊥≲[ i ] (k' b)) →
              (p >>=' k) ⊥≲̂[ i ] (q >>=' k')
⊥≲i>>=-cong = ≲i>>=-cong

⊥~i>>=-cong : ∀ {i E A B} {p q : CTree⊥' E A} (b : p ⊥~̂[ i ] q)
              {k k' : A → CTree⊥ E B ∞} →
              (h : ∀ a → (k a) ⊥~[ i ] (k' a)) →
              (p >>=' k) ⊥~̂[ i ] (q >>=' k')
⊥~i>>=-cong = ~i>>=-cong


⊥≲imap-cong : ∀ {i E A B} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥' E A}
             (b : p ⊥≲̂[ i ] q) → {f : A → B} → (le : ∀ {a b} → a ⊑ b → f a ⊑ f b) → map' f p ⊥≲̂[ i ] map' f q
⊥≲imap-cong = ≲imap-cong

⊥~imap-cong : ∀ {i E A B} {p q : CTree⊥' E A}
             (b : p ⊥~̂[ i ] q) → {f : A → B} → map' f p ⊥~̂[ i ] map' f q
⊥~imap-cong = ~imap-cong

-----------------------------
-- step-indexed version of --
-- Corollary 3             --
-----------------------------

⊥≲i-~i : ∀ {E A B P i} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree⊥ E A ∞} {f : A → B} 
  → safeP P p → (∀ {x y : B} → x ⊑ y → x ≡ y) → (∀ {a b} → a ⊑ b → f a ⊑ f b) → p ⊥≲[ i ] q → map f p ~[ i ] map f q
⊥≲i-~i {i = i} {p = p} {q} {f} S ⊑-≡ f⊑ le = ≲i-~i ⊑-≡ ≲map
  where ⊥≲map : map f p ⊥≲[ i ] map f q
        ⊥≲map = ⊥≲imap-cong le f⊑
        ≲map : map f p ≲[ i ] map f q
        ≲map = ⊥≲i-≲i (safeP-map S (λ p → tt)) ⊥≲map

open InterpStep

interpSt⊥' : ∀ {E F A S} → S → (∀ {B} → S → E B → CTree⊥ F (B × S) ∞) → CTree⊥' E A → CTree⊥' F A
interpSt⊥' st f p = interpSt' st (interpMap⊥ f) p

effFree-NotStuckEff : ∀ {E F A} {l : label (Stuck E) A} {l' : label (Stuck F) A} → effFree l l' → NotStuckEff ?? l'
effFree-NotStuckEff effFreeρ = isEffPredρ _
effFree-NotStuckEff effFreeι = isEffPredι _
effFree-NotStuckEff effFreeτ = isEffPredτ

interpSt⊥-lsafe : ∀ {E F A S} {p : CTree⊥' E A} {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  → lsafe NotStuckEff (interpSt⊥' st f p) → lsafe NotStuckEff p
interpSt⊥-lsafe ls {l = ⟨ ε stuckEff ⟩} (⇒-eff .stuckEff c) = ⊥-elim (stuck-lsafe ls)
interpSt⊥-lsafe ls {l = ⟨ ε stuckEff ⟩} (⇒-⊕-l tr) = interpSt⊥-lsafe (⊕-lsafe-l ls) tr
interpSt⊥-lsafe ls {l = ⟨ ε stuckEff ⟩} (⇒-⊕-r tr) = interpSt⊥-lsafe (⊕-lsafe-r ls) tr
interpSt⊥-lsafe ls {l = ⟨ ε (notStuck x) ⟩} tr = isEffPredε (notStuck x) notStuckEff
interpSt⊥-lsafe ls {l = ⟨ ι x ⟩} tr = isEffPredι x
interpSt⊥-lsafe ls {l = ⟨ ρ x ⟩} tr = isEffPredρ x
interpSt⊥-lsafe ls {l = τ} tr = isEffPredτ


interpSt-lsafe : ∀ {E F L A B S c} {e : E B} {p : CTree' E A} {st : S}
               {f : ∀ {B} → S → E B → CTree F (B × S) ∞} →
               lsafe L (interpSt' st f p) → p [ ⟨ ε e ⟩ ]⇒ wait B c → lsafe L ((f st e >>= (λ (x , s') → interpSt s' f (c x))) ↑)
interpSt-lsafe ls tr tr' = ls (interpSt-eff tr tr')


⊥≲iinterpSt⊥-cong' : ∀ {i E F A S} {{_ : Ord A}} {p q : CTree⊥' E A} {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  → p ⊥≲̂[ i ] q → interpSt⊥' st f p ⊥≲̂[ i ] interpSt⊥' st f q
⊥≲iinterpSt⊥-cong' = prf (<×⇐⁺-wf _) where
  prf : ∀ {i E F A S} {{_ : Ord A}} {p q : CTree⊥' E A} {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
    (ac : Acc (×-Lex _≡_ _<_ _⇐⁺_) (i , p)) → p ⊥≲̂[ i ] q → interpSt⊥' st f p ⊥≲̂[ i ] interpSt⊥' st f q
  prf {zero} _ bi = ≲izero
  prf {suc i} {p = p} {q} {st} {f} (acc rec) bi = ≲istep left right where
    left : lsafe NotStuckEff (interpSt⊥' st f p) → ∀ {l fp'} → interpSt⊥' st f p [ l ]⇒ fp' → 
      ∃[ l' ] ∃[ fq' ] l ⊑ l' × interpSt⊥' st f q [ l' ]⇒ fq' × fp' ⊥≲̂[ lsuc l i ] fq'
    left ls tr with interpSt-step {p = p} tr
    ... | inj₁ (p' , l' , ef , tr' , refl) rewrite effFree-lsuc {i = i} ef with ≲ileft bi (interpSt⊥-lsafe ls) tr'
    ... | l' , q' , leq , tr'' , bi' with (⊑-effFree leq ef)
    ... | l'' , leq' , ef' = l'' , _ , leq'  , interpSt-effFree ef' tr'' , prf (rec (recStep⁺ tr')) bi'
    left ls tr | inj₂ (B , stuckEff , c , tr1 , tr2)
      with (isEffPredε .stuckEff ()) ← interpSt⊥-lsafe ls tr1
    left ls tr | inj₂ (B , notStuck e , c , tr1 , tr2)
      with l' , wc' , ⊑ε _ , tr1' , bi1 ← ≲ileft bi (interpSt⊥-lsafe ls) tr1 with c' , refl ← ⇒-ε-wait tr1'
      with l' , fq' , leq , tr2' , bi2 ← ≲ileft (≲i>>=-cong-r (f st e)  (λ (x , s') →
           prf (rec (inj₂ (refl , (-, ⇒-inp x c) ∷ [ -, tr1 ] ))) (≲iwait' bi1 x))) (interpSt-lsafe ls tr1) tr2
           = -, -, leq , interpSt-eff tr1' tr2' , bi2    
    right : lsafe NotStuckEff (interpSt⊥' st f p) → ∀ {l fq'} → interpSt⊥' st f q [ l ]⇒ fq' → 
      ∃[ l' ] ∃[ fp' ] l' ⊑ l × interpSt⊥' st f p [ l' ]⇒ fp' × fp' ⊥≲̂[ lsuc l i ] fq'
    right ls tr with interpSt-step {p = q} tr
    ... | inj₁ (p' , l' , ef , tr' , refl) rewrite effFree-lsuc {i = i} ef with ≲iright bi (interpSt⊥-lsafe ls) tr'
    ... | l' , q' , leq , tr'' , bi' with (⊑-effFree' leq ef)
    ... | l'' , leq' , ef' = l'' , _ , leq' , interpSt-effFree ef' tr'' , prf (rec (recStep⊑⁺ leq tr'')) bi'
    right ls tr | inj₂ (B , stuckEff , c , tr1 , tr2)
      with l' , wc' , ⊑ε _ , tr1' , bi1 ← ≲iright bi (interpSt⊥-lsafe ls) tr1
      with (isEffPredε .stuckEff ()) ← interpSt⊥-lsafe ls tr1'
    right ls tr | inj₂ (B , notStuck e , c , tr1 , tr2)
      with l' , wc , ⊑ε _ , tr1' , bi1 ← ≲iright bi (interpSt⊥-lsafe ls) tr1 with c , refl ← ⇒-ε-wait tr1'
      with l'' , fp' , leq , tr2' , bi2 ← ≲iright (≲i>>=-cong-r (f st e)  (λ (x , s') →
           prf (rec (inj₂ (refl , (-, ⇒-inp x c) ∷ [ -, tr1' ] ))) (≲iwait' bi1 x))) (interpSt-lsafe ls tr1') tr2
           = -, -, leq , interpSt-eff tr1' tr2' , bi2

⊥~iinterpSt⊥-cong' : ∀ {i E F A S} {p q : CTree⊥' E A} {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  → p ⊥~̂[ i ] q → interpSt⊥' st f p ⊥~̂[ i ] interpSt⊥' st f q
⊥~iinterpSt⊥-cong' = ⊥≲iinterpSt⊥-cong' {{≡-Ord}}



⊥~iinterpSt⊥-cong : ∀ {E F A S i} {p q : CTree⊥ E A ∞} {st : S}
  {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  → p ⊥~[ i ] q → interpSt⊥ st f p ⊥~[ i ] interpSt⊥ st f q
⊥~iinterpSt⊥-cong = ⊥~iinterpSt⊥-cong'

⊥≲iinterpSt⊥-cong : ∀ {E F A S i} {{_ : Ord A}} {p q : CTree⊥ E A ∞} {st : S}
  {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  → p ⊥≲[ i ] q → interpSt⊥ st f p ⊥≲[ i ] interpSt⊥ st f q
⊥≲iinterpSt⊥-cong = ⊥≲iinterpSt⊥-cong'


⊥~iinterpSt⊥-map : ∀ {i E F A B S} (p : CTree⊥ E A ∞) {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  (g : A → B) → map g (interpSt⊥ st f p) ⊥~[ i ] interpSt⊥ st f (map g p)
⊥~iinterpSt⊥-map {0} _ _ = ⊥~izero
⊥~iinterpSt⊥-map (now v) g = ⊥~irefl
⊥~iinterpSt⊥-map {suc i} (later p) g = ⊥~ilater (⊥~iinterpSt⊥-map {i} (force p) g)
⊥~iinterpSt⊥-map (p ⊕ q) g = ⊥~i⊕-cong (⊥~iinterpSt⊥-map p g) (⊥~iinterpSt⊥-map q g)
⊥~iinterpSt⊥-map ∅ g = ⊥~irefl
⊥~iinterpSt⊥-map (eff e c) {st} {f} g =
  ~itrans (~i>>=-assoc (interpMap⊥ f st e)) (~i>>=-cong-r (interpMap⊥ f st e) (λ x → ⊥~iinterpSt⊥-map (c _) g))

⊥≲iinterpSt⊥-map : ∀ {i E F A B S} {{_ : Ord B}} (p : CTree⊥ E A ∞) {st : S} {f : ∀ {B} → S → E B → CTree⊥ F (B × S) ∞}
  (g : A → B) → map g (interpSt⊥ st f p) ⊥≲[ i ] interpSt⊥ st f (map g p)
⊥≲iinterpSt⊥-map p g = ~i-≲i (⊥~iinterpSt⊥-map p g)

ctree⊥-map : ∀ {E B} → ⊤ → E B → CTree⊥ E (B × ⊤) ∞
ctree⊥-map = interpMap (λ x → eff (notStuck x) now)

ctree⊥' : ∀ {E A} (p : CTree' E A) → CTree⊥' E A
ctree⊥' = interpSt' tt ctree⊥-map


ctree⊥ : ∀ {i E A} (p : CTree E A i) → CTree⊥ E A i
ctree⊥ = interpSt tt ctree⊥-map

∞ctree⊥ : ∀ {i E A} (p : ∞CTree E A i) → ∞CTree⊥ E A i
∞ctree⊥ = ∞interpSt tt ctree⊥-map

data stuckFree {E : Set → Set} {A : Set} : label (Stuck E) A → label E A → Set where
  stuckFreeε : ∀ {B} {e : E B} → stuckFree ⟨ ε (notStuck e) ⟩ ⟨ ε e ⟩
  stuckFreeι : ∀ {B} {r : B} → stuckFree ⟨ ι r ⟩ ⟨ ι r ⟩
  stuckFreeρ : ∀ {v} → stuckFree ⟨ ρ v ⟩ ⟨ ρ v ⟩
  stuckFreeτ : stuckFree τ τ

effFree-stuckFree : ∀ {E A} {l : label (Stuck E) A} {l'} → effFree l l' → stuckFree l l'
effFree-stuckFree effFreeρ = stuckFreeρ
effFree-stuckFree effFreeι = stuckFreeι
effFree-stuckFree effFreeτ = stuckFreeτ

ctree⊥-⇒ : ∀ { E A} {p : CTree' E A}{l q} → (ctree⊥' p) [ l ]⇒ q →
  ∃[ q' ] ∃[ l' ] stuckFree l l' × ctree⊥' q' ≡ q × p [ l' ]⇒ q'
ctree⊥-⇒ tr with interpSt-step tr
... | inj₁ (q' , l' , ef , tr' , eq) = q' , l' , effFree-stuckFree ef , eq , tr'
... | inj₂ (B , e , c , tr1 , ⇒-eff .(notStuck e) c') = 
  wait B c ,  ⟨ ε e ⟩ , stuckFreeε , refl , tr1

⊥-lab :  ∀ {E A} → label E A → label (Stuck E) A
⊥-lab ⟨ ε x ⟩ =  ⟨ ε (notStuck x) ⟩
⊥-lab ⟨ ι x ⟩ = ⟨ ι x ⟩
⊥-lab ⟨ ρ x ⟩ = ⟨ ρ x ⟩
⊥-lab τ = τ

ctree⊥-⇐ : ∀ { E A} {p : CTree' E A}{l q} → p [ l ]⇒ q → ctree⊥' p [ ⊥-lab l ]⇒ ctree⊥' q
ctree⊥-⇐ {l = ⟨ ε x ⟩} tr with ⇒-ε-wait tr
... | q , refl = interpSt-eff tr (⇒-eff (notStuck x) _)
ctree⊥-⇐ {l = ⟨ ι x ⟩} tr = interpSt-effFree effFreeι tr
ctree⊥-⇐ {l = ⟨ ρ x ⟩} tr = interpSt-effFree effFreeρ tr
ctree⊥-⇐ {l = τ} tr = interpSt-effFree effFreeτ tr


ctree⊥-now : ∀ { E A B} {p : CTree' E (A × B)} {v w} → ctree⊥' p ≡ (now (v , w) ↑) → p ≡ (now (v , w) ↑)
ctree⊥-now {p = now .(_ , _) ↑} refl = refl

instance
  StuckConcurrent : ∀ {E : Set → Set} → {{Concurrent E}} → Concurrent (Stuck E)
  _⇄_ ⦃ StuckConcurrent ⦄ stuckEff stuckEff = ∅
  _⇄_ ⦃ StuckConcurrent ⦄ stuckEff (notStuck x) = ∅
  _⇄_ ⦃ StuckConcurrent ⦄ (notStuck x) stuckEff = ∅
  _⇄_ ⦃ StuckConcurrent ⦄ (notStuck x) (notStuck y) = ctree⊥ (x ⇄ y)
  ⇄-sym ⦃ StuckConcurrent ⦄ (notStuck x) (notStuck x') {v} {w} tr with ctree⊥-⇒ tr
  ... | q' , .τ , stuckFreeτ , eq , tr' rewrite ctree⊥-now eq =  ctree⊥-⇐ (⇄-sym x x' {v} {w} tr')
  ⇄-step ⦃ StuckConcurrent ⦄ stuckEff stuckEff ()
  ⇄-step ⦃ StuckConcurrent ⦄ stuckEff (notStuck x) ()
  ⇄-step ⦃ StuckConcurrent ⦄ (notStuck x) (notStuck y) tr with ctree⊥-⇒ tr
  ... | q' , l' , sf , eq , tr' with ⇄-step x y tr'
  ⇄-step StuckConcurrent (notStuck x) (notStuck y) tr | q' , .τ , stuckFreeτ , refl , tr' | refl , v' , refl
    = refl ,  v' , refl

mutual
  safeP-ctree⊥ :  ∀ {E A} (p : CTree E A ∞) → safeP (λ _ → ⊤) (ctree⊥ p)
  safeP-ctree⊥ (now v) = spnow tt
  safeP-ctree⊥ (later p) = splater (∞safeP-ctree⊥ p)
  safeP-ctree⊥ (p ⊕ q) = spplus (safeP-ctree⊥ p) (safeP-ctree⊥ q)
  safeP-ctree⊥ ∅ = spempty
  safeP-ctree⊥ (eff e c) = speff (λ r → safeP-ctree⊥ (c r))

  ∞safeP-ctree⊥ :  ∀ {E A} (p : ∞CTree E A ∞) → ∞safeP (λ _ → ⊤) (∞ctree⊥ p)
  spforce (∞safeP-ctree⊥ p) = safeP-ctree⊥ (force p)

mutual
  safeP-∥ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} → safeP {i} {E} {A} P p → safeP {i} {E} {B} Q q
    → safeP {i} (λ { (x , y) → P x × Q y}) (p ∥ q)
  safeP-∥ sp sq = spplus (spplus (safeP-⦉ sp sq) (safeP-⦊ sp sq)) (safeP-⋈ sp sq)

  safeP-⦉ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} → safeP {i} {E} {A} P p → safeP {i} {E} {B} Q q
    → safeP {i} (λ { (x , y) → P x × Q y}) (p ⦉ q)
  safeP-⦉ (spnow x) sq = spempty
  safeP-⦉ (splater sp) sq = splater (safeP-∞∥ sp sq)
  safeP-⦉ (spplus sp1 sp2) sq = spplus (safeP-⦉ sp1 sq) (safeP-⦉ sp2 sq)
  safeP-⦉ spempty sq = spempty
  safeP-⦉ (speff sk) sq = speff (λ r → safeP-∥ (sk r) sq)
  
  safeP-⦊ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} → safeP {i} {E} {A} P p → safeP {i} {E} {B} Q q
    → safeP {i} (λ { (x , y) → P x × Q y}) (p ⦊ q)
  safeP-⦊ sp (spnow x) = spempty
  safeP-⦊ sp (splater sq) = splater (safeP-∥∞ sp sq)
  safeP-⦊ sp (spplus sq1 sq2) = spplus (safeP-⦊ sp sq1) (safeP-⦊ sp sq2)
  safeP-⦊ sp spempty = spempty
  safeP-⦊ sp (speff sk) = speff (λ r → safeP-∥ sp (sk r))

  safeP-⋈ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} →
    safeP {i} {E} {A} P p → safeP {i} {E} {B} Q q
    → safeP {i} (λ { (x , y) → P x × Q y}) (p ⋈ q)
  safeP-⋈ (spnow x) (spnow y) = spnow (x , y)
  safeP-⋈ (spnow x) (splater x₁) = spempty
  safeP-⋈ sp@(spnow x) (spplus sq1 sq2) = spplus (safeP-⋈ sp sq1) (safeP-⋈ sp sq2)
  safeP-⋈ (spnow x) spempty = spempty
  safeP-⋈ (spnow x) (speff x₁) = spempty
  safeP-⋈ (splater sp) (spnow x) = spempty
  safeP-⋈ (splater sp) (splater x) = spempty
  safeP-⋈ sp@(splater _) (spplus sq1 sq2) = spplus (safeP-⋈ sp sq1) (safeP-⋈ sp sq2)
  safeP-⋈ (splater sp) spempty = spempty
  safeP-⋈ (splater sp) (speff x) = spempty
  safeP-⋈ (spplus sp1 sp2) sq = spplus (safeP-⋈ sp1 sq) (safeP-⋈ sp2 sq)
  safeP-⋈ spempty (spnow x) = spempty
  safeP-⋈ spempty (splater x) = spempty
  safeP-⋈ sp@spempty (spplus sq1 sq2) = spplus (safeP-⋈ sp sq1) (safeP-⋈ sp sq2)
  safeP-⋈ spempty spempty = spempty
  safeP-⋈ spempty (speff x) = spempty
  safeP-⋈ (speff _) (spnow _) = spempty
  safeP-⋈ (speff _) (splater _) = spempty
  safeP-⋈ sp@(speff _) (spplus sq1 sq2) = spplus (safeP-⋈ sp sq1) (safeP-⋈ sp sq2)
  safeP-⋈ (speff _) spempty = spempty
  safeP-⋈ (speff {k = k1} {e = e1} sk1) (speff {k = k2} {e = e2} sk2) =
    safeP->>= {p = ctree⊥ (e1 ⇄ e2)} {P = λ _ → ⊤} (safeP-ctree⊥ (e1 ⇄ e2)) λ {v} _ → safeP-∥ (sk1 (proj₁ v)) (sk2 (proj₂ v))



  safeP-∞∥ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} → ∞safeP {i} {E} {A} P p → safeP {i} {E} {B} Q q
    → ∞safeP {i} (λ { (x , y) → P x × Q y}) (p ∞∥ q)
  spforce (safeP-∞∥ sp sq) = (safeP-∥ (spforce sp) sq)

  safeP-∥∞ : ∀ {i A B E p q} {P : A → Set} {Q : B → Set} {{_ : Concurrent E}} → safeP {i} {E} {A} P p → ∞safeP {i} {E} {B} Q q
    → ∞safeP {i} (λ { (x , y) → P x × Q y}) (p ∥∞ q)
  spforce (safeP-∥∞ sp sq) = (safeP-∥ sp (spforce sq))

  safeP-∥⃗ : ∀ {i A B E p q} {P : B → Set} {{_ : Concurrent E}} → safeP {i} {E} {A} (λ _ → ⊤) p → safeP {i} {E} {B} P q
    → safeP {i} P (p ∥⃗ q)
  safeP-∥⃗ sp sq = safeP-map (safeP-∥ sp sq) (λ Pv → proj₂ Pv)


⊥~ireturn-∥⃗ : ∀ {i A B E} {{_ : Concurrent E}} {v : A} {p : CTree⊥ E B ∞} 
  → return v ∥⃗ p ⊥~[ i ] p
⊥~ireturn-∥⃗ = ~ireturn-∥⃗

⊥≲ireturn-∥⃗ : ∀ {i A B E} {{_ : Ord B}} {{_ : Concurrent E}} {v : A} {p : CTree⊥ E B ∞} 
  → return v ∥⃗ p ⊥≲[ i ] p
⊥≲ireturn-∥⃗ = ≲ireturn-∥⃗


⊥≲i∥-cong : ∀ {i A B E} {{_ : Ord A}} {{_ : Ord B}} {{EC : Concurrent E}} {p p' : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → p ⊥≲[ i ] p' → q ⊥≲[ i ] q' → p ∥ q ⊥≲[ i ] p' ∥ q'
⊥≲i∥-cong {E = E} ≲p ≲q = ≲i∥-cong-gen ( λ tr → le tr)  ≲p ≲q
  where le : ∀ {A B} {e1 : Stuck E A} {e2 : Stuck E B} {p} → (e1 ⇄ e2) [ τ ]=> p → NotStuckEff (MkEff e1)
        le {e1 = stuckEff} {stuckEff} ()
        le {e1 = stuckEff} {notStuck x} ()
        le {e1 = notStuck x} tr = notStuckEff


⊥~i∥-cong : ∀ {i A B E} {{EC : Concurrent E}} {p p' : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → p ⊥~[ i ] p' → q ⊥~[ i ] q' → p ∥ q ⊥~[ i ] p' ∥ q'
⊥~i∥-cong ~p ~q = ≲i-weaken {{_}} {{≡-Ord}} (λ { (refl , refl) → refl}) (⊥≲i∥-cong {{≡-Ord}} {{≡-Ord}} ~p ~q)


⊥~i∥⃗-cong : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → p ⊥~[ i ] p' → q ⊥~[ i ] q' → p ∥⃗ q ⊥~[ i ] p' ∥⃗ q'
⊥~i∥⃗-cong ~p ~q = ~imap-cong (⊥~i∥-cong ~p ~q)


⊥≲i∥⃗-cong : ∀ {i A B E} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → p ⊥≲[ i ] p' → q ⊥≲[ i ] q' → p ∥⃗ q ⊥≲[ i ] p' ∥⃗ q'
⊥≲i∥⃗-cong ≲p ≲q = ≲imap-cong (⊥≲i∥-cong ≲p ≲q) proj₂

⊥~i∥⃗-cong-l : ∀ {i A B E} {{_ : Concurrent E}} {p p' : CTree⊥ E A ∞}{q : CTree⊥ E B ∞}
  → p ⊥~[ i ] p' → p ∥⃗ q ⊥~[ i ] p' ∥⃗  q
⊥~i∥⃗-cong-l b = ⊥~i∥⃗-cong b ~irefl

⊥≲i∥⃗-cong-l : ∀ {i A B E} {{_ : Ord A}} {{_ : Ord B}} {{_ : Concurrent E}} {p p' : CTree⊥ E A ∞}{q : CTree⊥ E B ∞}
  → p ⊥≲[ i ] p' → p ∥⃗ q ⊥≲[ i ] p' ∥⃗  q
⊥≲i∥⃗-cong-l b = ⊥≲i∥⃗-cong b ≲irefl

⊥~i∥⃗-cong-r : ∀ {i A B E} {{_ : Concurrent E}} {p : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → q ⊥~[ i ] q' → p ∥⃗ q ⊥~[ i ] p ∥⃗ q'
⊥~i∥⃗-cong-r b = ⊥~i∥⃗-cong ~irefl b

⊥≲i∥⃗-cong-r : ∀ {i A B E} {{_ : Ord B}} {{_ : Concurrent E}} {p : CTree⊥ E A ∞}{q q' : CTree⊥ E B ∞}
  → q ⊥≲[ i ] q' → p ∥⃗ q ⊥≲[ i ] p ∥⃗ q'
⊥≲i∥⃗-cong-r b = ⊥≲i∥⃗-cong {{≡-Ord}} ~irefl b


⊥~i∥⃗-map-r : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : B → C} 
  → map f (p ∥⃗ q) ⊥~[ i ] p ∥⃗ (map f q)
⊥~i∥⃗-map-r p q = ~i-⊥~i (~i∥⃗-map-r p q)


⊥≲i∥⃗-map-r : ∀ {i A B C E} {{_ : Ord C}} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : B → C} 
  → map f (p ∥⃗ q) ⊥≲[ i ] p ∥⃗ (map f q)
⊥≲i∥⃗-map-r p q = ≲i-⊥≲i (≲i∥⃗-map-r p q)


⊥~i∥⃗-map-r' : ∀ {i A B C D E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : B → C} {g : C → CTree⊥ E D ∞}
  → ((p ∥⃗ q) >>= (λ v → g (f v))) ⊥~[ i ] ((p ∥⃗ (map f q)) >>= g)
⊥~i∥⃗-map-r' p q = ~i-⊥~i (~i∥⃗-map-r' p q)


⊥≲i∥⃗-map-r' : ∀ {i A B C D E} {{_ : Ord D}} {{_ : Concurrent E}}
  (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : B → C} {g : C → CTree⊥ E D ∞}
  → ((p ∥⃗ q) >>= (λ v → g (f v))) ⊥≲[ i ] ((p ∥⃗ (map f q)) >>= g)
⊥≲i∥⃗-map-r' p q = ≲i-⊥≲i (≲i∥⃗-map-r' p q)

⊥~i∥⃗-map-l : ∀ {i A A' B E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'}
  → p ∥⃗ q ⊥~[ i ]  map f p ∥⃗ q
⊥~i∥⃗-map-l p q = ~i-⊥~i (~i∥⃗-map-l p q)


⊥≲i∥⃗-map-l : ∀ {i A A' B E} {{_ : Ord B}} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'}
  → p ∥⃗ q ⊥≲[ i ]  map f p ∥⃗ q
⊥≲i∥⃗-map-l p q = ≲i-⊥≲i (≲i∥⃗-map-l p q)


⊥~i∥⃗-comm : ∀ {i A B C E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) (r : CTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥~[ i ] (q ∥⃗ p) ∥⃗ r
⊥~i∥⃗-comm p q r = ~i-⊥~i (~i∥⃗-comm p q r)

⊥≲i∥⃗-comm : ∀ {i A B C E} {{_ : Ord C}} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) (r : CTree⊥ E C ∞)
  → (p ∥⃗ q) ∥⃗ r ⊥≲[ i ] (q ∥⃗ p) ∥⃗ r
⊥≲i∥⃗-comm p q r = ≲i-⊥≲i (≲i∥⃗-comm p q r)


⊥~i∥-map : ∀ {i A A' B B' E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'} {g : B → B'}
  → map (map× f g)  (p ∥ q) ⊥~[ i ] map f p ∥ map g q
⊥~i∥-map = ~i∥-map


⊥≲i∥-map : ∀ {i A A' B B' E} {{_ : Ord A'}} {{_ : Ord B'}} {{_ : Concurrent E}}
  (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'} {g : B → B'}
  → map (map× f g)  (p ∥ q) ⊥≲[ i ] map f p ∥ map g q
⊥≲i∥-map = ≲i∥-map



⊥~i∥⃗-map-l' : ∀ {i A A' B E} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'}
  → map f p ∥⃗ q ⊥~[ i ] p ∥⃗ q
⊥~i∥⃗-map-l' p q = ~ilift (~isym (~i∥⃗-map-l p q))


⊥≲i∥⃗-map-l' : ∀ {i A A' B E} {{_ : Ord B}} {{_ : Concurrent E}} (p : CTree⊥ E A ∞) (q : CTree⊥ E B ∞) {f : A → A'}
  → map f p ∥⃗ q ⊥≲[ i ] p ∥⃗ q
⊥≲i∥⃗-map-l' p q = ~i-≲i (⊥~i∥⃗-map-l' p q)


--------------------------
-- non-determinism laws --
--------------------------

⊥~i⊕-unit-l : ∀ {i E A} {p : CTree⊥ E A ∞} → ∅ ⊕ p ⊥~[ i ] p
⊥~i⊕-unit-l = ~i⊕-unit-l

⊥≲i⊕-unit-l : ∀ {i E A} {{_ : Ord A}} {p : CTree⊥ E A ∞} → ∅ ⊕ p ⊥≲[ i ] p
⊥≲i⊕-unit-l = ≲i⊕-unit-l

⊥~i⊕-unit-r : ∀ {i E A} {p : CTree⊥ E A ∞} → p ⊕ ∅ ⊥~[ i ] p
⊥~i⊕-unit-r = ~i⊕-unit-r

⊥≲i⊕-unit-r : ∀ {i E A} {{_ : Ord A}} {p : CTree⊥ E A ∞} → p ⊕ ∅ ⊥≲[ i ] p
⊥≲i⊕-unit-r = ≲i⊕-unit-r
 
⊥~i⊕-assoc : ∀ {i E A} {p q r : CTree⊥ E A ∞} → (p ⊕ q) ⊕ r ⊥~[ i ] p ⊕ (q ⊕ r)
⊥~i⊕-assoc = ~i⊕-assoc

⊥≲i⊕-assoc : ∀ {i E A} {{_ : Ord A}} {p q r : CTree⊥ E A ∞} → (p ⊕ q) ⊕ r ⊥≲[ i ] p ⊕ (q ⊕ r)
⊥≲i⊕-assoc = ≲i⊕-assoc

⊥~i⊕-idem : ∀ {i E A} {p : CTree⊥ E A ∞} → p ⊕ p ⊥~[ i ] p
⊥~i⊕-idem = ~i⊕-idem

⊥≲i⊕-idem : ∀ {i E A} {{_ : Ord A}} {p : CTree⊥ E A ∞} → p ⊕ p ⊥≲[ i ] p
⊥≲i⊕-idem = ≲i⊕-idem

⊥~i⊕-comm : ∀ {i E A} {p q : CTree⊥ E A ∞} → p ⊕ q ⊥~[ i ] q ⊕ p
⊥~i⊕-comm = ~i⊕-comm

⊥≲i⊕-comm : ∀ {i E A} {{_ : Ord A}} {p q : CTree⊥ E A ∞} → p ⊕ q ⊥≲[ i ] q ⊕ p
⊥≲i⊕-comm = ≲i⊕-comm

⊥~i⊕-distr : ∀ {i E A B} {p q : CTree⊥ E A ∞} {f : A → CTree⊥ E B ∞}
  → ((p ⊕ q) >>= f) ⊥~[ i ] (p >>= f) ⊕ (q >>= f)
⊥~i⊕-distr = ⊥~irefl

⊥≲i⊕-distr : ∀ {i E A B} {{_ : Ord B}} {p q : CTree⊥ E A ∞} {f : A → CTree⊥ E B ∞}
  → ((p ⊕ q) >>= f) ⊥≲[ i ] (p >>= f) ⊕ (q >>= f)
⊥≲i⊕-distr = ⊥≲irefl

⊥~iempty->>= : ∀ {i E A B} {f : A → CTree⊥ E B ∞} → (∅ >>= f) ⊥~[ i ] ∅
⊥~iempty->>=  = ⊥~irefl

⊥≲iempty->>= : ∀ {i E A B} {{_ : Ord B}} {f : A → CTree⊥ E B ∞} → (∅ >>= f) ⊥≲[ i ] ∅
⊥≲iempty->>=  = ⊥≲irefl


~iset-get : ∀ {E A i} {m : Memory A} {r : Reg} {v : A} 
  → get (m #[ r ← v ]) r ~[ i ] return {E = Stuck E} v
~iset-get {m = m} {r} {v} rewrite getSet {r = r} {v} {m} =  ~irefl

~iset-get->>= : ∀ {E A B i} {m : Memory A} {r : Reg} {v : A} {f : A → CTree⊥ E B ∞}
  → (get (m #[ r ← v ]) r >>= f) ~[ i ] f v
~iset-get->>= {m = m} {r} {v} rewrite getSet {r = r} {v} {m} =  ~irefl


⊥~iget : ∀ {A E} {{_ : Ord A}} {i} {r : Reg} {m m' : Memory A}
           → m ⊑ m' → get {E = E} m r ⊥~[ i ] get m' r
⊥~iget {r = r} {m = m} le with ⊑-get {r = r} {m = m}
... | le' with  m #[ r ]
... | nothing = ⊥~istuck
... | just x rewrite le' le refl = ⊥~irefl


⊥≲iget : ∀ {A E} {{_ : Ord A}} {i} {r : Reg} {m m' : Memory A}
           → m ⊑ m' → get {E = E} m r ⊥≲[ i ] get m' r
⊥≲iget le = ~i-≲i (⊥~iget le)


⊥~iget->>= : ∀ {A B E} {{_ : Ord A}}  {i} {r : Reg} {m m' : Memory A}
           {f : A → CTree⊥ E B ∞}
           → m ⊑ m' → get {E = E} m r >>= f ⊥~[ i ] get m' r >>= f
⊥~iget->>= {r = r} {m = m} le with ⊑-get {r = r} {m = m}
... | le' with  m #[ r ]
... | nothing = ⊥~istuck
... | just x rewrite le' le refl = ⊥~irefl

⊥≲iget->>= : ∀ {A B E} {{_ : Ord A}} {{_ : Ord B}} {i} {r : Reg} {m m' : Memory A}
           {f : A → CTree⊥ E B ∞}
           → m ⊑ m' → get {E = E} m r >>= f ⊥≲[ i ] get m' r >>= f
⊥≲iget->>= le = ~i-≲i (⊥~iget->>= le)



module ⊥~i-Calculation where

  _⊥~⟨_⟩_ : ∀ {E} {A : Set} {i} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞}
    {z : CTree⊥ E A ∞} → x ⊥~[ i ] y → y ⊥~[ i ] z → x ⊥~[ i ] z
  _⊥~⟨_⟩_ {_} x r eq =  ⊥~itrans r eq

  _~⟨_⟩_ : ∀ {E} {A : Set} {i} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} {z : CTree⊥ E A ∞} → x ~[ i ] y → y ⊥~[ i ] z → x ⊥~[ i ] z
  _~⟨_⟩_ {_} x r eq =  ⊥~itrans (~i-⊥~i r) eq


  _≡⟨⟩_ : ∀ {E} {A : Set} {i} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} → x ⊥~[ i ] y → x ⊥~[ i ] y
  _≡⟨⟩_  x eq = eq



  _∎ : ∀ {E} {A : Set} {i} (x : CTree⊥ E A ∞) → x ⊥~[ i ] x
  _∎  x = ⊥~irefl

  infix  3 _∎
  infixr 1 _⊥~⟨_⟩_
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_


module ⊥≲i-Calculation where

  _⊥≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞}
    {z : CTree⊥ E A ∞} → x ⊥≲[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _⊥≲⟨_⟩_ x r eq =  ⊥≲itrans r eq


  _⊥~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} {z : CTree⊥ E A ∞}
    → x ⊥~[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _⊥~⟨_⟩_ x r eq =  ⊥≲itrans (~i-≲i r) eq

  _~⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} {z : CTree⊥ E A ∞}
    → x ~[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _~⟨_⟩_ x r eq =  ⊥≲itrans (≲i-⊥≲i (~i-≲i r)) eq

  _≲⟨_⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} {z : CTree⊥ E A ∞}
    → x ≲[ i ] y → y ⊥≲[ i ] z → x ⊥≲[ i ] z
  _≲⟨_⟩_ {_} x r eq =  ⊥≲itrans (≲i-⊥≲i r) eq


  _≡⟨⟩_ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → ∀ {y : CTree⊥ E A ∞} → x ⊥≲[ i ] y → x ⊥≲[ i ] y
  _≡⟨⟩_  x eq = eq



  _∎ : ∀ {E A i} {{_ : Ord A}} (x : CTree⊥ E A ∞) → x ⊥≲[ i ] x
  _∎  x = ⊥≲irefl

  infix  3 _∎
  infixr 1 _⊥≲⟨_⟩_
  infixr 1 _≲⟨_⟩_
  infixr 1 _⊥~⟨_⟩_
  infixr 1 _~⟨_⟩_
  infixr 1 _≡⟨⟩_


