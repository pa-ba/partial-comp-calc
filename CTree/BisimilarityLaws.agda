{-# OPTIONS --sized-types #-}

---------------------------------------------------------------------
-- Monad and functor laws, and the congruence law for >>=, stated for
-- (ordered) bisimilarity rather than for its step-indexed
-- approximation. These are the laws exactly as section 3.3 of the
-- paper states them.
--
-- Every statement is parametric in the effect predicate L, so each law
-- instantiates to bisimilarity (L = AnyEff) and to skew bisimilarity
-- (L = NotStuckEff) alike; see CTree.SkewBisimilarity for the latter.

---------------------------------------------------------------------

module CTree.BisimilarityLaws where

open import CTree.Bisimilarity public
open import CTree.Definitions
open import CTree.IndexedBisimilarity
open import Preorder

open import Size
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality
open import Function using (id; _∘_)

private
  -- retFree relates a label only to itself
  retFree-≡ : ∀ {E A} {l l' : label E A} → retFree l l' → l ≡ l'
  retFree-≡ retFreeε = refl
  retFree-≡ retFreeι = refl
  retFree-≡ retFreeτ = refl

---------------------------------------------------------------------
-- Reflexivity and congruence for ⊕
---------------------------------------------------------------------

≲refl : ∀ {E L A i} {{O : Ord A}} {p : CTree' E A} → (p ≲̂ L ! p) {i}
≲left  (≲refl {{O}}) _ tr = _ , _ , ⊑-refl {{LabOrd {{O}}}} , tr , ≲refl
≲right (≲refl {{O}}) _ tr = _ , _ , ⊑-refl {{LabOrd {{O}}}} , tr , ≲refl

~refl : ∀ {E L A i} {p : CTree' E A} → (p ~̂ L ! p) {i}
~refl = ≲refl {{≡-Ord}}

≲⊕-cong : ∀ {E L A i} {{_ : Ord A}} {p1 p2 q1 q2 : CTree E A ∞}
  → (p1 ↑ ≲̂ L ! p2 ↑) {i} → (q1 ↑ ≲̂ L ! q2 ↑) {i}
  → ((p1 ⊕ q1) ↑ ≲̂ L ! (p2 ⊕ q2) ↑) {i}
≲left (≲⊕-cong bp bq) ls (⇒-⊕-l tr)
  with l' , r' , leq , tr' , b' ← ≲left bp (⊕-lsafe-l ls) tr = l' , r' , leq , ⇒-⊕-l tr' , b'
≲left (≲⊕-cong bp bq) ls (⇒-⊕-r tr)
  with l' , r' , leq , tr' , b' ← ≲left bq (⊕-lsafe-r ls) tr = l' , r' , leq , ⇒-⊕-r tr' , b'
≲right (≲⊕-cong bp bq) ls (⇒-⊕-l tr)
  with l' , r' , leq , tr' , b' ← ≲right bp (⊕-lsafe-l ls) tr = l' , r' , leq , ⇒-⊕-l tr' , b'
≲right (≲⊕-cong bp bq) ls (⇒-⊕-r tr)
  with l' , r' , leq , tr' , b' ← ≲right bq (⊕-lsafe-r ls) tr = l' , r' , leq , ⇒-⊕-r tr' , b'

~⊕-cong : ∀ {E L A i} {p1 p2 q1 q2 : CTree E A ∞}
  → (p1 ↑ ~̂ L ! p2 ↑) {i} → (q1 ↑ ~̂ L ! q2 ↑) {i}
  → ((p1 ⊕ q1) ↑ ~̂ L ! (p2 ⊕ q2) ↑) {i}
~⊕-cong = ≲⊕-cong {{≡-Ord}}

---------------------------------------------------------------------
-- Monad laws
---------------------------------------------------------------------

-- left identity: `return x >>= f` and `f x` are definitionally equal,
-- so the law is just reflexivity
≲return->>= : ∀ {E L A B i} {{_ : Ord B}} {x : A} {f : A → CTree E B ∞}
  → ((return x >>= f) ↑ ≲̂ L ! f x ↑) {i}
≲return->>= = ≲refl

~return->>= : ∀ {E L A B i} {x : A} {f : A → CTree E B ∞}
  → ((return x >>= f) ↑ ~̂ L ! f x ↑) {i}
~return->>= = ≲refl {{≡-Ord}}

-- right identity
≲>>='-return : ∀ {E L A i} {{O : Ord A}} {p : CTree' E A} → ((p >>=' return) ≲̂ L ! p) {i}
≲left (≲>>='-return {{O}} {p = p}) ls tr with >>=-step p return tr
... | inj₁ (v , tr1 , ⇒-now .v) = _ , _ , ⊑-refl {{LabOrd {{O}}}} , tr1 , ≲refl
... | inj₂ (l' , rf , p' , tr' , refl) rewrite retFree-≡ rf
      = _ , _ , ⊑-refl {{LabOrd {{O}}}} , tr' , ≲>>='-return
≲right (≲>>='-return {{O}} {p = p}) ls {l = ⟨ ρ v ⟩} tr rewrite ⇒-ρ-∅ tr
  = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step1 return tr (⇒-now v) , ≲refl
≲right (≲>>='-return {{O}} {p = p}) ls {l = ⟨ ε e ⟩} tr
  = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step2 p return retFreeε tr , ≲>>='-return
≲right (≲>>='-return {{O}} {p = p}) ls {l = ⟨ ι r ⟩} tr
  = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step2 p return retFreeι tr , ≲>>='-return
≲right (≲>>='-return {{O}} {p = p}) ls {l = τ} tr
  = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step2 p return retFreeτ tr , ≲>>='-return

≲>>=-return : ∀ {E L A i} {{_ : Ord A}} {p : CTree E A ∞} → ((p >>= return) ↑ ≲̂ L ! p ↑) {i}
≲>>=-return = ≲>>='-return

~>>=-return : ∀ {E L A i} {p : CTree E A ∞} → ((p >>= return) ↑ ~̂ L ! p ↑) {i}
~>>=-return = ≲>>=-return {{≡-Ord}}

-- associativity
≲>>='-assoc : ∀ {E L A B C i} {{O : Ord C}} (p : CTree' E A)
  {k : A → CTree E B ∞} {l : B → CTree E C ∞}
  → (((p >>=' k) >>=' l) ≲̂ L ! (p >>=' (λ a → k a >>= l))) {i}
≲left (≲>>='-assoc {{O}} p {k} {l}) ls tr with >>=-step (p >>=' k) l tr
... | inj₁ (v , tr1 , tr2) with >>=-step p k tr1
...   | inj₁ (u , trp , trk)
        = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step1 _ trp (>>=-step1 l trk tr2) , ≲refl
≲left (≲>>='-assoc {{O}} p {k} {l}) ls tr | inj₂ (l₁ , rf , r , tr1 , refl) with >>=-step p k tr1
...   | inj₁ (u , trp , trk)
        = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step1 _ trp (>>=-step2 (k u ↑) l rf trk) , ≲refl
...   | inj₂ (l₂ , rf2 , p₂ , trp , refl)
        = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step2 p _ (retFree-trans rf rf2) trp , ≲>>='-assoc p₂

≲right (≲>>='-assoc {{O}} p {k} {l}) ls tr with >>=-step p (λ a → k a >>= l) tr
... | inj₁ (u , trp , tr2) with >>=-step (k u ↑) l tr2
...   | inj₁ (v , trk , tr3)
        = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step1 l (>>=-step1 k trp trk) tr3 , ≲refl
...   | inj₂ (l₁ , rf , r , trk , refl)
        = _ , _ , ⊑-refl {{LabOrd {{O}}}} , >>=-step2 (p >>=' k) l rf (>>=-step1 k trp trk) , ≲refl
≲right (≲>>='-assoc {{O}} p {k} {l}) ls tr | inj₂ (l₁ , rf , p₁ , trp , refl)
      = _ , _ , ⊑-refl {{LabOrd {{O}}}}
      , >>=-step2 (p >>=' k) l (coerce-retFree rf) (>>=-step2 p k (coerce-retFree' rf) trp)
      , ≲>>='-assoc p₁

≲>>=-assoc : ∀ {E L A B C i} {{_ : Ord C}} (p : CTree E A ∞)
  {k : A → CTree E B ∞} {l : B → CTree E C ∞}
  → (((p >>= k) >>= l) ↑ ≲̂ L ! (p >>= (λ a → k a >>= l)) ↑) {i}
≲>>=-assoc p = ≲>>='-assoc (p ↑)

~>>=-assoc : ∀ {E L A B C i} (p : CTree E A ∞)
  {k : A → CTree E B ∞} {l : B → CTree E C ∞}
  → (((p >>= k) >>= l) ↑ ~̂ L ! (p >>= (λ a → k a >>= l)) ↑) {i}
~>>=-assoc = ≲>>=-assoc {{≡-Ord}}

---------------------------------------------------------------------
-- Congruence law for >>=
---------------------------------------------------------------------

≲>>='-cong : ∀ {E L A B i} {{OA : Ord A}} {{OB : Ord B}} {p q : CTree' E A}
  → (p ≲̂ L ! q) {i} → {k k' : A → CTree E B ∞}
  → (h : ∀ {a b} → a ⊑ b → (k a ↑ ≲̂ L ! k' b ↑) {∞})
  → ((p >>=' k) ≲̂ L ! (q >>=' k')) {i}
≲left (≲>>='-cong {{OA}} {{OB}} {p = p} {q} b {k} {k'} h) ls tr with >>=-step p k tr
... | inj₁ (v , tr1 , tr2) with ≲left b (>>=-lsafe-l ls) tr1
...   | ⟨ ρ v' ⟩ , q' , ⊑ρ leq , tr1' , b'
        with l' , kv' , leq' , tr2' , b'' ← ≲left (h leq) (>>=-lsafe-r ls tr1) tr2
        = l' , _ , leq' , >>=-step1 k' tr1' tr2' , b''
≲left (≲>>='-cong {{OA}} {{OB}} {p = p} {q} b {k} {k'} h) ls tr | inj₂ (l₁ , rf , p' , tr' , refl)
  with ≲left b (>>=-lsafe-l ls) tr'
... | l₁' , q' , leq , tr'' , b'' with ⊑-retFree rf leq
...   | refl = _ , _ , ⊑-refl {{LabOrd {{OB}}}} , >>=-step2 q k' rf tr'' , ≲>>='-cong b'' h

≲right (≲>>='-cong {{OA}} {{OB}} {p = p} {q} b {k} {k'} h) ls tr with >>=-step q k' tr
... | inj₁ (v , tr1 , tr2) with ≲right b (>>=-lsafe-l ls) tr1
...   | ⟨ ρ v' ⟩ , p' , ⊑ρ leq , tr1' , b'
        with l' , kv' , leq' , tr2' , b'' ← ≲right (h leq) (>>=-lsafe-r ls tr1') tr2
        = l' , _ , leq' , >>=-step1 k tr1' tr2' , b''
≲right (≲>>='-cong {{OA}} {{OB}} {p = p} {q} b {k} {k'} h) ls tr | inj₂ (l₁ , rf , q' , tr' , refl)
  with ≲right b (>>=-lsafe-l ls) tr'
... | l₁' , p' , leq , tr'' , b'' with ⊑-retFree' rf leq
...   | refl = _ , _ , ⊑-refl {{LabOrd {{OB}}}} , >>=-step2 p k rf tr'' , ≲>>='-cong b'' h

≲>>=-cong : ∀ {E L A B i} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree E A ∞}
  → (p ↑ ≲̂ L ! q ↑) {i} → {k k' : A → CTree E B ∞}
  → (∀ {a b} → a ⊑ b → (k a ↑ ≲̂ L ! k' b ↑) {∞})
  → ((p >>= k) ↑ ≲̂ L ! (q >>= k') ↑) {i}
≲>>=-cong b h = ≲>>='-cong b h

~>>=-cong : ∀ {E L A B i} {p q : CTree E A ∞}
  → (p ↑ ~̂ L ! q ↑) {i} → {k k' : A → CTree E B ∞}
  → (∀ a → (k a ↑ ~̂ L ! k' a ↑) {∞})
  → ((p >>= k) ↑ ~̂ L ! (q >>= k') ↑) {i}
~>>=-cong b h = ≲>>=-cong {{≡-Ord}} {{≡-Ord}} b λ { {a} refl → h a }

-- Congruence for `map`, as an instance of the congruence for >>=
-- (recall map f p = p >>= (return ∘ f)).

≲⊑ : ∀ {E L A i} {{_ : Ord A}} {v w : A} → v ⊑ w → (return {E = E} v ↑ ≲̂ L ! return w ↑) {i}
≲left  (≲⊑ leq) _ (⇒-now _) = _ , _ , ⊑ρ leq , ⇒-now _ , ≲refl
≲right (≲⊑ leq) _ (⇒-now _) = _ , _ , ⊑ρ leq , ⇒-now _ , ≲refl

≲map-cong : ∀ {E L A B i} {{_ : Ord A}} {{_ : Ord B}} {p q : CTree' E A} {f : A → B}
  → (∀ {a b} → a ⊑ b → f a ⊑ f b)
  → (p ≲̂ L ! q) {i} → (map' f p ≲̂ L ! map' f q) {i}
≲map-cong le b = ≲>>='-cong b (λ leq → ≲⊑ (le leq))

~map-cong : ∀ {E L A B i} {p q : CTree' E A} {f : A → B}
  → (p ~̂ L ! q) {i} → (map' f p ~̂ L ! map' f q) {i}
~map-cong = ≲map-cong {{≡-Ord}} {{≡-Ord}} λ {refl → refl}

---------------------------------------------------------------------
-- Functor laws
---------------------------------------------------------------------

≲map-id : ∀ {E L A i} {{_ : Ord A}} (p : CTree E A ∞) → (map id p ↑ ≲̂ L ! p ↑) {i}
≲map-id _ = ≲>>=-return

~map-id : ∀ {E L A i} (p : CTree E A ∞) → (map id p ↑ ~̂ L ! p ↑) {i}
~map-id = ≲map-id {{≡-Ord}}

≲map-∘ : ∀ {E L A B C i} {{_ : Ord C}} (p : CTree E A ∞) {f : A → B} {g : B → C}
  → (map g (map f p) ↑ ≲̂ L ! map (g ∘ f) p ↑) {i}
≲map-∘ p = ≲>>=-assoc p

~map-∘ : ∀ {E L A B C i} (p : CTree E A ∞) {f : A → B} {g : B → C}
  → (map g (map f p) ↑ ~̂ L ! map (g ∘ f) p ↑) {i}
~map-∘ = ≲map-∘ {{≡-Ord}}
